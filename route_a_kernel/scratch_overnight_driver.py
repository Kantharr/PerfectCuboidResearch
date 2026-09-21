import csv, subprocess, sys, time
from collections import Counter, defaultdict
from math import gcd
from gaussian_predict import candidate_ratios

rows = list(csv.DictReader(open('kernel_table_20000.csv')))
for r in rows:
    for k in r: r[k] = int(r[k])

def reduce_ratio(a, b):
    g = gcd(a, b)
    return (a // g, b // g)

# known ratios per product (across all (alpha,beta) pairs sharing that product)
known_by_product = defaultdict(set)
for r in rows:
    p = r['alpha'] * r['beta']
    known_by_product[p].add(reduce_ratio(r['x'], r['y']))

def run_search(a, b, tmax=3000, timeout_s=60):
    t0 = time.time()
    try:
        out = subprocess.run(['./kernel_line_search2.exe', 'xy', str(a), str(b), str(tmax)],
                              capture_output=True, text=True, timeout=timeout_s)
    except subprocess.TimeoutExpired:
        return None, time.time() - t0  # signal: too expensive at this tmax
    dt = time.time() - t0
    lines = out.stdout.strip().splitlines()
    hits = []
    for line in lines:
        if line.startswith('  HIT:'):
            hits.append(line.strip())
    return hits, dt

def test_product(product, u1_bound=100, max_ab_size=3000, tmax=3000, max_candidates=6, timeout_budget=30):
    known = known_by_product.get(product, set())
    try:
        cands = candidate_ratios(product, 1, u1_bound=u1_bound)
    except Exception as e:
        print(f"  [product={product}] candidate generation FAILED: {e}")
        return []
    new_cands = []
    for u1 in sorted(cands.keys()):
        if u1 == 1:
            continue
        for (a, b) in sorted(cands[u1], key=lambda ab: ab[0]):
            if (a, b) in known:
                continue
            if a > max_ab_size:
                continue
            new_cands.append((u1, a, b))
    # dedupe by (a,b), keep smallest u1 explanation, sort by a (smallest first = cheapest)
    seen_ab = {}
    for u1, a, b in new_cands:
        if (a, b) not in seen_ab:
            seen_ab[(a, b)] = u1
    ordered = sorted(seen_ab.items(), key=lambda kv: kv[0][0])[:max_candidates]

    results = []
    for (a, b), u1 in ordered:
        # calibrate: try a small tmax first if the ratio's magnitude looks expensive
        probe_tmax = min(tmax, 300) if b > 400 else tmax
        hits, dt = run_search(a, b, probe_tmax)
        if hits is None:
            results.append((product, u1, a, b, round(a / b, 3), None, [], round(dt, 2), probe_tmax))
            continue
        if probe_tmax < tmax:
            # small probe finished fast enough; extrapolate cost before going to full tmax
            est_full = dt * (tmax / probe_tmax) ** 2
            if est_full > timeout_budget:
                results.append((product, u1, a, b, round(a / b, 3), len(hits), hits, round(dt, 2), probe_tmax))
                continue
            hits, dt = run_search(a, b, tmax)
            if hits is None:
                results.append((product, u1, a, b, round(a / b, 3), None, [], round(dt, 2), tmax))
                continue
        results.append((product, u1, a, b, round(a / b, 3), len(hits), hits, round(dt, 2), tmax))
    return results

if __name__ == '__main__':
    import csv as csvmod
    products = [int(x) for x in sys.argv[1:]]
    logpath = 'scratch_overnight_log.csv'
    file_exists = False
    try:
        with open(logpath) as f:
            file_exists = True
    except FileNotFoundError:
        pass
    with open(logpath, 'a', newline='') as logf:
        w = csvmod.writer(logf)
        if not file_exists:
            w.writerow(['product', 'u1', 'a', 'b', 'ratio', 'hits', 'skipped', 'time_s', 'tmax', 'hit_details'])
        for p in products:
            print(f"=== product={p} (known triples with this product: {len(known_by_product.get(p, []))}) ===")
            results = test_product(p)
            for (product, u1, a, b, ratio, nhits, hits, dt, used_tmax) in results:
                if nhits is None:
                    print(f"  u1={u1:5d}  ratio={a}:{b}  (a/b={ratio})  SKIPPED (too expensive, >{dt}s at tmax={used_tmax})")
                    w.writerow([product, u1, a, b, ratio, '', 1, dt, used_tmax, ''])
                    continue
                print(f"  u1={u1:5d}  ratio={a}:{b}  (a/b={ratio})  hits={nhits}  time={dt}s  tmax={used_tmax}")
                for h in hits:
                    print(f"      {h}")
                w.writerow([product, u1, a, b, ratio, nhits, 0, dt, used_tmax, ' | '.join(hits)])
            print()
