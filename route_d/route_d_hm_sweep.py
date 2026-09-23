import sys, itertools
from math import gcd
sys.path.insert(0, '.')
from route_d_hasse_minkowski import (squarefree_part, factorize, valid_alpha_beta_splits,
                                       qfsolve_point, derive_quartic_from_conic_point,
                                       ellrootno_for_quartic)

# Fresh (a,b) ratios: both odd, coprime, small, none previously tested by brute force
ab_list = []
for a in range(3, 40):
    for b in range(1, a):
        if gcd(a, b) != 1 or a % 2 == 0 or b % 2 == 0:
            continue
        prod = squarefree_part(a*a + b*b)
        if prod == 1:
            continue
        ab_list.append((a, b, prod))

known_ab = {(39,37),(13,9),(93,71),(223,211),(287,109),(257,93),(311,273),
            (139,97),(67,55),(125,79),(193,179),(157,101),(73,39),(127,67),
            (151,143),(47,21),(347,215),(47,23),(39,23),(71,69)}
ab_list = [c for c in ab_list if (c[0], c[1]) not in known_ab]

# small odd squarefree gamma candidates (coprime-to-alpha*beta checked per-fiber)
gamma_candidates = [1, 3, 5, 7, 11, 13, 15, 17, 19, 21, 23, 29, 31, 33, 35, 37]

results = []
tested = 0
target_count = 150

for a, b, prod in ab_list:
    if tested >= target_count:
        break
    for (alpha, beta) in valid_alpha_beta_splits(prod):
        if tested >= target_count:
            break
        for gamma in gamma_candidates:
            if tested >= target_count:
                break
            if gamma != 1 and (gamma % alpha == 0 or gamma % beta == 0):
                pass
            if gcd(gamma, alpha * beta) != 1:
                continue
            label = f"({alpha},{beta},{gamma};{a},{b})"
            pt = qfsolve_point(alpha, beta, gamma, a, b)
            if pt is None:
                print(f"{label}: ANISOTROPIC (no rational point on conic -- locally obstructed)")
                tested += 1
                continue
            coeffs = derive_quartic_from_conic_point(alpha, beta, gamma, a, b, *pt)
            if coeffs is None:
                print(f"{label}: point={pt} -- degenerate seed, skipped")
                tested += 1
                continue
            out = ellrootno_for_quartic(coeffs)
            cond = None
            rootno = None
            for line in out.splitlines():
                if line.startswith("COND:"):
                    cond = line.split(":",1)[1].strip()
                if line.startswith("ROOTNO:"):
                    rootno = line.split(":",1)[1].strip()
            print(f"{label}: point={pt}  cond={cond}  rootno={rootno}")
            results.append((label, alpha, beta, gamma, a, b, pt, cond, rootno))
            tested += 1

print(f"\n\n{'='*70}")
print(f"Total fibers tested: {tested}")
pos = sum(1 for r in results if r[8] == '1')
neg = sum(1 for r in results if r[8] == '-1')
aniso = tested - len(results)
print(f"Anisotropic (no rational point, locally obstructed): {aniso}")
print(f"Isotropic and rootno computed: {len(results)}  (+1: {pos}, -1: {neg})")

import pickle
with open('route_d_hm_sweep_results.pkl', 'wb') as f:
    pickle.dump(results, f)
