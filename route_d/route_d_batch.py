"""Batch cuboid-exclusion over clean Route D fibers.

For each fiber (a, b, alpha, beta, gamma[, [t, z, u2, u3]]):
  1. base point: the one given, else conic parametrization + hyperellratpoints (route_d_basepoint.gp)
  2. route_d_sieve_setup.py  (explicit model, proven rank, saturated generators)
  3. per-prime data (PARI, every discrete log / basis / bijection verified)
  4. staged Mordell-Weil sieve, recording death N, killing primes, allowed fractions
  5. verification: full exact certificate if the class count at death is small,
     otherwise ground-truth validation of the data against exact F at real points
Results are appended as JSON lines to batch_results.jsonl as they come in.
"""
import sys, os, json, time, subprocess, re, io, contextlib, traceback
sys.set_int_max_str_digits(0)   # exact coordinates can exceed 4300 digits
import sympy as sp

GP = os.environ.get("PARI_GP_PATH", "gp")
# helper scripts live next to this file; generated files go to the current directory
HERE = os.path.dirname(os.path.abspath(__file__))
CHAIN = [8, 24, 48, 240, 1680, 5040]
# full exact certificate when the class count at death is at most this; above it, the
# ground-truth cross-check (override with ROUTE_D_CERT_MAX, e.g. for large batches)
CERT_MAX_CLASSES = int(os.environ.get("ROUTE_D_CERT_MAX", "20000"))
CLASS_CAP = 30_000_000


def gp_run(src, timeout):
    return subprocess.run([GP, "-q"], input=src, capture_output=True, text=True, timeout=timeout)


def basepoint(a, b, al, be, ga):
    for H in (10**4, 10**6):
        out = gp_run(f'read("{HERE.replace(chr(92), "/")}/route_d_basepoint.gp"); P = fiberpoints({a},{b},{al},{be},{ga},{H}); if(#P, print(P[1]), print("NONE"));\nquit;\n', 300).stdout.strip().splitlines()
        if out and out[-1] != "NONE":
            return [abs(int(x)) for x in out[-1].strip("[]").split(",")], H
    return None, None


def one(a, b, al, be, ga, log, known_bp=None):
    tag = f"{a}_{b}_{al}_{be}_{ga}"
    rec = dict(a=a, b=b, kernel=[al, be, ga], tag=tag)
    t0 = time.time()
    # a known base point (e.g. from route_d_fiber_descent.gp) skips the height search
    bp, H = (known_bp, None) if known_bp else basepoint(a, b, al, be, ga)
    if bp is None:
        src = ("default(parisize,500000000);\n"
               f"E=ellinit([0,-({a*a+b*b})^2,0,{a*a*b*b}*({a*a+b*b})^2,0]); r=ellrank(E); "
               'print(r[1]," ",r[2]," ",r[3]);\nquit;\n')
        er = gp_run(src, 600).stdout.split()
        rec.update(status="SKIP: no base point up to height 1e6", line_rank=er[-3:] if len(er) >= 3 else None); return rec
    rec["base"] = bp
    try:
        so = subprocess.run([sys.executable, os.path.join(HERE, "route_d_sieve_setup.py"), str(a), str(b), str(al), str(be), str(ga),
                             *map(str, bp), "5040", "300000", tag], capture_output=True, text=True, timeout=900)
    except subprocess.TimeoutExpired:
        rec.update(status="SKIP: setup timeout (rank/saturation)"); return rec
    if not os.path.exists(f"fiber_{tag}.json") or "rank not proven" in so.stderr + so.stdout or so.returncode:
        rec.update(status="SKIP: setup failed", err=(so.stderr or so.stdout)[-300:]); return rec
    info = json.load(open(f"fiber_{tag}.json"))
    r = info["rank"]; rec["rank"] = r
    if os.path.exists(f"sieve_data_{tag}.txt"):
        os.remove(f"sieve_data_{tag}.txt")           # PARI write() appends
    try:
        dg = subprocess.run([GP, "-q", f"route_d_mwsieve_data_{tag}.gp"], stdin=subprocess.DEVNULL,
                            capture_output=True, text=True, timeout=1800)
    except subprocess.TimeoutExpired:
        rec.update(status="SKIP: data generation timeout"); return rec
    m = re.search(r"wrote data for (\d+) primes", dg.stdout)
    if not m:
        rec.update(status="SKIP: data generation error", err=(dg.stdout + dg.stderr)[-400:]); return rec
    rec["nprimes"] = int(m.group(1))
    from route_d_mwsieve import run
    stats = []
    with contextlib.redirect_stdout(io.StringIO()):
        cls, hist = run(f"sieve_data_{tag}.txt", r, 2, CHAIN, cap=CLASS_CAP, stats=stats)
    rec["history"] = hist
    dead = len(cls) == 0 and hist and hist[-1][3] == 0
    if not dead:
        rec.update(status="SURVIVES", survivors=len(cls), N=hist[-1][0] if hist else None,
                   sample_survivors=[list(c) for c in cls[:8]])
        return rec
    Nd = hist[-1][0]
    rec["death_N"] = Nd
    # which primes actually removed classes, and the independence ("random") model
    kills = {}
    for (N, l, c1, c2, frac, nb, na) in stats:
        if na < nb:
            kills[l] = kills.get(l, 0) + (nb - na)
    rec["killing_primes"] = kills
    exp = 1.0
    N0 = None
    for (N, l, c1, c2, frac, nb, na) in stats:
        exp *= frac
    rec["random_model_surviving_fraction"] = exp
    rec["classes_at_death_N"] = 4 * Nd**r
    rec["expected_survivors_random_model"] = 4 * Nd**r * exp
    # verification
    if 4 * Nd**r <= CERT_MAX_CLASSES:
        try:
            co = subprocess.run([sys.executable, os.path.join(HERE, "route_d_certificate.py"), str(a), str(b), str(al), str(be), str(ga),
                                 *map(str, bp), tag, str(Nd)], capture_output=True, text=True, timeout=5400)
            rec["verification"] = "certificate: " + ("VALID" if "CERTIFICATE: VALID" in co.stdout else "NOT ESTABLISHED")
            rec["cert_tail"] = co.stdout.strip().splitlines()[-4:]
        except subprocess.TimeoutExpired:
            rec["verification"] = "certificate: timeout"
    else:
        from route_d_validate import validate
        try:
            res, Fv = validate(tag, B=3 if r <= 2 else 2)
            rec["verification"] = ("ground truth: " + ("OK" if res["unsound"] == 0 and res["inconsistent"] == 0 and res["squares"] == 0 else "PROBLEM"))
            rec["ground_truth"] = res
        except Exception as e:
            rec["verification"] = f"ground truth: error {type(e).__name__}"
    rec["status"] = "EXCLUDED" if rec["verification"].endswith(("VALID", "OK")) else "UNVERIFIED"
    rec["seconds"] = round(time.time() - t0, 1)
    return rec


if __name__ == "__main__":
    fibers = json.load(open(sys.argv[1]))
    done = set()
    if os.path.exists("batch_results.jsonl"):
        done = {json.loads(l)["tag"] for l in open("batch_results.jsonl")}
    for f in fibers:
        tag = "_".join(map(str, f[:5]))
        if tag in done:
            continue
        t0 = time.time()
        try:
            rec = one(*f[:5], None, f[5] if len(f) > 5 else None)
        except Exception as e:
            rec = dict(a=f[0], b=f[1], kernel=f[2:5], tag=tag, status=f"ERROR {type(e).__name__}: {e}", tb=traceback.format_exc()[-600:])
        rec["seconds"] = round(time.time() - t0, 1)
        with open("batch_results.jsonl", "a") as fh:
            fh.write(json.dumps(rec) + "\n")
        print(f"{tag}: {rec['status']}  rank={rec.get('rank')}  death_N={rec.get('death_N')}  "
              f"kills={rec.get('killing_primes')}  {rec.get('verification', '')}  ({rec['seconds']}s)", flush=True)
