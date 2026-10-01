"""Staged Mordell-Weil sieve for the Route D cuboid cover W^2 = F on a rank-r fiber.

Input: per-prime data lines "l c1 c2 [[a,b],...] bits" from the PARI generator
(route_d_fiber_model.py + psiF export), where the coordinate list gives the
discrete logs of the saturated generators G1..Gr and the torsion generators
in E(F_l) = Z/c1 x Z/c2, and bits[b*c1 + a] = 1 iff the point a*g1 + b*g2 is
"allowed" (F a nonzero square mod l, or undecidable -> conservatively allowed).

A class (n_1..n_r, tau) mod N survives a prime l (c1 | N) iff its reduction
lies in the allowed set. Soundness: generators are saturated at every prime
dividing N, so every rational point lies in exactly one class.
"""
import os, sys, ast
from itertools import product


def load(path, r, nt):
    data = []
    for line in open(path):
        line = line.strip()
        if not line:
            continue
        l, c1, c2, rest = line.split(" ", 3)
        co_str, bits = rest.rsplit(" ", 1)
        co = ast.literal_eval(co_str)
        assert len(co) == r + nt
        data.append((int(l), int(c1), int(c2), co, bits))
    return data


def _stage_c(binp, classes, sel, r, nt, N, k):
    """One streamed stage in C (route_d_sieve_stage.c); same survivors and counts as the Python loop."""
    import tempfile, subprocess
    from array import array
    m = r + nt
    with tempfile.TemporaryDirectory() as td:
        pf, ci, co, cf = (os.path.join(td, x) for x in ("primes.txt", "in.bin", "out.bin", "counts.txt"))
        with open(pf, "w") as fh:
            for (l, c1, c2, ca, cb, bits) in sel:
                fh.write(f"{l} {c1} {c2} {' '.join(map(str, ca))} {' '.join(map(str, cb))} {bits}\n")
        flat = array("i")
        for c in classes:
            flat.extend(c)
        with open(ci, "wb") as fh:
            flat.tofile(fh)
        subprocess.run([binp, pf, ci, co, cf, str(r), str(nt), str(N), str(k)], check=True)
        res = array("i")
        with open(co, "rb") as fh:
            res.frombytes(fh.read())
        out = [tuple(res[i:i + m]) for i in range(0, len(res), m)]
        lines = open(cf).read().split("\n")
        nb = [int(x.split()[1]) for x in lines[:len(sel)]]
        na = [int(x.split()[2]) for x in lines[:len(sel)]]
    return out, nb, na


def _passes(c, P):
    l, c1, c2, ca, cb, bits = P
    return bits[(sum(ci * bi for ci, bi in zip(c, cb)) % c2) * c1 + sum(ci * ai for ci, ai in zip(c, ca)) % c1] == "1"


def run(path, r, nt, chain, cap=None, stats=None, stream_cap=None):
    """cap: largest class list that is materialised.  If lifting would exceed it and stream_cap is
    set (and at least the number of lifted classes), the lift is streamed instead: each lifted class
    is tested against this stage's primes as it is generated and only survivors are kept (the run
    stops if the survivors alone exceed cap).  Same result as the materialised lift; the per-prime
    stats are the same too, since the primes are applied in the same order."""
    data = load(path, r, nt)
    used = set()
    tors = list(product(range(2), repeat=nt))
    N = chain[0]
    classes = [g + t for g in product(range(N), repeat=r) for t in tors]
    history = []
    for stage, Nn in enumerate(chain):
        if stage > 0:
            assert Nn % N == 0
            k = Nn // N
            lifts = list(product(range(k), repeat=r))
            total = len(classes) * len(lifts)
            if cap is not None and total > cap:
                if stream_cap is None or total > stream_cap:
                    history.append((Nn, total, 0, -1))
                    print(f"stage N={Nn}: would lift to {total} classes > cap {cap}; stopping", flush=True)
                    return classes, history
                # streamed lift + filter
                sel = []
                for (l, c1, c2, co, bits) in data:
                    if l in used or Nn % c1:
                        continue
                    used.add(l)
                    sel.append((l, c1, c2, [x[0] for x in co], [x[1] for x in co], bits))
                binp = os.environ.get("ROUTE_D_SIEVE_BIN")
                if binp:
                    out, nb, na = _stage_c(binp, classes, sel, r, nt, N, k)
                    if len(out) > cap:
                        history.append((Nn, total, len(sel), -1))
                        print(f"stage N={Nn}: streamed survivors exceed cap {cap}; stopping", flush=True)
                        return out, history
                else:
                    nb, na, out = [0] * len(sel), [0] * len(sel), []
                for c in ([] if binp else classes):
                    for L in lifts:
                        cc = tuple(c[i] + L[i] * N for i in range(r)) + c[r:]
                        ok = True
                        for j, P in enumerate(sel):
                            nb[j] += 1
                            if not _passes(cc, P):
                                ok = False
                                break
                            na[j] += 1
                        if ok:
                            out.append(cc)
                            if len(out) > cap:
                                history.append((Nn, total, len(sel), -1))
                                print(f"stage N={Nn}: streamed survivors exceed cap {cap}; stopping", flush=True)
                                return out, history
                N = Nn
                # primes no class reached (after the set became empty) count as unused, as in the
                # materialised path, which stops at the first prime that empties the set
                reached = [j for j in range(len(sel)) if nb[j] > 0]
                if stats is not None:
                    for j in reached:
                        P = sel[j]
                        stats.append((N, P[0], P[1], P[2], P[5].count("1") / len(P[5]), nb[j], na[j]))
                classes = out
                history.append((N, total, len(reached), len(classes)))
                print(f"stage N={N}: {total} classes streamed, {len(reached)} new primes applied, {len(classes)} survive", flush=True)
                if not classes:
                    break
                continue
            classes = [tuple(c[i] + L[i] * N for i in range(r)) + c[r:] for c in classes for L in lifts]
            N = Nn
        before = len(classes)
        nused = 0
        for (l, c1, c2, co, bits) in data:
            if l in used or N % c1:
                continue
            used.add(l)
            nused += 1
            ca = [x[0] for x in co]; cb = [x[1] for x in co]
            nbefore = len(classes)
            classes = [c for c in classes
                       if bits[(sum(ci * bi for ci, bi in zip(c, cb)) % c2) * c1 + sum(ci * ai for ci, ai in zip(c, ca)) % c1] == "1"]
            if stats is not None:
                stats.append((N, l, c1, c2, bits.count("1") / len(bits), nbefore, len(classes)))
            if not classes:
                break
        history.append((N, before, nused, len(classes)))
        print(f"stage N={N}: {before} classes after lifting, {nused} new primes applied, {len(classes)} survive", flush=True)
        if not classes:
            break
    return classes, history


if __name__ == "__main__":
    path = sys.argv[1]
    r, nt = int(sys.argv[2]), int(sys.argv[3])
    chain = [int(x) for x in sys.argv[4].split(",")]
    cls, hist = run(path, r, nt, chain)
    if len(cls):
        print("surviving classes (first 20):")
        print(cls[:20])
