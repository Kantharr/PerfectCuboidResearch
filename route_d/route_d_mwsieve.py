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
import sys, ast
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


def run(path, r, nt, chain, cap=None, stats=None):
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
            if cap is not None and len(classes) * len(lifts) > cap:
                history.append((Nn, len(classes) * len(lifts), 0, -1))
                print(f"stage N={Nn}: would lift to {len(classes) * len(lifts)} classes > cap {cap}; stopping", flush=True)
                return classes, history
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
