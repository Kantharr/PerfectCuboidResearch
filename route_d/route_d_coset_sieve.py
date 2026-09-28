"""Full Mordell-Weil sieve at a fixed level N using EVERY prime (not only those whose
group exponent divides N): a class delta mod N E(Q) survives prime l iff the coset
red_l(delta) + N * red_l(E(Q)) meets the allowed set A_l.  Equivalently: the pulled-back
N-cover C_delta has l-adic points compatible with E(Q).  If no class survives, C(Q) is
empty by a finite descent obstruction at level N.

Usage: python route_d_coset_sieve.py datafile rank N1,N2,...
"""
import sys, ast
from itertools import product


def load(path):
    out = []
    for line in open(path):
        l, c1, c2, rest = line.strip().split(" ", 3)
        co, bits = rest.rsplit(" ", 1)
        out.append((int(l), int(c1), int(c2), ast.literal_eval(co), bits))
    return out


def subgroup(gens, c1, c2):
    S = {(0, 0)}
    fr = [(0, 0)]
    while fr:
        x = fr.pop()
        for g in gens:
            y = ((x[0] + g[0]) % c1, (x[1] + g[1]) % c2)
            if y not in S:
                S.add(y)
                fr.append(y)
    return S


def sieve(data, r, N, verbose=False):
    classes = [g + t for g in product(range(N), repeat=r) for t in product(range(2), repeat=2)]
    killers = {}
    for (l, c1, c2, co, bits) in data:
        H = subgroup(co, c1, c2)
        NH = {((N * h[0]) % c1, (N * h[1]) % c2) for h in H}
        if len(NH) == len(H):
            continue                     # N acts invertibly on the image: no information at this prime
        keep = []
        for c in classes:
            base = (sum(ci * v[0] for ci, v in zip(c, co)) % c1, sum(ci * v[1] for ci, v in zip(c, co)) % c2)
            ok = any(bits[((base[1] + h[1]) % c2) * c1 + (base[0] + h[0]) % c1] == "1" for h in NH)
            if ok:
                keep.append(c)
            else:
                killers[c] = l
        classes = keep
        if not classes:
            break
    return classes, killers


if __name__ == "__main__":
    data = load(sys.argv[1])
    r = int(sys.argv[2])
    for N in map(int, sys.argv[3].split(",")):
        cls, kil = sieve(data, r, N)
        used = sorted(set(kil.values()))
        print(f"N={N:3d}: {4 * N**r:6d} classes, survivors {len(cls):5d}; killing primes {used[:12]}{'...' if len(used) > 12 else ''}")
