"""Enumerate every kernel (alpha,beta,gamma) on a ratio line a:b, test solvability,
search for rational points on each fiber, and classify fibers as
Case-1 (contains (a^2,ab,b^2)), y=z (contains (a,b,b)), or clean."""
import sys, subprocess, os
from math import gcd, isqrt
from itertools import combinations
import sympy as sp

GP = os.environ.get("PARI_GP_PATH", "gp")

def sqf(n):
    r = 1
    for p, e in sp.factorint(n).items():
        if e % 2: r *= p
    return r

def kernels(a, b):
    s1 = sqf(a*a + b*b)
    D = a*a - b*b
    ps = [p for p in sp.factorint(s1)]
    gps = [p for p in sp.factorint(D) if s1 % p]
    out = []
    for r in range(len(ps) + 1):
        for A in combinations(ps, r):
            al = 1
            for p in A: al *= p
            be = s1 // al
            for r2 in range(len(gps) + 1):
                for Gs in combinations(gps, r2):
                    ga = 1
                    for p in Gs: ga *= p
                    out.append((al, be, ga))
    return out

def conic_solvable(ks, D):
    lines = ["default(parisize,100000000);"]
    for al, be, ga in ks:
        lines.append(f"print(type(qfsolve(matdiagonal([{ga*al},{-ga*be},{-D}])))==\"t_COL\");")
    lines.append("quit;")
    out = subprocess.run([GP, "-q"], input="\n".join(lines), capture_output=True, text=True).stdout.split()
    return [o == "1" for o in out]

def issq(n):
    return n >= 0 and isqrt(n) ** 2 == n

def points(a, b, al, be, ga, T):
    pts = []
    for t in range(1, T + 1):
        for z in range(0, b * t + 1):
            n2, n3 = a*a*t*t - z*z, b*b*t*t - z*z
            if n2 % (al*ga) or n3 % (be*ga): continue
            if issq(n2 // (al*ga)) and issq(n3 // (be*ga)) and gcd(gcd(t, z), 1) == 1:
                pts.append((t, z))
    return pts

def classify(a, b, T=60):
    D = a*a - b*b
    ks = kernels(a, b)
    solv = conic_solvable(ks, D)
    res = []
    for k, ok in zip(ks, solv):
        if not ok:
            continue
        al, be, ga = k
        pts = points(a, b, al, be, ga, T)
        c1 = (a, b*b) in pts or any(t == a and z == b*b for t, z in pts)
        # Case-1 kernel test directly from (a^2,ab,b^2):
        x, y, z = a*a, a*b, b*b
        k_c1 = (sqf(x*x + y*y), sqf(x*x - z*z), sqf(y*y - z*z)) == (al*be, al*ga, be*ga)
        yz = issq(D // (al*ga)) if D % (al*ga) == 0 else False
        kind = "Case-1" if k_c1 else ("y=z" if yz else "CLEAN")
        res.append((k, kind, pts[:6], len(pts)))
    return res

if __name__ == "__main__":
    for arg in sys.argv[1:]:
        a, b = map(int, arg.split(":"))
        print(f"== {a}:{b}")
        for k, kind, pts, n in classify(a, b):
            print(f"   kernel {k}: {kind:6s}  rational points found (t<=60): {n}  e.g. {pts}")
