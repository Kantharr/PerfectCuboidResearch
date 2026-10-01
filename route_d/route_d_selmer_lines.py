"""Line-level test from the 2-Selmer group alone (no generators, no proven rank needed).

A fibre of the line a:b with kernel (al, be, ga) is the 2-covering of E = E_{a,b} of class
(sigma, -sigma al ga) for the Kummer map P -> (X, X - a^2 sigma) mod squares. A fibre with a
rational point has its class in the image of E(Q)/2E(Q), hence in the 2-Selmer group. So if
Sel2(E) contains no clean class (first coordinate sigma, al*ga > 0, be*ga > 0, not one of the two
degenerate classes), no clean fibre of the line has a rational point, whatever the rank.

Sel2 is computed exactly as in route_d_selmer2.py (complete 2-descent over the full rational
2-torsion), but its elements are returned rather than only its dimension.

Usage:  python route_d_selmer_lines.py 49:5 11:3 ...      (prints dim Sel2 and the fibre classes)
        python route_d_selmer_lines.py --lines L.json     (writes selmer_<L>.json)
Checked on the 54 survey lines: the clean classes are exactly the survey's locally solvable clean
kernels; and on 96 lines dim Sel2 = (ellrank upper bound) + 2 + s.
"""
import sys
from math import gcd

import sympy as sp

from route_d_selmer2 import local_image, annihilator, sqclass_local

def core(n):
    n = int(n); s = -1 if n < 0 else 1; n = abs(n); c = 1
    for p, e in sp.factorint(n).items():
        if e % 2: c *= p
    return s * c

def nullspace_f2(rows, n):
    """basis (bitmasks) of {c : popcount(r & c) even for all rows}"""
    piv = {}
    for r in rows:
        for b in range(n - 1, -1, -1):
            if not (r >> b) & 1: continue
            if b in piv: r ^= piv[b]
            else: piv[b] = r; break
    # reduce to RREF
    for b in sorted(piv):
        for b2 in piv:
            if b2 != b and (piv[b2] >> b) & 1: piv[b2] ^= piv[b]
    free = [b for b in range(n) if b not in piv]
    basis = []
    for f in free:
        v = 1 << f
        for b, r in piv.items():
            if (r >> f) & 1: v |= 1 << b
        basis.append(v)
    return basis

def selmer_elements(a, b):
    s = a * a + b * b; es = (0, a * a * s, b * b * s)
    disc = 16 * (es[1] * es[2] * (es[1] - es[2])) ** 2
    S = sorted(sp.factorint(disc).keys())
    g = [-1] + S
    basis = [(x, 1) for x in g] + [(1, x) for x in g]
    n = len(basis); rows = []
    for p in [0] + S:
        img = local_image(es, p); ld = len(img[0]); ann = annihilator(img, ld)
        cols = [sqclass_local(u, p) + sqclass_local(w, p) for (u, w) in basis]
        for wmask in ann:
            w = list(map(int, format(wmask, f"0{ld}b"))); r = 0
            for j, c in enumerate(cols):
                if sum(wi * ci for wi, ci in zip(w, c)) % 2: r |= 1 << j
            rows.append(r)
    B = nullspace_f2(rows, n)
    elts = set()
    for m in range(1 << len(B)):
        v = 0
        for i, bv in enumerate(B):
            if (m >> i) & 1: v ^= bv
        d1 = d2 = 1
        for j in range(n):
            if (v >> j) & 1: d1 *= basis[j][0]; d2 *= basis[j][1]
        elts.add((core(d1), core(d2)))
    return len(B), sorted(elts)

def fibre_classes(a, b):
    """clean / degenerate kernels whose class lies in Sel2 (first coordinate sigma, al*ga, be*ga > 0)"""
    s = a * a + b * b; dim, E = selmer_elements(a, b); out = []
    dy, dc = core(a * a - b * b), core(a ** 4 - b ** 4)
    for d1, d2 in E:
        if d1 != core(s): continue
        ag, bg = core(-s * d2), core(-s * d1 * d2)
        if ag < 0 or bg < 0: continue
        ga = gcd(ag, bg); kind = "y=z" if ag == dy else "case1" if ag == dc else "clean"
        out.append((ag // ga, bg // ga, ga, kind))
    return dim, out

if __name__ == "__main__":
    if sys.argv[1] == "--lines":
        import json, os
        lines = json.load(open(sys.argv[2]))
        out = {}
        for a, b in lines:
            dim, fc = fibre_classes(a, b)
            out[f"{a}:{b}"] = dict(dimSel2=dim, clean=[list(f[:3]) for f in fc if f[3] == "clean"],
                                   degenerate=[list(f[:3]) for f in fc if f[3] != "clean"])
            print(f"{a}:{b}  dim Sel2 = {dim}  clean classes: {out[f'{a}:{b}']['clean']}", flush=True)
        tag = os.path.splitext(os.path.basename(sys.argv[2]))[0]
        json.dump(out, open(f"selmer_{tag}.json", "w"), indent=0)
    else:
        for a, b in [(int(x.split(":")[0]), int(x.split(":")[1])) for x in sys.argv[1:]]:
            dim, fc = fibre_classes(a, b)
            print(f"{a}:{b}  dim Sel2 = {dim}  fibre classes in Sel2: {fc}")
