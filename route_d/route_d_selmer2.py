"""Independent 2-Selmer computation for E(a,b): y^2 = x(x-e2)(x-e3),
e2 = a^2(a^2+b^2), e3 = b^2(a^2+b^2), via complete 2-descent over the full
rational 2-torsion.  Kummer map: P=(x,y) -> (x-e1, x-e2) in (Q*/Q*^2)^2.

Sel_2 = { c in candidate group : res_p(c) in delta_p(E(Q_p)) for all p in S u {inf} }.
Local images are found by sampling Q_p-points until the span reaches its known
dimension (2 at odd p, 3 at p=2, 1 at infinity); failure to reach it raises.
"""
import sys
from fractions import Fraction
from math import gcd

import sympy as sp


def vp(n, p):
    n = abs(n)
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v, n


def sqclass_local(x, p):
    """Bit vector of x in Q_p*/Q_p*^2 (p prime) or R*/R*^2 (p == 0)."""
    x = Fraction(x)
    if p == 0:
        return [1 if x < 0 else 0]
    vn, un = vp(x.numerator, p)
    vd, ud = vp(x.denominator, p)
    sign = -1 if x < 0 else 1
    v = vn - vd
    if p == 2:
        u = (sign * un * pow(ud, -1, 8)) % 8
        return [v % 2, 1 if u % 4 == 3 else 0, 1 if u in (3, 5) else 0]
    u = (sign * un * pow(ud, -1, p)) % p
    return [v % 2, 0 if pow(u, (p - 1) // 2, p) == 1 else 1]


def is_local_square(x, p):
    x = Fraction(x)
    if x == 0:
        return False
    return not any(sqclass_local(x, p))


def f2_rank(masks):
    piv = []
    for r in masks:
        for b in piv:
            if r & (b & -b):
                r ^= b
        if r:
            low = r & -r
            piv = [b ^ r if b & low else b for b in piv]
            piv.append(r)
    return len(piv)


def span_rank(vecs):
    return f2_rank([int("".join(map(str, v)), 2) for v in vecs])


def local_image(es, p):
    e1, e2, e3 = es
    f = lambda x: x * (x - e2) * (x - e3)
    delta = lambda x: sqclass_local(x - e1, p) + sqclass_local(x - e2, p)
    imgs = [
        sqclass_local((e1 - e2) * (e1 - e3), p) + sqclass_local(e1 - e2, p),
        sqclass_local(e2 - e1, p) + sqclass_local((e2 - e1) * (e2 - e3), p),
        sqclass_local(e3 - e1, p) + sqclass_local(e3 - e2, p),
    ]
    target = 1 if p == 0 else (3 if p == 2 else 2)
    if span_rank(imgs) >= target:
        return imgs
    base = p if p else 2
    ks = range(-6, 10)
    for e in es:
        for k in ks:
            for t in list(range(1, 260)) + list(range(-259, 0)):
                x = Fraction(e) + Fraction(base) ** k * t
                if x in es:
                    continue
                if (p == 0 and f(x) > 0) or (p and is_local_square(f(x), p)):
                    imgs.append(delta(x))
                    if span_rank(imgs) >= target:
                        return imgs
    raise RuntimeError(f"local image at p={p} stuck below dim {target}")


def f2_kernel_dim(rows, n):
    """dim of {c in F2^n : row.c = 0 for all rows}."""
    return n - f2_rank(rows)


def annihilator(vecs, dim):
    """Basis of {w in F2^dim : w.v = 0 for all v in vecs}, as int bitmasks."""
    vs = [int("".join(map(str, v)), 2) for v in vecs]
    out = []
    for w in range(1, 1 << dim):
        if all(bin(w & v).count("1") % 2 == 0 for v in vs):
            if f2_rank(out + [w]) > len(out):
                out.append(w)
    return out


def selmer_dim(a, b, restrict_support=False):
    assert gcd(a, b) == 1 and a != b
    s = a * a + b * b
    e1, e2, e3 = 0, a * a * s, b * b * s
    es = (e1, e2, e3)
    disc = 16 * (e2 * e3 * (e2 - e3)) ** 2
    S = sorted(sp.factorint(disc).keys())
    odd = lambda n: {q for q in sp.factorint(abs(n)) if q != 2}
    if restrict_support:
        g1 = [-1, 2] + sorted(odd(a) | odd(b) | odd(s))
        g2 = [-1, 2] + sorted(odd(a) | odd(s) | odd(a - b) | odd(a + b))
    else:
        g1 = g2 = [-1] + S
    basis = [(g, 1) for g in g1] + [(1, g) for g in g2]
    n = len(basis)
    rows = []
    for p in [0] + S:
        img = local_image(es, p)
        ld = len(img[0])
        ann = annihilator(img, ld)
        cols = [sqclass_local(u, p) + sqclass_local(w, p) for (u, w) in basis]
        for wmask in ann:
            w = list(map(int, format(wmask, f"0{ld}b")))
            r = 0
            for j, c in enumerate(cols):
                if sum(wi * ci for wi, ci in zip(w, c)) % 2:
                    r |= 1 << j
            rows.append(r)
    return f2_kernel_dim(rows, n), n


def prime_class(p, a, b):
    s = a * a + b * b
    if a % p == 0:
        return "a"
    if b % p == 0:
        return "b"
    if s % p == 0:
        return "s_odd" if vp(s, p)[0] % 2 else "s_even"
    if (a - b) % p == 0:
        return "m"
    if (a + b) % p == 0:
        return "p"
    return "good"


def rule_image(a, b, p):
    """Closed-form local image at an odd prime p or at infinity (p == 0),
    as a list of basis vectors in sqclass_local bit order."""
    s = a * a + b * b
    if p == 0:
        return [[0, 1]]  # d1 > 0, d2 free
    unram = [[0, 1, 0, 0], [0, 0, 0, 1]]
    cls = prime_class(p, a, b)
    if cls == "good" or cls == "s_even":
        return unram
    if cls == "s_odd":
        return [sqclass_local(1, p) + sqclass_local(-s, p),
                sqclass_local(s, p) + sqclass_local(a * a - b * b, p)]
    if cls == "a":
        return [[1, 0, 1, 0], [0, 1, 0, 1]] if p % 4 == 1 else unram
    if cls == "b":
        return [[1, 0, 0, 0], [0, 1, 0, 0]] if p % 4 == 1 else unram
    t = vp(a - b if cls == "m" else a + b, p)[0]
    if p % 8 in (1, 7):
        return [[0, 0, 1, 0], [0, 0, 0, 1]]
    if t % 2 == 0:
        return unram
    return [[0, 0, 0, 1], [0, 1, 1, 0]]


def same_subspace(u, v):
    return span_rank(u) == span_rank(v) == span_rank(u + v)


def selmer_dim_formula(a, b, image2=None):
    """Sel_2 dimension from the closed-form odd/infinite local rules; the
    p = 2 image is supplied (or sampled) since it has no closed form here."""
    s = a * a + b * b
    es = (0, a * a * s, b * b * s)
    odd = lambda n: {q for q in sp.factorint(abs(n)) if q != 2}
    S_odd = sorted(odd(a) | odd(b) | odd(s) | odd(a - b) | odd(a + b))
    g = [-1, 2] + S_odd
    basis = [(x, 1) for x in g] + [(1, x) for x in g]
    rows = []
    for p in [0, 2] + S_odd:
        if p == 2:
            img = image2 if image2 is not None else local_image(es, 2)
        else:
            img = rule_image(a, b, p)
        ld = len(img[0])
        cols = [sqclass_local(u, p) + sqclass_local(w, p) for (u, w) in basis]
        for wmask in annihilator(img, ld):
            w = list(map(int, format(wmask, f"0{ld}b")))
            r = 0
            for j, c in enumerate(cols):
                if sum(wi * ci for wi, ci in zip(w, c)) % 2:
                    r |= 1 << j
            rows.append(r)
    return f2_kernel_dim(rows, len(basis))


_P2TABLE = None


def p2_key(a, b):
    k = [min(vp(n, 2)[0], 3) for n in (a, b, a - b, a + b)]
    k += [vp(a - b, 2)[1] % 8, vp(a + b, 2)[1] % 8]
    return ",".join(map(str, k))


def p2_image_table(a, b):
    """2-adic local image from the empirical 88-key table (verified conflict-free
    on 27,317 fibers, not proven); falls back to exact sampling on an unseen key."""
    global _P2TABLE
    if _P2TABLE is None:
        import json, os
        path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "route_d_selmer2_p2table.json")
        _P2TABLE = json.load(open(path))
    entry = _P2TABLE.get(p2_key(a, b))
    if entry is None:
        s = a * a + b * b
        return local_image((0, a * a * s, b * b * s), 2)
    return entry["basis"]


def selmer_dim_fast(a, b):
    return selmer_dim_formula(a, b, image2=p2_image_table(a, b))


if __name__ == "__main__":
    pairs = [tuple(map(int, s.split(":"))) for s in sys.argv[1:]]
    for a, b in pairs:
        d, n = selmer_dim(a, b)
        d2, n2 = selmer_dim(a, b, restrict_support=True)
        print(f"{a}:{b}  dim Sel2 = {d}  (full-S candidates dim {n});  "
              f"with S1/S2 support = {d2} (candidates dim {n2});  rank bound = {d - 2}")
