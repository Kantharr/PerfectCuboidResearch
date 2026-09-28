"""Mechanical check of the written proofs of the odd-prime / infinity local
images for E(a,b): y^2 = x(x-e2)(x-e3), e2=a^2 s, e3=b^2 s, s=a^2+b^2.

For every bad prime this follows the proof literally: it builds exactly the
witness points the proof uses, checks each is a genuine Q_p-point (f(x) a
nonzero p-adic square), checks the Kummer vector equals the one the proof
claims, and checks the span equals rule_image() from route_d_selmer2.py.
It also verifies the character-sum count N(eps1,eps2;c) used for existence.
"""
import sys
from fractions import Fraction
from math import gcd

from route_d_selmer2 import (sqclass_local, is_local_square, span_rank,
                             same_subspace, rule_image, prime_class, vp)
import sympy as sp


def leg(u, p):
    u %= p
    if u == 0:
        return 0
    return 1 if pow(u, (p - 1) // 2, p) == 1 else -1


def N_formula(e1, e2, c, p):
    """#{u in F_p : (u/p)=e1, ((u+c)/p)=e2}, c != 0 mod p."""
    return (p - 2 - e1 * leg(-c, p) - e2 * leg(c, p) - e1 * e2) // 4


def N_enum(e1, e2, c, p):
    return sum(1 for u in range(1, p) if leg(u, p) == e1 and leg(u + c, p) == e2)


def find_unit(p, pred):
    for u in range(1, p):
        if pred(u):
            return u
    return None


class Fail(Exception):
    pass


def check_prime(a, b, p):
    s = a * a + b * b
    e2, e3 = a * a * s, b * b * s
    f = lambda x: x * (x - e2) * (x - e3)
    delta = lambda x: sqclass_local(x, p) + sqclass_local(x - e2, p)
    T1 = sqclass_local(1, p) + sqclass_local(-s, p)
    T2 = sqclass_local(s, p) + sqclass_local(a * a - b * b, p)

    def point(x, claimed):
        x = Fraction(x)
        if not is_local_square(f(x), p):
            raise Fail(f"witness x={x} not a Q_{p}-point")
        if delta(x) != claimed:
            raise Fail(f"witness x={x}: delta={delta(x)} but proof claims {claimed}")
        return claimed

    cls = prime_class(p, a, b)
    n = find_unit(p, lambda u: leg(u, p) == -1)
    if cls == "s_odd":
        W = [T1, T2]
        if T1[0] != 0 or T1[2] != 1 or T2[0] != 1 or T2[2] != 0:
            raise Fail("s_odd: torsion valuation pattern differs from proof")
    elif cls == "s_even":
        return "s_even (containment proof, no witnesses)"
    elif cls == "a":
        if p % 4 == 1:
            W = [point(p * 1, [1, 0, 1, 0]), point(p * n, [1, 1, 1, 1])]
        else:
            if T1 != [0, 0, 0, 1]:
                raise Fail(f"a, p=3 mod 4: delta(T1)={T1}, proof claims [0,0,0,1]")
            c = e3 % p
            if leg(c, p) != 1 or N_formula(-1, 1, -c, p) != (p + 1) // 4:
                raise Fail("a, p=3 mod 4: count premise fails")
            x = find_unit(p, lambda u: leg(u, p) == -1 and leg(u - c, p) == 1)
            W = [T1, point(x, [0, 1, 0, 1])]
    elif cls == "b":
        if p % 4 == 1:
            W = [point(p * 1, [1, 0, 0, 0]), point(p * n, [1, 1, 0, 0])]
        else:
            if T1 != [0, 0, 0, 1]:
                raise Fail(f"b, p=3 mod 4: delta(T1)={T1}, proof claims [0,0,0,1]")
            c = e2 % p
            if leg(c, p) != 1 or N_formula(-1, 1, -c, p) != (p + 1) // 4:
                raise Fail("b, p=3 mod 4: count premise fails")
            x = find_unit(p, lambda u: leg(u, p) == -1 and leg(u - c, p) == 1)
            W = [T1, point(x, [0, 1, 0, 0])]
    elif cls in ("m", "p"):
        t = vp(a - b if cls == "m" else a + b, p)[0]
        c = e2 % p
        if leg(c, p) != leg(2, p):
            raise Fail("m/p: chi(e2) != chi(2)")
        if p % 8 in (1, 7):
            if N_formula(-1, 1, c, p) < 1:
                raise Fail("m/p split: count < 1")
            u = find_unit(p, lambda u: leg(u, p) == -1 and leg(e2 + u, p) == 1)
            wA = point(e2 + u, [0, 0, 0, 1])
            if t >= 2:
                wB = point(e2 + p, [0, 0, 1, 0])
            else:
                if T2[:3] != [0, 0, 1]:
                    raise Fail("m/p split, t=1: delta(T2) not (0,0,1,*)")
                wB = T2
            W = [wA, wB]
        else:
            if N_formula(1, -1, -c, p) != (p - leg(-1, p)) // 4 or N_formula(1, -1, -c, p) < 1:
                raise Fail("m/p nonsplit: count premise fails")
            x = find_unit(p, lambda u: leg(u, p) == 1 and leg(u - c, p) == -1)
            wC = point(x, [0, 0, 0, 1])
            if T2[:3] != [0, 1, t % 2]:
                raise Fail(f"m/p nonsplit: delta(T2)={T2}, proof claims (0,1,{t%2},*)")
            W = [wC, T2]
    else:
        raise Fail(f"unexpected class {cls}")
    if span_rank(W) != 2:
        raise Fail(f"{cls}: witnesses span dim {span_rank(W)} != 2")
    if not same_subspace(W, rule_image(a, b, p)):
        raise Fail(f"{cls}: proof's span != rule_image")
    return cls


def check_infinity(a, b):
    s = a * a + b * b
    e2, e3 = a * a * s, b * b * s
    lo, hi = min(e2, e3), max(e2, e3)
    # real points: x in [0, lo] or x >= hi; sample both components and T1
    xs = [Fraction(lo, 2), Fraction(lo, 7), hi, hi + 1, hi * 3]
    for x in xs:
        if x * (x - e2) * (x - e3) < 0:
            raise Fail("infinity: sample not a real point")
        if x <= 0:
            raise Fail("infinity: d1 <= 0 on a real point")
    T1 = sqclass_local(1, 0) + sqclass_local(-s, 0)
    if T1 != [0, 1] or not same_subspace([T1], rule_image(a, b, 0)):
        raise Fail("infinity: torsion/rule mismatch")


if __name__ == "__main__":
    amax = int(sys.argv[1]) if len(sys.argv) > 1 else 120
    # 1. character-sum identity, by enumeration
    for p in sp.primerange(3, 400):
        for c in range(1, p):
            for e1 in (1, -1):
                for e2 in (1, -1):
                    if N_formula(e1, e2, c, p) != N_enum(e1, e2, c, p):
                        raise SystemExit(f"N formula wrong at p={p}, c={c}, {e1},{e2}")
    print("character-sum formula N(e1,e2;c): verified for all odd p < 400, all c, all signs")
    # 2. every bad prime of every fiber
    from collections import Counter
    tally = Counter()
    for a in range(2, amax):
        for b in range(1, a):
            if gcd(a, b) != 1:
                continue
            s = a * a + b * b
            for p in sorted(sp.factorint(a * b * s * (a * a - b * b))):
                if p == 2:
                    continue
                tally[check_prime(a, b, p)] += 1
            check_infinity(a, b)
            tally["infinity"] += 1
    print("all proofs' witness constructions check out; counts:", dict(tally))
