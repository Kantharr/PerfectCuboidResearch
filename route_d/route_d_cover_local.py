"""Exhaustive p-adic test: does the cuboid cover C: W^2 = F have a Q_p-point?

Fiber (ratio a:b, kernel alpha,beta,gamma), s^2 = (a^2+b^2)/(alpha*beta), in P^3(t:z:u2:u3):
    a^2 t^2 - z^2 = alpha*gamma*u2^2,    b^2 t^2 - z^2 = beta*gamma*u3^2
F = m S (m-k),  m = a b t^2 z,  S = (a^2+b^2) t^2 - z^2,  k = alpha*beta*gamma*s*t*u2*u3.

Tree search over primitive p-adic points (four charts), keeping residue classes
mod p^k that satisfy both equations, discarding a class once F's square class
on it is determined and non-square. If every class dies, C(Q_p) is empty
(a branch surviving forever would converge to a Q_p-point with F = 0, i.e. a
point of C). Returns ("EMPTY", stats) or ("POINT", witness-class).
"""
import sys
from itertools import product


def make(a, b, al, be, ga, s):
    ab, s2 = a * b, a * a + b * b
    kc = al * be * ga * s

    def eqs(t, z, u2, u3):
        return (a * a * t * t - z * z - al * ga * u2 * u2, b * b * t * t - z * z - be * ga * u3 * u3)

    def F(t, z, u2, u3):
        m = ab * t * t * z
        return m * (s2 * t * t - z * z) * (m - kc * t * u2 * u3)

    return eqs, F


def sq_status(val, k, p):
    """val = F(x0) for a class mod p^k.  Returns 'nonsq', 'sq', or None (undecided)."""
    val %= p ** k
    if val == 0:
        return None
    v = 0
    while val % p == 0:
        val //= p
        v += 1
    rem = k - v                      # unit part known mod p^rem
    if v % 2:
        return "nonsq"
    if p == 2:
        if rem < 3:
            return None
        return "sq" if val % 8 == 1 else "nonsq"
    if rem < 1:
        return None
    return "sq" if pow(val % p, (p - 1) // 2, p) == 1 else "nonsq"


def search(a, b, al, be, ga, s, p, kmax=40, cap=2_000_000):
    eqs, F = make(a, b, al, be, ga, s)
    # chart c: coordinate c is 1, coordinates before it are in pZ_p, after it in Z_p
    total_classes = 0
    for chart in range(4):
        level = 1
        classes = []
        for free in product(range(p), repeat=3):
            v = list(free[:chart]) + [1] + list(free[chart:])
            if any(v[i] % p for i in range(chart)):
                continue
            if all(e % p == 0 for e in eqs(*v)):
                classes.append(tuple(v))
        while classes:
            total_classes += len(classes)
            if total_classes > cap:
                return ("GAVE_UP", chart, level, len(classes))
            nxt = []
            mod = p ** level
            for v in classes:
                st = sq_status(F(*v), level, p)
                if st == "nonsq":
                    continue
                if st == "sq":
                    return ("POINT", chart, level, v)
                if level >= kmax:
                    return ("DEEP", chart, level, v)
                # refine: lift the free coordinates by p^level
                for d in product(range(p), repeat=3):
                    w = list(v)
                    idx = [i for i in range(4) if i != chart]
                    for i, di in zip(idx, d):
                        w[i] = v[i] + di * mod
                    if all(e % (mod * p) == 0 for e in eqs(*w)):
                        nxt.append(tuple(w))
            classes = nxt
            level += 1
    return ("EMPTY", total_classes)


if __name__ == "__main__":
    a, b, al, be, ga, s = map(int, sys.argv[1:7])
    for p in map(int, sys.argv[7:]):
        print(f"fiber {a}:{b} kernel ({al},{be},{ga}), p={p}:", search(a, b, al, be, ga, s, p))
