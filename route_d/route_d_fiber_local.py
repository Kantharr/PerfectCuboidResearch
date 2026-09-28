"""Exact test: does a Route D fiber (a genus-1 intersection of two quadrics)
    a^2 t^2 - z^2 = al*ga*u2^2,   b^2 t^2 - z^2 = be*ga*u3^2
have a Q_p-point?

Tree search over primitive vectors (four charts). A class mod p^k that satisfies
both equations mod p^k is certified to contain a genuine Q_p-point by the
multivariate Hensel lemma once k >= 2e+1, where e = min valuation of the 2x2
minors of the Jacobian at the representative. If every branch dies, there is
no Q_p-point (compactness: a branch surviving forever converges to a point).
Returns ("POINT", chart, level, rep) or ("EMPTY", classes_examined).
"""
import sys
from itertools import product, combinations


def vp(n, p):
    if n == 0:
        return 10**9
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


def solve_mod_p(M, r, p):
    """All d in F_p^n with M d = r (mod p); M is a list of rows."""
    n = len(M[0])
    A = [[x % p for x in row] + [y % p] for row, y in zip(M, r)]
    piv = []
    row = 0
    for col in range(n):
        pr = next((i for i in range(row, len(A)) if A[i][col]), None)
        if pr is None:
            continue
        A[row], A[pr] = A[pr], A[row]
        inv = pow(A[row][col], -1, p)
        A[row] = [x * inv % p for x in A[row]]
        for i in range(len(A)):
            if i != row and A[i][col]:
                f = A[i][col]
                A[i] = [(x - f * y) % p for x, y in zip(A[i], A[row])]
        piv.append(col)
        row += 1
    if any(all(x == 0 for x in A[i][:n]) and A[i][n] for i in range(len(A))):
        return []
    free = [c for c in range(n) if c not in piv]
    sols = []
    for fv in product(range(p), repeat=len(free)):
        d = [0] * n
        for c, v in zip(free, fv):
            d[c] = v
        for i, c in enumerate(piv):
            d[c] = (A[i][n] - sum(A[i][fc] * d[fc] for fc in free)) % p
        sols.append(d)
    return sols


_ROOTS = {}


def roots_table(p):
    if p not in _ROOTS:
        tab = {}
        for u in range(p):
            tab.setdefault(u * u % p, []).append(u)
        _ROOTS[p] = tab
    return _ROOTS[p]


def solve_sq(A, c, p):
    """all u mod p with A - c u^2 = 0 (mod p)"""
    A %= p
    c %= p
    if c == 0:
        return list(range(p)) if A == 0 else []
    return roots_table(p).get(A * pow(c, -1, p) % p, [])


def level1_points(a, b, c2, c3, p, chart):
    """points mod p of the fiber in the given chart, in O(p) instead of O(p^3)."""
    out = []
    if chart == 0:
        tz = [(1, z) for z in range(p)]
    elif chart == 1:
        tz = [(0, 1)]
    else:
        tz = [(0, 0)]
    for t, z in tz:
        A1, A2 = a * a * t * t - z * z, b * b * t * t - z * z
        if chart == 2:
            U2 = [1] if (A1 - c2) % p == 0 else []
        elif chart == 3:
            U2 = [0] if A1 % p == 0 else []   # u2 in pZ_p
        else:
            U2 = solve_sq(A1, c2, p)
        if chart == 3:
            U3 = [1] if (A2 - c3) % p == 0 else []
        else:
            U3 = solve_sq(A2, c3, p)
        if chart == 3:
            U2 = [u for u in U2 if u % p == 0]
        for u2 in U2:
            for u3 in U3:
                out.append((t, z, u2, u3))
    return out


def search(a, b, al, be, ga, p, kmax=60, cap=3_000_000):
    c2, c3 = al * ga, be * ga

    def eqs(t, z, u2, u3):
        return (a * a * t * t - z * z - c2 * u2 * u2, b * b * t * t - z * z - c3 * u3 * u3)

    def minor_val(t, z, u2, u3):
        J = [(2 * a * a * t, -2 * z, -2 * c2 * u2, 0), (2 * b * b * t, -2 * z, 0, -2 * c3 * u3)]
        return min(vp(J[0][i] * J[1][j] - J[0][j] * J[1][i], p) for i, j in combinations(range(4), 2))

    total = 0
    for chart in range(4):
        level = 1
        classes = level1_points(a, b, c2, c3, p, chart)
        assert all(all(e % p == 0 for e in eqs(*v)) for v in classes)
        while classes:
            total += len(classes)
            if total > cap:
                return ("GAVE_UP", chart, level)
            nxt = []
            mod = p ** level
            for v in classes:
                e = minor_val(*v)
                if e < level and level >= 2 * e + 1:
                    return ("POINT", chart, level, v)
                if level >= kmax:
                    return ("DEEP", chart, level, v)
                # w = v + p^level d: for level >= 1 the quadratic term vanishes mod
                # p^(level+1), so the lifting condition is linear in d mod p.
                idx = [i for i in range(4) if i != chart]
                t, z, u2, u3 = v
                J = [(2 * a * a * t, -2 * z, -2 * c2 * u2, 0), (2 * b * b * t, -2 * z, 0, -2 * c3 * u3)]
                M = [[J[0][i] for i in idx], [J[1][i] for i in idx]]
                r = [-(e // mod) for e in eqs(*v)]
                for d in solve_mod_p(M, r, p):
                    w = list(v)
                    for i, di in zip(idx, d):
                        w[i] = v[i] + di * mod
                    assert all(x % (mod * p) == 0 for x in eqs(*w))
                    nxt.append(tuple(w))
            classes = nxt
            level += 1
    return ("EMPTY", total)


def bad_primes(a, b, al, be, ga):
    import sympy as sp
    N = 2 * a * b * (a * a + b * b) * (a * a - b * b) * al * be * ga
    return sorted(sp.factorint(N))


if __name__ == "__main__":
    a, b, al, be, ga = map(int, sys.argv[1:6])
    for p in bad_primes(a, b, al, be, ga):
        print(f"  p={p}: {search(a, b, al, be, ga, p)}", flush=True)
