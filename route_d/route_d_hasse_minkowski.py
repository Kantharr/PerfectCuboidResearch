"""
Route D, unbiased sampling via Hasse-Minkowski (2026-09-22).

The 21 fibers tested so far all exist in the sample because a brute-force
line search already found an integer point on them -- a real selection
bias, since a rank-0 curve (finitely many points, often none of them
small) is exactly the kind of fiber such a search is least likely to ever
surface. This module removes that bias: the conic each fiber reduces to,

    gamma*(alpha*u2^2 - beta*u3^2) = (a^2-b^2)*t^2

is a genuine ternary quadratic form (alpha*gamma*U2^2 - beta*gamma*U3^2 -
(a^2-b^2)*T^2 = 0). By the Hasse-Minkowski theorem, it has a nontrivial
rational solution iff it is isotropic over R and every Q_p -- a decidable,
provable condition, checked here via PARI/GP's qfsolve (which both decides
isotropy AND constructs an explicit point when isotropic), with NO
dependence on whether a brute-force search has ever found an actual
integer (x,y,z) on that fiber.

Given ANY point on the conic (not necessarily corresponding to a genuine
integer triple), the same Vieta-based construction used throughout Route D
still produces a valid quartic model -- the seed point only needs to make
the parametrization well-defined, not to itself be a solution of the
original problem.
"""

import sys, subprocess, os
from math import gcd, isqrt
from sympy import symbols, expand, simplify, Poly, together, fraction, Rational

GP = os.environ.get("PARI_GP_PATH", "gp")


def factorize(n):
    f = {}; d = 2; n = abs(n)
    while d * d <= n:
        while n % d == 0:
            f[d] = f.get(d, 0) + 1
            n //= d
        d += 1 if d == 2 else 2
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f


def squarefree_part(n):
    r = 1
    for p, e in factorize(n).items():
        if e % 2 == 1:
            r *= p
    return r


def is_prime(n):
    if n < 2: return False
    if n % 2 == 0: return n == 2
    i = 3
    while i * i <= n:
        if n % i == 0: return False
        i += 2
    return True


def valid_alpha_beta_splits(product):
    """Enumerate (alpha,beta) splits of a squarefree product respecting
    Theorem 4.1: exactly one of alpha,beta even (if 2 | product), the rest
    split arbitrarily among the odd (all =1 mod 4) prime factors."""
    f = factorize(product)
    has_two = 2 in f
    odd_primes = [p for p in f if p != 2]
    splits = []
    n = len(odd_primes)
    for mask in range(1 << n):
        alpha_odd = 1
        beta_odd = 1
        for i, p in enumerate(odd_primes):
            if mask & (1 << i):
                alpha_odd *= p
            else:
                beta_odd *= p
        if has_two:
            splits.append((2 * alpha_odd, beta_odd))
            splits.append((alpha_odd, 2 * beta_odd))
        else:
            splits.append((alpha_odd, beta_odd))
    # dedupe (alpha,beta) vs (beta,alpha) not deduped -- both are legitimate,
    # distinct fibers (they govern different equations)
    return list(set(splits))


def qfsolve_point(alpha, beta, gamma, a, b):
    """Run PARI's qfsolve on the fiber's ternary form; return (u2,u3,t) as
    integers (clearing any denominators) if isotropic, else None."""
    A, B, C = alpha * gamma, -beta * gamma, -(a * a - b * b)
    script = f"G = [{A},0,0;0,{B},0;0,0,{C}]; v = qfsolve(G); if(type(v)==\"t_COL\", print(\"SOL:\", v[1], \" \", v[2], \" \", v[3]), print(\"NONE\"))"
    try:
        out = subprocess.run([GP, "-q"], input=script, capture_output=True, text=True, timeout=20)
    except subprocess.TimeoutExpired:
        return None
    for line in out.stdout.splitlines():
        if line.startswith("SOL:"):
            parts = line[4:].split()
            u2, u3, t = (Rational(x) for x in parts)
            # clear denominators to get an integer point (projective, any scalar multiple is fine)
            from sympy import lcm as slcm, fraction as sfraction
            d2 = sfraction(u2)[1]; d3 = sfraction(u3)[1]; dt = sfraction(t)[1]
            D = slcm(slcm(d2, d3), dt)
            U2, U3, T = int(u2 * D), int(u3 * D), int(t * D)
            g = gcd(gcd(abs(U2), abs(U3)), abs(T))
            if g == 0:
                return None
            return (U2 // g, U3 // g, T // g)
    return None


def derive_quartic_from_conic_point(alpha, beta, gamma, a, b, u2_0, u3_0, t0):
    """Same Vieta-based derivation as route_d_inverse_map.FiberXY, but seeded
    from an arbitrary conic point (not necessarily an actual (x,y,z))."""
    if u2_0 == 0:
        return None  # base point at a coordinate axis -- parametrization needs u2_0 != 0
    m, W2 = symbols('m W2')
    W3_line = u3_0 + m * (W2 - u2_0)
    conic = expand(alpha * W2**2 - beta * W3_line**2 - Rational(a*a - b*b, gamma) * t0**2)
    poly = Poly(conic, W2)
    coeffs = poly.all_coeffs()
    if len(coeffs) < 3:
        return None
    A, Bc, Cc = coeffs
    if A == 0:
        return None
    W2_other = simplify(Cc / (A * u2_0))

    Z2 = a**2 * t0**2 - alpha * gamma * W2_other**2
    num, den = fraction(together(Z2))
    num = expand(num)
    qpoly = Poly(num, m)
    c = qpoly.all_coeffs()
    while len(c) < 5:
        c = [0] + c
    return c  # [c4,c3,c2,c1,c0]


def ellrootno_for_quartic(coeffs, timeout=30):
    c4, c3, c2, c1, c0 = coeffs
    script = f"""
f = y^2 - ({c4}*x^4 + ({c3})*x^3 + ({c2})*x^2 + ({c1})*x + ({c0}));
E = ellinit(ellfromeqn(f));
print("COND: ", ellglobalred(E)[1]);
print("ROOTNO: ", ellrootno(E));
"""
    try:
        out = subprocess.run([GP, "-q"], input=script, capture_output=True, text=True, timeout=timeout)
        return out.stdout
    except subprocess.TimeoutExpired:
        return "TIMEOUT"


if __name__ == "__main__":
    print(__doc__)
