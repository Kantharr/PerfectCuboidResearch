"""
Route D inverse map: given a rational point (X,Y) on PARI's Weierstrass
model E (as returned by ellfromeqn + ellrank), recover the corresponding
point on the original genus-1 quartic model, and from there the actual
(x,y,z) integer triple (when it exists).

Derived from scratch via sympy (not a memorized formula) on 2026-09-21,
verified against PARI's exact discriminant/j-invariant, and round-tripped
successfully on an independent known data point (not the one used to
build the transformation) before being trusted on unknown points -- see
referee_notes.md for the full derivation and a documented sign bug this
process caught and fixed.

Forward chain:  quartic point (m,Y_q) --[shift to n=m-m0]--> my (X,Y)
                --[shift X_pari = X + r]--> PARI (X,Y)
Inverse chain:  PARI (X,Y) --[X_mine = X_pari - r]--> my (X,Y)
                --[solve quadratic for n]--> n --[m = n+m0]--> m
                --[W2(m),W3(m), clear denominators]--> (u2,u3,t) or (u1,u2,t)
                --[reconstruct]--> (x,y,z)
"""

from math import gcd, isqrt
from sympy import symbols, expand, simplify, Poly, together, fraction, Rational, sqrt as ssqrt, nsimplify

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

def recover_abg(x, y, z):
    xy = squarefree_part(x * x + y * y)
    xz = squarefree_part(x * x - z * z)
    yz = squarefree_part(y * y - z * z)
    num = xz * yz
    g2 = num // xy
    g = isqrt(g2)
    assert g * g == g2 and num % xy == 0
    return xz // g, yz // g, g

class FiberXY:
    """x=a*t, y=b*t fixed; conic in (u2,u3,t): gamma*(alpha*u2^2-beta*u3^2)=(a^2-b^2)*t^2."""
    def __init__(self, alpha, beta, gamma, a, b, seed_xyz):
        self.alpha, self.beta, self.gamma, self.a, self.b = alpha, beta, gamma, a, b
        x, y, z = seed_xyz
        t0 = gcd(x, y)
        u2_0 = isqrt((x * x - z * z) // (alpha * gamma))
        u3_0 = isqrt((y * y - z * z) // (beta * gamma))
        assert alpha * gamma * u2_0**2 == x * x - z * z
        assert beta * gamma * u3_0**2 == y * y - z * z
        self.u2_0, self.u3_0, self.t0 = u2_0, u3_0, t0

        m, W2 = symbols('m W2')
        W3_line = u3_0 + m * (W2 - u2_0)
        conic = expand(alpha * W2**2 - beta * W3_line**2 - Rational(a*a - b*b, gamma) * t0**2)
        poly = Poly(conic, W2)
        A, B, C = poly.all_coeffs()
        self.W2_of_m = simplify(C / (A * u2_0))
        self.W3_of_m = simplify(u3_0 + m * (self.W2_of_m - u2_0))
        self.m_sym = m

        Z2 = a**2 * t0**2 - alpha * gamma * self.W2_of_m**2
        num, den = fraction(together(Z2))
        self.quartic_num = expand(num)  # Y_q^2 = this, in variable m

        qpoly = Poly(self.quartic_num, m)
        c = qpoly.all_coeffs()
        while len(c) < 5:
            c = [0] + c
        self.a4, self.a3, self.a2, self.a1, self.a0 = c

    def quartic_val(self, mval):
        return self.a4*mval**4 + self.a3*mval**3 + self.a2*mval**2 + self.a1*mval + self.a0

    def m_to_xyz(self, mval):
        """Given a rational m, recover (x,y,z) by clearing denominators.
        W2(m),W3(m) are values in the T=t0 chart; the integer representative
        is (W2*D, W3*D, t0*D) for D clearing their denominators -- NOT
        (W2*D, W3*D, D) -- t0 must be carried along, since the parametrization
        is normalized relative to the base point's own t0, not to 1."""
        if getattr(mval, 'free_symbols', None) or (hasattr(mval, 'is_finite') and mval.is_finite is False):
            return None
        W2v = self.W2_of_m.subs(self.m_sym, mval)
        W3v = self.W3_of_m.subs(self.m_sym, mval)
        _, d2 = fraction(together(W2v))
        _, d3 = fraction(together(W3v))
        from sympy import lcm as slcm
        D = slcm(d2, d3)
        U2 = simplify(W2v * D)
        U3 = simplify(W3v * D)
        T = self.t0 * D
        g = gcd(gcd(int(U2), int(U3)), int(T))
        U2, U3, T = int(U2)//g, int(U3)//g, int(T)//g
        x = self.a * T
        y = self.b * T
        z2 = x*x - self.alpha*self.gamma*U2*U2
        if z2 < 0:
            return None
        z = isqrt(z2)
        if z*z != z2:
            return None
        return (x, y, z)

    def build_weierstrass_and_shift(self, seed_m):
        """Build my Weierstrass model centered at seed_m, return (A2,A1,A0,y0,m0)
        plus the shift r to PARI's model IF given PARI's a2 target."""
        m = self.m_sym
        n = symbols('n')
        shifted = expand(self.quartic_val(m).subs(m, n + seed_m))
        poly = Poly(shifted, n)
        b4, b3, b2, b1, b0 = poly.all_coeffs()
        return b4, b3, b2, b1, b0

class FiberYZ:
    """y=p*t, z=q*t fixed; conic in (u1,u2,t): alpha*(beta*u1^2-gamma*u2^2)=(p^2+q^2)*t^2."""
    def __init__(self, alpha, beta, gamma, p, q, seed_xyz):
        self.alpha, self.beta, self.gamma, self.p, self.q = alpha, beta, gamma, p, q
        x, y, z = seed_xyz
        t0 = gcd(y, z)
        u1_0 = isqrt((x*x + y*y) // (alpha*beta))
        u2_0 = isqrt((x*x - z*z) // (alpha*gamma))
        assert alpha*beta*u1_0**2 == x*x+y*y
        assert alpha*gamma*u2_0**2 == x*x-z*z
        self.u1_0, self.u2_0, self.t0 = u1_0, u2_0, t0

        m, U1 = symbols('m U1')
        U2_line = u2_0 + m*(U1 - u1_0)
        conic = expand(alpha*beta*U1**2 - alpha*gamma*U2_line**2 - (p*p+q*q)*t0**2)
        poly = Poly(conic, U1)
        A, B, C = poly.all_coeffs()
        self.U1_of_m = simplify(C / (A * u1_0))
        self.U2_of_m = simplify(u2_0 + m*(self.U1_of_m - u1_0))
        self.m_sym = m

        X2 = alpha*beta*self.U1_of_m**2 - (p*t0)**2
        num, den = fraction(together(X2))
        self.quartic_num = expand(num)  # Y_q^2 = this (the "X" of the yz case), in variable m

        qpoly = Poly(self.quartic_num, m)
        c = qpoly.all_coeffs()
        while len(c) < 5:
            c = [0] + c
        self.a4, self.a3, self.a2, self.a1, self.a0 = c

    def quartic_val(self, mval):
        return self.a4*mval**4 + self.a3*mval**3 + self.a2*mval**2 + self.a1*mval + self.a0

    def m_to_xyz(self, mval):
        """See FiberXY.m_to_xyz's note: T must be t0*D, not D."""
        if getattr(mval, 'free_symbols', None) or (hasattr(mval, 'is_finite') and mval.is_finite is False):
            return None
        U1v = self.U1_of_m.subs(self.m_sym, mval)
        U2v = self.U2_of_m.subs(self.m_sym, mval)
        _, d1 = fraction(together(U1v))
        _, d2 = fraction(together(U2v))
        from sympy import lcm as slcm
        D = slcm(d1, d2)
        U1, U2, T = simplify(U1v*D), simplify(U2v*D), self.t0*D
        g = gcd(gcd(int(U1), int(U2)), int(T))
        U1, U2, T = int(U1)//g, int(U2)//g, int(T)//g
        y = self.p * T
        z = self.q * T
        x2 = self.alpha*self.beta*U1*U1 - y*y
        if x2 < 0:
            return None
        x = isqrt(x2)
        if x*x != x2:
            return None
        return (x, y, z)

    def build_weierstrass_and_shift(self, seed_m):
        m = self.m_sym
        n = symbols('n')
        shifted = expand(self.quartic_val(m).subs(m, n + seed_m))
        poly = Poly(shifted, n)
        b4, b3, b2, b1, b0 = poly.all_coeffs()
        return b4, b3, b2, b1, b0


def find_r(b4, b3, b2, b1, b0, target_a2, target_a4, target_a6):
    """Find r such that substituting X -> Xp - r in my cubic gives PARI's (a2,a4,a6)."""
    A2 = b2
    A1 = -(4*b0*b4 - b1*b3)
    A0 = -(4*b0*b2*b4 - b0*b3**2 - b1**2*b4)
    X, r, Xp = symbols('X r Xp')
    cubic = X**3 + A2*X**2 + A1*X + A0
    cubic_new = expand(cubic.subs(X, Xp - r))
    poly = Poly(cubic_new, Xp)
    c3, c2, c1, c0 = poly.all_coeffs()
    from sympy import solve
    r_sol = solve(c2 - target_a2, r)
    for rv in r_sol:
        a4v = simplify(c1.subs(r, rv))
        a6v = simplify(c0.subs(r, rv))
        if a4v == target_a4 and a6v == target_a6:
            return rv, (A2, A1, A0)
    raise ValueError("no matching r found -- model mismatch")

def pari_point_to_m(fiber, seed_m, r, X_pari, Y_pari):
    """Invert: PARI (X,Y) -> quartic parametrization value m."""
    b4, b3, b2, b1, b0 = fiber.build_weierstrass_and_shift(seed_m)
    y0 = ssqrt(b0)
    X_mine = X_pari - r
    A_coef = X_mine**2 - 4*b0*b4
    B_coef = -(2*X_mine*b1 + 4*b0*b3)
    Y_raw = 4*y0*Y_pari
    n_rec = (Y_raw - B_coef) / (2*A_coef)
    return simplify(n_rec + seed_m)

if __name__ == "__main__":
    # ---- self-test on the 39:37 fiber, independent point (t=173) ----
    alpha, beta, gamma, a, b = 5, 2, 19, 39, 37
    seed = (39, 37, 1)  # t=1
    fib = FiberXY(alpha, beta, gamma, a, b, seed)
    seed_m = Rational(25, 14)  # the point used to center the Weierstrass shift (t=27 data)
    r, (A2, A1, A0) = find_r(*fib.build_weierstrass_and_shift(seed_m),
                              target_a2=-115540, target_a4=3326975600, target_a6=66585736000)
    print("r =", r)

    # known independent point: t=173 -> (6747,6401,6253), m=17/9
    X_pari, Y_pari = Rational(1432620), Rational(1645582400)
    m_rec = pari_point_to_m(fib, seed_m, r, X_pari, Y_pari)
    print("recovered m =", m_rec, " (expect 17/9)")
    xyz = fib.m_to_xyz(m_rec)
    print("recovered (x,y,z) =", xyz, " (expect (6747,6401,6253))")

    # ---- self-test on the 53:49 (yz-fixed) fiber, independent point ----
    print("\n--- yz-fixed self-test: 53:49 fiber ---")
    alpha2, beta2, gamma2, p2, q2 = 5, 34, 3, 53, 49
    seed2 = (2597, 2279, 2107)  # t=43
    fib2 = FiberYZ(alpha2, beta2, gamma2, p2, q2, seed2)
    # use the seed point itself as the Weierstrass-centering point this time (u1_0 -> m=infinity there;
    # instead center on the SAME seed's own m, which requires finding it first via a fresh line through
    # a DIFFERENT known point). Use the base point's own natural finite m if it has one, else pick the
    # second known member (4109,3233,2989) to center on, and test round-trip on a THIRD point.
    x3, y3, z3 = 4109, 3233, 2989
    t3 = 61
    u1_3 = isqrt((x3*x3+y3*y3)//(alpha2*beta2))
    u2_3 = isqrt((x3*x3-z3*z3)//(alpha2*gamma2))
    from sympy import solve as ssolve
    msym = fib2.m_sym
    scale3 = Rational(fib2.t0, t3)
    sols = ssolve(fib2.U1_of_m - u1_3*scale3, msym)
    seed_m2 = None
    for mv in sols:
        if simplify(fib2.U2_of_m.subs(msym, mv) - u2_3*scale3) == 0:
            seed_m2 = mv
            break
    print("centering m for (4109,3233,2989):", seed_m2)

    target_a2, target_a4, target_a6 = 4435370244, 2687632115455841904, -2093816872435291837382735424
    r2, _ = find_r(*fib2.build_weierstrass_and_shift(seed_m2),
                    target_a2=target_a2, target_a4=target_a4, target_a6=target_a6)
    print("r2 =", r2)

    # Now build a THIRD independent point to test: need another known (5,34,3) triple with y:z=53:49.
    # (13861,6943,6419), t=131
    x4, y4, z4 = 13861, 6943, 6419
    t4 = 131
    u1_4 = isqrt((x4*x4+y4*y4)//(alpha2*beta2))
    u2_4 = isqrt((x4*x4-z4*z4)//(alpha2*gamma2))
    scale4 = Rational(fib2.t0, t4)
    sols4 = ssolve(fib2.U1_of_m - u1_4*scale4, msym)
    m4 = None
    for mv in sols4:
        if simplify(fib2.U2_of_m.subs(msym, mv) - u2_4*scale4) == 0:
            m4 = mv
            break
    print("m for test point (13861,6943,6419):", m4)

    # forward: compute (X_pari,Y_pari) for this test point, then invert and recover xyz
    b4,b3,b2,b1,b0 = fib2.build_weierstrass_and_shift(seed_m2)
    y0_2 = ssqrt(b0)
    n4 = m4 - seed_m2
    Yq4 = ssqrt(fib2.quartic_val(m4))
    X_mine4 = simplify((2*b0 + b1*n4 + 2*y0_2*Yq4)/n4**2)
    A_c = X_mine4**2 - 4*b0*b4
    B_c = -(2*X_mine4*b1 + 4*b0*b3)
    Y_mine4 = simplify((2*A_c*n4 + B_c)/(4*y0_2))
    X_pari4 = X_mine4 + r2
    Y_pari4 = Y_mine4
    print("forward-mapped point on PARI curve:", (X_pari4, Y_pari4))
    lhs4 = Y_pari4**2
    rhs4 = X_pari4**3 + target_a2*X_pari4**2 + target_a4*X_pari4 + target_a6
    print("on-curve check:", simplify(lhs4-rhs4)==0)

    m_rec4 = pari_point_to_m(fib2, seed_m2, r2, X_pari4, Y_pari4)
    print("recovered m:", m_rec4, " expected:", m4)
    xyz4 = fib2.m_to_xyz(m_rec4)
    print("recovered (x,y,z):", xyz4, " expected: (13861,6943,6419)")
