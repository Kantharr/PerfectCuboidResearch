"""Explicit birational model of a Route D fiber (ratio a:b, kernel al,be,ga) as a
Weierstrass curve, with forward and inverse maps, all verified symbolically.

Fiber in P^3(t:z:u2:u3):  a^2 t^2 - z^2 = al*ga*u2^2,  b^2 t^2 - z^2 = be*ga*u3^2.
Base point O = (1, z0, u20, u30) (a known rational point).
"""
import sympy as sp

lam, u, v, X, Y = sp.symbols('lam u v X Y')

def build(a, b, al, be, ga, O):
    t0 = sp.Rational(O[0])
    _, z0, u20, u30 = [sp.Rational(c) / t0 for c in O]
    A2, B2, c2, c3 = a * a, b * b, al * ga, be * ga
    zz, w2 = sp.symbols('zz w2')
    # conic zz^2 + c2 w2^2 = A2 (t=1) through (z0,u20); line w2 = u20 + lam (zz - z0)
    eq = sp.expand(zz**2 + c2 * (u20 + lam * (zz - z0))**2 - A2)
    other = sp.cancel(-sp.Poly(eq, zz).all_coeffs()[1] / sp.Poly(eq, zz).all_coeffs()[0] - z0)
    zl = sp.simplify(other)
    u2l = sp.simplify(u20 + lam * (zl - z0))
    den = sp.denom(sp.together(zl))
    # u3^2 = (B2 - z^2)/c3 ;  put V = c3 * u3 * den  => V^2 = c3 * (B2 den^2 - num^2)
    num = sp.numer(sp.together(zl))
    quart = sp.expand(c3 * (B2 * den**2 - num**2))
    # lam0: the line through O whose second intersection is O itself (tangent) -> O's image
    lam0 = sp.solve(sp.Eq(zl, z0), lam)
    lam0 = [l for l in lam0 if sp.simplify(u2l.subs(lam, l) - u20) == 0][0]
    V0 = sp.simplify(c3 * u30 * den.subs(lam, lam0))
    assert sp.simplify(V0**2 - quart.subs(lam, lam0)) == 0
    qd = sp.Poly(sp.expand(quart.subs(lam, u + lam0)), u)       # v^2 = qd(u), qd(0) = V0^2
    co = qd.all_coeffs()[::-1] + [0] * 5
    e_, d_, c_, b_, a_ = [sp.nsimplify(x) for x in co[:5]]
    q = V0
    # Connell / Mordell: v^2 = a u^4 + b u^3 + c u^2 + d u + q^2
    a1, a2, a3 = d_ / q, c_ - d_**2 / (4 * q**2), 2 * q * b_
    a4, a6 = -4 * q**2 * a_, (c_ - d_**2 / (4 * q**2)) * (-4 * q**2 * a_)
    Xf = (2 * q * (v + q) + d_ * u) / u**2
    Yf = (4 * q**2 * (v + q) + 2 * q * (d_ * u + c_ * u**2) - d_**2 * u**2 / (2 * q)) / u**3
    Uf = (2 * q * (X + c_) - d_**2 / (2 * q)) / Y
    Vf = -q + Uf * (Uf * X - d_) / (2 * q)
    W = [a1, a2, a3, a4, a6]
    # symbolic verification: forward map lands on the Weierstrass curve
    wf = sp.simplify((Yf**2 + a1 * Xf * Yf + a3 * Yf - (Xf**3 + a2 * Xf**2 + a4 * Xf + a6))
                     .subs(v, sp.sqrt(qd.as_expr())))
    assert wf == 0, wf
    return dict(zl=zl, u2l=u2l, den=den, lam0=lam0, qd=qd, q=q, W=W, Xf=Xf, Yf=Yf, Uf=Uf, Vf=Vf, c3=c3)

def fiber_to_W(M, pt):
    """rational fiber point (t,z,u2,u3), t != 0 -> Weierstrass (X,Y) (or 'O')."""
    t, z, u2, u3 = [sp.Rational(c) for c in pt]
    z, u2, u3 = z / t, u2 / t, u3 / t
    # line through O: lam = (u2 - u20)/(z - z0); handle via zl
    lamv = sp.solve(sp.Eq(M['zl'], z), lam)
    lamv = [l for l in lamv if sp.simplify(M['u2l'].subs(lam, l) - u2) == 0]
    if not lamv:
        return None
    L = lamv[0]
    uu = L - M['lam0']
    vv = M['c3'] * u3 * M['den'].subs(lam, L)
    if uu == 0:
        return 'O' if sp.simplify(vv - M['q']) == 0 else None
    return (sp.simplify(M['Xf'].subs({u: uu, v: vv})), sp.simplify(M['Yf'].subs({u: uu, v: vv})))

def W_to_fiber(M, P):
    x, y = P
    uu = sp.simplify(M['Uf'].subs({X: x, Y: y}))
    vv = sp.simplify(M['Vf'].subs({X: x, Y: y, sp.Symbol('u'): uu}).subs(u, uu))
    L = uu + M['lam0']
    z = M['zl'].subs(lam, L); u2 = M['u2l'].subs(lam, L)
    u3 = vv / (M['c3'] * M['den'].subs(lam, L))
    return (1, sp.simplify(z), sp.simplify(u2), sp.simplify(u3))
