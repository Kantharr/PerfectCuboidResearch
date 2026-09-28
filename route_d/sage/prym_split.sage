# Elliptic factors of the four Prym surfaces of the 11:3 (65,2,1) fiber via the reflections
# r(P) = T - P of E' (T = B1 or B3), following route_d_prym_split.gp, but over number fields.
# For D_h: W^2 = h F, Tr/Nm of hF over K(E')/Q(u); if Nm = c M^2, the quotient curves are
# V^2 = Tr +- 2 sqrt(c) M over Q(sqrt c).  Jacobian of V^2 = quartic via invariants I, J.
import time
a, b, al, be, ga, s = 11, 3, 65, 2, 1, 1
c2, c3, S2, kc, ab = al*ga, be*ga, a^2 + b^2, al*be*ga*s, a*b
Fu.<u> = FunctionField(QQ)
Px.<x> = Fu[]
kx = x*(x - a^2)*(x - b^2)/(c2*c3)
x0 = QQ(14157)/1690
Ts = {"B1": (QQ(130), QQ(-33)), "B3": (x0, 33*x0/130)}
H = {1: Px(1), 2: x, 3: (a^2 - x)/c2, 4: (b^2 - x)/c3}

def trnm(T, hi):
    xT, yT = T
    yl = u*(x - xT) - yT
    Q = (yl^2 - kx) // (x - xT)
    assert (yl^2 - kx) % (x - xT) == 0 and Q.degree() == 2
    L = Px.quotient(Q)
    Fm = L(H[hi]*ab*(S2 - x)*(ab*x - kc*yl))
    return Fm.matrix().trace(), Fm.matrix().det()

def const_times_square(R):
    # R in Q(u): return (c squarefree, M) with R = c*M^2, else None
    n, d = R.numerator(), R.denominator()
    f = (n*d).factor()
    if any(e % 2 for _, e in f):
        return None
    c = f.unit()
    csf = c.squarefree_part()
    M = sqrt(c/csf) * prod(p^(e//2) for p, e in f) / d
    return csf, M

def jacobian_of_quartic(q):
    # q = e0 + e1 u + ... + e4 u^4 (degree 3 or 4) over a number field; returns E: y^2 = x^3 - 27I x - 27J
    cs = list(q) + [0]*(5 - len(list(q)))
    e0, e1, e2, e3, e4 = cs[:5]
    A, B, C, D, E = e4, e3, e2, e1, e0
    I = 12*A*E - 3*B*D + C^2
    J = 72*A*C*E + 9*B*C*D - 27*A*D^2 - 27*E*B^2 - 2*C^3
    return EllipticCurve([-27*I, -27*J])

def sqf_kernel(R, K):
    Pk = PolynomialRing(K, 'v')
    num = Pk([K(c) for c in list(R.numerator())]); den = Pk([K(c) for c in list(R.denominator())])
    f = (num*den).factor()
    q = f.unit() * prod(p for p, e in f if e % 2)
    return q

for name, hi in [("B3", 1), ("B1", 2), ("B1", 3), ("B1", 4)]:
    t0 = time.time()
    Tr, Nm = trnm(Ts[name], hi)
    cs = const_times_square(Nm)
    print(f"psi{hi} via reflection {name}: Nm = c*M^2 with c = {cs[0]}", flush=True)
    c, M = cs
    K = QQ if c == 1 else NumberField(polygen(QQ)^2 - c, 'r')
    rc = K(1) if c == 1 else K.gen()
    Fk = FunctionField(K, 'v'); v = Fk.gen()
    Trk = Fk(Tr.numerator().change_ring(K)(v)) / Fk(Tr.denominator().change_ring(K)(v))
    Mk = Fk(M.numerator().change_ring(K)(v)) / Fk(M.denominator().change_ring(K)(v))
    for sgn in (1, -1):
        q = sqf_kernel(Trk + 2*sgn*rc*Mk, K)
        if q.degree() not in (3, 4):
            print(f"   sign {sgn}: degree {q.degree()} (not genus 1)", flush=True); continue
        E = jacobian_of_quartic(q)
        if K is QQ:
            E = E.minimal_model()
            print(f"   sign {sgn}: E over Q, conductor {E.conductor()}, j = {E.j_invariant()}", flush=True)
        else:
            E = E.global_minimal_model() if E.has_global_minimal_model() else E
            print(f"   sign {sgn}: E over {K}, j = {E.j_invariant()}", flush=True)
            print(f"      j in Q? {E.j_invariant() in QQ};  conductor norm {E.conductor().norm().factor()}", flush=True)
            try:
                lo, hi_ = E.rank_bounds(lim1=5, lim3=50, limtriv=50, maxprob=20, limbigprime=30)
                print(f"      rank bounds over K (Simon 2-descent): [{lo}, {hi_}]", flush=True)
                print(f"      points found: {E.gens(lim1=5, lim3=50, limtriv=50)}", flush=True)
            except Exception as ex:
                print("      rank computation failed:", ex, flush=True)
    print(f"   ({time.time() - t0:.0f} s)", flush=True)
