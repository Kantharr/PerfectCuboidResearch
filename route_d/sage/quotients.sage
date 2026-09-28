# Plane models of the four genus-3 quotients D_h: W^2 = h*F of the cuboid cover over the
# Route D fiber (a,b,al,be,ga,s) = (11,3,65,2,1,1), and their numerical endomorphism rings.
# E': c2c3 y^2 = x(a^2-x)(b^2-x);  F = ab(S2-x)(ab x - kc y).  Solving W^2 = h F for y and
# substituting gives  (h ab (S2-x) ab x - W^2)^2 = h^2 ab^2 (S2-x)^2 kc^2 g(x)/(c2 c3).
import sys, time
from sage.schemes.riemann_surfaces.riemann_surface import RiemannSurface
a, b, al, be, ga, s = 11, 3, 65, 2, 1, 1
c2, c3, S2, kc, ab = al*ga, be*ga, a^2 + b^2, al*be*ga*s, a*b
R.<x, W> = QQ[]
g = x*(a^2 - x)*(b^2 - x)
H = {1: R(1), 2: x, 3: (a^2 - x)/c2, 4: (b^2 - x)/c3}
which = [int(t) for t in sys.argv[1].split(",")] if len(sys.argv) > 1 else [1, 2, 3, 4]
prec = int(sys.argv[2]) if len(sys.argv) > 2 else 100
for hi in which:
    h = H[hi]
    f = (h*ab*(S2 - x)*ab*x - W^2)^2 - h^2*ab^2*(S2 - x)^2*kc^2*g/(c2*c3)
    f = f * lcm([c.denominator() for c in f.coefficients()])
    f = f / gcd([ZZ(c) for c in f.coefficients()])
    C = Curve(f)
    print(f"psi{hi}: h = {h};  plane model degree {f.degree()}, geometric genus {C.genus()}", flush=True)
    t0 = time.time()
    S = RiemannSurface(f, prec=prec)
    print("  differentials:", S.cohomology_basis(), flush=True)
    PM = S.period_matrix()
    B = S.endomorphism_basis()
    print(f"  rank of End(J_Qbar) over Z: {len(B)}   ({time.time() - t0:.0f} s)", flush=True)
    for M in B:
        T = S.tangent_representation_numerical([M])[0]
        print("   endo char poly on H1:", M.charpoly().factor(), flush=True)
        print("   tangent rep (rounded):", [[CC(z).real().round() if abs(CC(z).imag()) < 1e-20 and abs(CC(z).real() - CC(z).real().round()) < 1e-20 else CC(z) for z in row] for row in T.rows()], flush=True)
    save((f, PM, B), f"sage/quot_psi{hi}.sobj")
