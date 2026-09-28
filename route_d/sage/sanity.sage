print(version())
E = EllipticCurve([0,-1,1,-10,-20])
print("11a1 conductor", E.conductor(), "rank", E.rank())
print(factor(2^64+1))
R.<x,y> = QQ[]
print("genus of y^3+x^4-1:", Curve(y^3+x^4-1).genus())
from sage.schemes.riemann_surfaces.riemann_surface import RiemannSurface
S = RiemannSurface(y^2 - (x^5 - x + 1), prec=60)
print("genus-2 period matrix shape", S.period_matrix().dimensions())
