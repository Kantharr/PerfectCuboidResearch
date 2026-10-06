/* Rank-0 route for a clean fibre, needing nothing about E_{a,b} (no generators, no rank).

   Theorem weilres: on the fibre (al, be, ga) of the line a:b, with K = Q(sqrt sigma),
       Prym(D_h) ~ Res_{K/Q} E3^(al ga delta3)   for h = (a^2 - x)/(al ga),
       Prym(D_h) ~ Res_{K/Q} E4^(be ga delta4)   for h = (b^2 - x)/(be ga).
   The quotient D_h -> D_h / rho~ is defined over K, has genus one and Jacobian the twist A+.
   D_h has a rational point (the one over the branch point O), so D_h / rho~ = A+ over K.
   If A+(K) has rank 0, every rational point of D_h, hence every cuboid point on the fibre,
   lies over the finite group A+(K)_tors: at most 2 |A+(K)_tors| points to check.

   This file: the two twists of a fibre as curves over K, with root number, conductor norm and
   torsion.  Rank 0 itself needs L(A+/K, 1) != 0 (route_d_weilres_lvalue.gp; modularity over
   real quadratic K by Freitas-Le Hung-Siksek) or a 2-descent bound of 0 over K (Sage, Simon).

   wrtwists(a, b, al, be, ga) -> [[nf, E3t], [nf, E4t]]   (ellinit over nf = nfinit(y^2 - sigma))
   wrinfo(a, b, al, be, ga)   -> prints root numbers, conductor norms and torsion of both.

   2026-10-05, the 24 clean Selmer fibres of the 10 unresolved lines (11:3 (65,2,1) reproduces
   the paper's conductor norm 2^7 3^4 5 11^4 13): all 48 twists have full 2-torsion over K.
   Root number -1 for all four twists on 71:67 and 79:59, so the route cannot settle them;
   every fibre of the other 8 lines has a twist with root number +1. Conductor norms 10^9 to
   10^27, so L-values cost 25x (81:1) to far beyond the 11:3 sum. */

wrtwists(a, b, al, be, ga) =
{
  my(s = a^2 + b^2, nf = nfinit('y^2 - s), r = Mod('y, 'y^2 - s));
  my(d3 = al*ga*(-2*a*(a + r)), d4 = be*ga*(2*b*(r - b)));
  /* E^(d): Y^2 = X(X^2 + d lam X + d^2 mu) */
  my(E3 = ellinit([0, d3*(-4*b^2*s), 0, d3^2*(-4*a^2*b^2*s^2), 0], nf));
  my(E4 = ellinit([0, d4*(-4*a^2*s), 0, d4^2*(-4*a^2*b^2*s^2), 0], nf));
  [[nf, E3], [nf, E4]];
}

wrinfo(a, b, al, be, ga) =
{
  my(T = wrtwists(a, b, al, be, ga));
  for(i = 1, 2, my(E = T[i][2], gr = ellglobalred(E), N = idealnorm(T[i][1], gr[1]));
    print(a, ":", b, " (", al, ",", be, ",", ga, ")  E", i + 2, "-twist  rootno ", ellrootno(E),
          "  N(cond) ", N, " = ", factor(N)[, 1]~, "  torsion ", elltors(E)[2]));
}
