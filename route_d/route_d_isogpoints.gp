/* Independent points on E(Q) via its 2-isogenous curves, for when ellrank proves the rank but lists
   fewer points than the rank (seen on the line 43:9).  For each rational 2-torsion point T:
     phi: E -> E2 = E/<T>,  points Q on E2 from ellrank,
     psi: E2 -> E3 = E2/<phi(T')>  (T' another 2-torsion point; psi is dual to phi, so E3 ~= E),
   and psi(Q) is carried to E through the common reduced minimal model.
   isogpts(E, P, rk): E = ellinit over Q, P = known points, rk = proven rank.  Returns rk independent
   points (the known ones first, then new ones), or P unchanged if not enough were found.        */

twotors(E) =
{
  my(f = factor(elldivpol(E, 2))[, 1], T = List());
  for(i = 1, #f, if(poldegree(f[i]) == 1, my(x = -polcoeff(f[i], 0)/polcoeff(f[i], 1));
    listput(T, [x, -(E.a1*x + E.a3)/2])));
  Vec(T);
}
indep(E, P) = #P == 0 || matrank(ellheightmatrix(E, P) + 0.) == #P;

isogpts(E, P, rk, eff = 8) =
{
  my(T = twotors(E), vE, mE = ellminimalmodel(E, &vE), G = P);
  if(#G >= rk, return(G));
  for(i = 1, #T,
    my(I = ellisogeny(E, T[i]), E2 = ellinit(I[1]), r2 = ellrank(E2, eff), j = if(i == 1, 2, 1));
    if(#T < 2, break);
    my(K2 = ellisogenyapply(I[2], T[j]), J = ellisogeny(E2, K2), E3 = ellinit(J[1]), v3, m3 = ellminimalmodel(E3, &v3));
    if(m3[1..5] != mE[1..5], error("isogpts: dual isogeny does not return to E"));
    foreach(r2[4], Q, my(R = ellchangepointinv(ellchangepoint(ellisogenyapply(J[2], Q), v3), vE));
      if(!ellisoncurve(E, R), error("isogpts: mapped point not on E"));
      if(R != [0] && indep(E, concat(G, [R])), G = concat(G, [R])));
    if(#G >= rk, break));
  G;
}
