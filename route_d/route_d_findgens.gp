/* Find missing generators of E_{a,b}(Q) when ellrank proves the rank but lists too few points.

   E = E_{a,b}: Y^2 = X(X - a^2 s)(X - b^2 s), s = a^2 + b^2.  Stages, cheapest first, stopping as
   soon as there are rank-many independent points:
     1. rational points on the 2-covers of E (ell2cover; quartics y^2 = q(x) with an explicit map
        to E), height bound H1;
     2. the same on the 2-covers of the three 2-isogenous curves E' = E/<T>, mapped back to E by
        the dual isogeny (points there are smaller still);
     3. ellrank at effort EFF on the isogenous curves (route_d_isogpoints.gp);
     4. stage 1 again with the larger bound H2.
   With rank r proven and Sha[2] trivial, every locally solvable 2-cover has points, so the
   missing class does sit on one of the covers searched; the question is only how high.

   findgens(a, b) returns [status, rank, points] with points saturated at all primes <= 1000.
   gensentry(a, b) returns the KNOWNGENS entry [minimal model a-invariants, points on it].     */
\r route_d_isogpoints.gp

/* defaults, only where not already set (a params file read first must win; overwriting them here
   made the 2026-09-29 passes 2 and 3 run with H2 = 1e7, about 4 h per line).  Stage 4 at 1e7
   found 3 of the 8 generators found so far but costs hours per line, so the default is 1e6.     */
if(type(FG_H1) == "t_POL", FG_H1 = 10^6);
if(type(FG_H2) == "t_POL", FG_H2 = 10^6);
if(type(FG_EFF) == "t_POL", FG_EFF = 12);

coverpts(E, C, H, G, rk, tomap) =
{
  for(i = 1, #C, if(#G >= rk, break);
    my(q = C[i][1], mp = C[i][2], pts = iferr(hyperellratpoints(q, H), err, []));
    foreach(pts, pt, if(pt[2] == 0, next);
      my(P = [subst(subst(mp[1], 'x, pt[1]), 'y, pt[2]), subst(subst(mp[2], 'x, pt[1]), 'y, pt[2])]);
      P = tomap(P);
      if(P == [0] || !ellisoncurve(E, P), next);
      if(indep(E, concat(G, [P])), G = concat(G, [P]); if(#G >= rk, break))));
  G;
}

findgens(a, b) =
{
  my(s = a^2 + b^2, E = ellinit([0, -(a^2 + b^2)*s, 0, a^2*b^2*s^2, 0]), rk = ellrank(E, 4), e = 4);
  while(rk[1] != rk[2] && e < 8, e++; rk = ellrank(E, e));
  if(rk[1] != rk[2], return(["rank not proven", rk[1..3], []]));
  my(r = rk[1], G = [P | P <- rk[4], P != [0]], id = P -> P, stage = 0);
  /* stage 1 */
  if(#G < r, stage = 1; G = coverpts(E, ell2cover(E), FG_H1, G, r, id));
  /* stage 2: covers of the isogenous curves */
  if(#G < r,
    stage = 2;
    my(T = twotors(E), vE, mE = ellminimalmodel(E, &vE));
    for(i = 1, #T, if(#G >= r, break);
      my(I = ellisogeny(E, T[i]), E2 = ellinit(I[1]), j = if(i == 1, 2, 1));
      my(J = ellisogeny(E2, ellisogenyapply(I[2], T[j])), E3 = ellinit(J[1]), v3, m3 = ellminimalmodel(E3, &v3));
      if(m3[1..5] != mE[1..5], error("dual isogeny does not return to E"));
      my(back = P -> ellchangepointinv(ellchangepoint(ellisogenyapply(J[2], P), v3), vE));
      G = coverpts(E, ell2cover(E2), FG_H1, G, r, back)));
  /* stage 3 */
  if(#G < r, stage = 3; G = isogpts(E, G, r, FG_EFF));
  /* stage 4 */
  if(#G < r, stage = 4; G = coverpts(E, ell2cover(E), FG_H2, G, r, id));
  if(#G < r, return(["not found", rk[1..3], G]));
  G = ellsaturation(E, G, 1000);
  [Str("found at stage ", stage), rk[1..3], G];
}

gensentry(a, b, G) =
{
  my(s = a^2 + b^2, E = ellinit([0, -(a^2 + b^2)*s, 0, a^2*b^2*s^2, 0]), v, m = ellminimalmodel(E, &v));
  [m[1..5], apply(P -> ellchangepoint(P, v), G)];
}
