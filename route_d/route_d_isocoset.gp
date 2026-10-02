/* Missing generators of E_{a,b} from the coset search on the 2-isogenous curve E' = E/<(0,0)>.

   E: Y^2 = X(X^2 + A X + B), A = -(e2 + e3), B = e2 e3 = (a b s)^2, s = a^2 + b^2.
   E': Y^2 = X(X^2 - 2A X + A^2 - 4B) = X (X + s(a - b)^2) (X + s(a + b)^2): also full rational
   2-torsion, because B is a square.  phi: E -> E', (x, y) -> (y^2/x^2, y(B - x^2)/x^2); the dual
   sends (X, Y) on E' to (Y^2/(4X^2), Y(A^2 - 4B - X^2)/(8X^2)) on E and doubles canonical heights,
   so a missing generator G2 of E comes from a point of E' of half the height, and the 2-coverings
   of E' (route_d_cosetsearch.gp's covpts) quarter that again.
   The coset searched is Sel2(E') minus the span of the Kummer images of phi(G1) and E'(Q)_tors
   (Sel2(E') from route_d_selmer_lines.py --isogenous).

   Tested 2026-10-02: on 43:9 the second generator comes out in 0.7 s at height 1e4 (on E itself,
   none of the 8 coset classes has a point up to 1e6); on 49:5 and 79:11 nothing up to 1e5.

   isocoset(a, b, SEL1, H) -> [status, generators of E(Q) (saturated at primes <= 1000)].
   Run driver: params file with LINES, FG_OUT, ISO_H and the SEL1_a_b lists, then this file and
     isocoset_run(): each found line is written to FG_OUT as a KNOWNGENS entry.               */
\r route_d_cosetsearch.gp
\r route_d_findgens.gp

isocoset(a, b, SEL1, H) =
{
  my(s = a^2 + b^2, e = [0, a^2*s, b^2*s], E = ellinit([0, -(e[2] + e[3]), 0, e[2]*e[3], 0]));
  my(A = -(e[2] + e[3]), B = e[2]*e[3], f = [0, -s*(a - b)^2, -s*(a + b)^2], E1 = ellinit([0, -(f[2] + f[3]), 0, f[2]*f[3], 0]));
  if(E1[1..5] != [0, -2*A, 0, A^2 - 4*B, 0], error("isocoset: E' model"));
  my(rk = ellrank(E, 4), e0 = 4);
  while(rk[1] != rk[2] && e0 < 8, e0++; rk = ellrank(E, e0));
  if(rk[1] != rk[2], return(["rank not proven", []]));
  my(G = [P | P <- rk[4], P != [0]]);
  if(#G >= rk[1], return(["already complete", ellsaturation(E, G, 1000)]));
  my(phi = P -> if(P == [0] || P[1] == 0, [0], [P[2]^2/P[1]^2, P[2]*(B - P[1]^2)/P[1]^2]));
  my(back = Q -> if(Q == [0] || Q[1] == 0, [0], [Q[2]^2/(4*Q[1]^2), Q[2]*(A^2 - 4*B - Q[1]^2)/(8*Q[1]^2)]));
  my(known = concat(apply(phi, G), elltors(E1)[3]));
  foreach(known, P, if(P != [0] && !ellisoncurve(E1, P), error("isocoset: phi")));
  my(imgs = apply(P -> kum(E1, P, f), [P | P <- known, P != [0]]));
  my(PR = Set(concat(apply(v -> concat(primesof(v[1]), primesof(v[2])), concat(imgs, SEL1)))));
  my(Mk = matconcat(apply(v -> concat(sqvec(v[1], PR), sqvec(v[2], PR))~, imgs)));
  my(coset = [c | c <- SEL1, type(matsolvemod(Mk, 2, concat(sqvec(c[1], PR), sqvec(c[2], PR))~)) == "t_INT"]);
  my(tried = 0);
  foreach(coset, c, tried++;
    foreach(covpts(f[2], f[3], c[1], c[2], H), Q,
      my(P = back(Q)); if(P == [0] || !ellisoncurve(E, P), next);
      if(#G < rk[1] && indep(E, concat(G, [P])), G = concat(G, [P])));
    if(#G >= rk[1], return([Str("found on E' at class ", c, " (", tried, " of ", #coset, ")"), ellsaturation(E, G, 1000)])));
  [Str("not found on E' (", #coset, " classes, H = ", H, ")"), G];
}

isocoset_run() =
{
  foreach(LINES, L, my(t = getabstime(), sel = eval(Str("SEL1_", L[1], "_", L[2])));
    my(r = iferr(isocoset(L[1], L[2], sel, ISO_H), err, [Str("error ", err), []]));
    print(L[1], ":", L[2], "  ", r[1], "  #points ", #r[2], "  (", (getabstime() - t) \ 1000, " s)");
    if(#r[2] >= 2 && r[1] != "already complete", write(FG_OUT, gensentry(L[1], L[2], r[2]))));
}
