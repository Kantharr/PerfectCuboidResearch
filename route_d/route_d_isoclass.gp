/* Missing generators of E_{a,b} from the other curves in its isogeny class.

   E_{a,b}: Y^2 = X(X - a^2 s)(X - b^2 s), s = a^2 + b^2, has an isogeny class of 6 curves (degrees
   1, 2, 4, 4, 2, 2 from E).  Regulators across the class differ by powers of 2, and the BSD ratio
   predicts which curve has the smallest one: Reg_j / Reg_1 = ellbsd(E_1) / ellbsd(E_j) when the
   Sha orders agree.  On a curve with a 4x smaller regulator the missing generator has about a quarter
   of the canonical height, so ellrank's 2-cover search finds it where the search on E cannot.
   A point found on E_j is mapped back to E by the dual isogeny g_j from ellisomat, checked, and the
   generators are saturated at primes <= 1000.

   Tested 2026-10-02 on the 10 lines with known generators (tonight_0930/knowngens.gp): the minimal
   regulator sits on E' (j = 2) or on a 4-isogenous curve (j = 3), and on one line ellrank on j = 3
   returns G2 (height 34.9 there, 131 on E) in 16 ms.

   isoclass(a, b, eff) -> [status, generators of E(Q)].
   Run driver: params file with LINES, FG_OUT, IC_EFF, then this file and isoclass_run(). */
\r route_d_findgens.gp

isoclass(a, b, eff) =
{
  my(s = a^2 + b^2, e = [0, a^2*s, b^2*s], E = ellinit([0, -(e[2] + e[3]), 0, e[2]*e[3], 0]));
  my(rk = ellrank(E, 4), e0 = 4);
  while(rk[1] != rk[2] && e0 < 8, e0++; rk = ellrank(E, e0));
  if(rk[1] != rk[2], return(["rank not proven", []]));
  my(G = [P | P <- rk[4], P != [0]]);
  if(#G >= rk[1], return(["already complete", ellsaturation(E, G, 1000)]));
  my(L = ellisomat(E)[1], c1 = ellbsd(E));
  my(ratio = vector(#L, j, c1 / ellbsd(ellinit(L[j][1]))));
  my(order = vecsort(vector(#L, j, j), (i, j) -> sign(ratio[i] - ratio[j])));
  my(log = List());
  foreach(order, j,
    my(Ej = ellinit(L[j][1]), f = L[j][2], g = L[j][3]);
    my(Gj = [P | P <- apply(P -> ellisogenyapply(f, P), G), P != [0]]);
    my(rj = ellrank(Ej, eff, Gj));
    listput(log, Str("j", j, " ratio ", ratio[j], " rank ", rj[1..2], " pts ", #rj[4]));
    foreach(rj[4], Q, if(Q == [0], next);
      my(P = ellisogenyapply(g, Q));
      if(P == [0], next);
      if(!ellisoncurve(E, P), error("isoclass: dual map off E on curve ", j));
      if(#G < rk[1] && indep(E, concat(G, [P])), G = concat(G, [P])));
    if(#G >= rk[1], return([Str("found on curve ", j, " (Reg ratio ", ratio[j], "); ", Vec(log)), ellsaturation(E, G, 1000)])));
  [Str("not found (eff ", eff, "); ", Vec(log)), G];
}

isoclass_run() =
{
  foreach(LINES, L, my(t = getabstime());
    my(r = iferr(isoclass(L[1], L[2], IC_EFF), err, [Str("error ", err), []]));
    print(L[1], ":", L[2], "  ", r[1], "  #points ", #r[2], "  (", (getabstime() - t) \ 1000, " s)");
    if(#r[2] >= 2 && r[1] != "already complete", write(FG_OUT, gensentry(L[1], L[2], r[2]))));
}
