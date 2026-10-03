/* BSD estimate of the size of the missing generator on each curve of the isogeny class of E_{a,b}.

   For a rank-2 line where only one generator G1 is known: ellanalyticrank gives L''(E,1)/2, and
   Reg_j = L''(E,1)/2 / ellbsd(E_j) on each isogenous curve E_j if Sha(E_j) is trivial (Sha[2] = 0
   is known from dim Sel2 = rank + 2; an odd Sha would make Reg_j smaller by a square). With G1_j
   the image of G1 on E_j, Reg_j <= h(G1_j) h(G2_j), so Reg_j / h(G1_j) bounds h(G2_j) from below.
   The image of G1 is often twice a point on E_j (the generator there has a quarter of its height),
   so the realistic estimate is about 4 Reg_j / h(G1_j).

   Params: LINES = [[a, b], ...].  Prints, per line, [j, Reg_j, h(G1_j), Reg_j / h(G1_j)].
   Needs a large stack: run gp with -D parisizemax=8000000000 (ellanalyticrank).

   2026-10-02 on the 8 lines left after route_d_isoclass.gp: Reg(E) 2929 to 10978, and the missing
   generator has height about 160-370 on the best curve, against 35-65 for the 6 lines found. */

g2height(a, b) =
{
  my(s = a^2 + b^2, e = [0, a^2*s, b^2*s], E = ellinit([0, -(e[2] + e[3]), 0, e[2]*e[3], 0]));
  my(ar = ellanalyticrank(E), G1 = ellrank(E, 6)[4][1], C = ellisomat(E)[1], out = []);
  for(j = 1, #C, my(Ej = ellinit(C[j][1]), Rj = ar[2] / ellbsd(Ej), h1 = ellheight(Ej, ellisogenyapply(C[j][2], G1)));
    out = concat(out, [[j, round(Rj), round(h1*10)/10, round(Rj/h1*10)/10]]));
  [ar[1], ar[2] / ellbsd(E), out];
}

g2height_run() =
{
  default(parisize, 1000000000);
  foreach(LINES, L, my(t = getabstime(), r = g2height(L[1], L[2]));
    print(L[1], ":", L[2], "  an.rank ", r[1], "  Reg_E ~ ", round(r[2]), "  [j, Reg_j, h(G1_j), Reg_j/h(G1_j)] ", r[3], "  (", (getabstime() - t) \ 1000, " s)"));
}
