/* Analytic rank of E_{a,b}: Y^2 = X(X - a^2 s)(X - b^2 s), s = a^2 + b^2, for lines whose rank
   ellrank cannot prove.  If the root number is -1 and L'(E,1) != 0, then by Gross-Zagier and
   Kolyvagin E_{a,b} has rank exactly 1 (and Sha is finite), so Theorem 6.4 (rank-one lines)
   applies: only the two degenerate fibres of the line have rational points.
   Read a params file first defining  LINES = [[a, b], ...];
     gp -q params.gp route_d_analytic_rank.gp
   Output per line: "a:b  root_number  analytic_rank  leading_coefficient  milliseconds".
   (The stack default has to be on its own line: gp ignores the rest of a default(...) line.) */
default(parisize, 1000000000);
default(parisizemax, 8000000000);
{
  foreach(LINES, L, my(a = L[1], b = L[2], s = a^2 + b^2, t = getabstime());
    my(E = ellinit([0, -(a^2 + b^2)*s, 0, a^2*b^2*s^2, 0]), w = ellrootno(E), r = ellanalyticrank(E));
    print(a, ":", b, " ", w, " ", r[1], " ", r[2], " ", getabstime() - t));
}
quit
