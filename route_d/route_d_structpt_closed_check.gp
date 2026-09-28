\r route_d_structpt_sym.gp
default(parisize, 2000000000);
{closed(a, b) = my(S = a^2 + b^2);
  [[[0, -4*a^2*b^2, 0, a^2*b^2*S^2, 0], [b^2*S, b^2*S*(a^2 - b^2)]],
   [[0, 0, 0, a^2*b^2*S^2, 0], [b^2*S, b^2*S^2]],
   [[0, 2*a*b*S*(a^2 + a*b + b^2), 0, a^4*b^4*S^2, 0], [a^4*S, a^4*S^2*(a + b)]],
   [[0, -2*a*b*S*(a^2 - a*b + b^2), 0, a^4*b^4*S^2, 0], [a^4*S, a^4*S^2*(a - b)]]];}
{SC = vector(4, k, symcurve((k + 1)\2, 2 - (k % 2)));
 lines = [[11,3],[19,7],[23,11],[27,1],[39,23],[31,3],[45,37],[33,19],[43,1],[5,3],[101,7]];
 foreach(lines, ab, my([a, b] = ab, C = closed(a, b), res = "");
   for(k = 1, 4, my(E = ellinit(C[k][1]), P = C[k][2], found = 0);
     if(!ellisoncurve(E, P), res = concat(res, Str(" k", k, ":P-not-on-curve")); next);
     for(m = 1, 4, my(F = ellinit(substvec(SC[m][1], ['t], [b/a]))); if(ellminimalmodel(E)[1..5] == ellminimalmodel(F)[1..5], found = m));
     res = concat(res, Str(" k", k, "=model", found, if(ellheight(E, P) > 0, "(P non-tors)", "(P TORSION)"))));
   print([a, b], res))}
quit
