\r route_d_quotients.gp
default(parisize, 200000000);
{forprime(p = 17, 400, if(p == 5 || p == 11 || p == 13, next);
  my(t0 = getabstime(), v = vector(2, hi, iferr(dcount(11, 3, 65, 2, 1, 1, hi, p), E, 0)));
  if(v[1] == 0 || v[2] == 0, print(p, " skipped (degenerate)"); next);
  my(P = vector(2, i, lpoly(v[i][1], v[i][2], p)));
  write("quot_11_3_65_2_1.txt", [p, v[1][3], v[1][1], v[1][2], v[2][1], v[2][2]]);
  print(p, "  aE'=", v[1][3], "  psi1 ", factor(P[1])[, 1]~, " RH ", rh(P[1], p), "  psi2 ", factor(P[2])[, 1]~, " RH ", rh(P[2], p), "  (", getabstime() - t0, " ms)"))}
quit
