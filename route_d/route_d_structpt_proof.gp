\r route_d_structpt_sym.gp
default(parisize, 2000000000);
{closed(a, b) = my(S = a^2 + b^2);
  [[[0, -4*a^2*b^2, 0, a^2*b^2*S^2, 0], [b^2*S, b^2*S*(a^2 - b^2)]],
   [[0, 0, 0, a^2*b^2*S^2, 0], [b^2*S, b^2*S^2]],
   [[0, 2*a*b*S*(a^2 + a*b + b^2), 0, a^4*b^4*S^2, 0], [a^4*S, a^4*S^2*(a + b)]],
   [[0, -2*a*b*S*(a^2 - a*b + b^2), 0, a^4*b^4*S^2, 0], [a^4*S, a^4*S^2*(a - b)]]];}
ratroots(P) = my(fa = factor(P)[,1], R = List()); for(i = 1, #fa, if(poldegree(fa[i]) == 1, listput(R, -polcoeff(fa[i], 0)/polcoeff(fa[i], 1)))); Vec(R);
c46(c) = my(b2 = 4*c[2], b4 = 2*c[4], b6 = 4*c[5]); [b2^2 - 24*b4, -b2^3 + 36*b2*b4 - 216*b6];
{C = closed(1, 't); names = ["E_A (psi1)", "E_B (psi1)", "E_C (psi2)", "E_D (psi2)"];
 for(k = 1, 4, my(sc = symcurve((k + 1)\2, 2 - (k % 2)), c = C[k][1], P = C[k][2]);
   my(u = c46(c), v = c46(sc[1]), jc = u[1]^3/(u[1]^3 - u[2]^2), jv = v[1]^3/(v[1]^3 - v[2]^2));
   my(tw = if(u[1] != 0 && u[2] != 0, (u[2]*v[1])/(v[2]*u[1]), if(u[2] == 0, "j=1728", "j=0")));
   my(sqok = if(type(tw) == "t_STR", "n/a", issquare(tw)));
   if(sqok == "n/a", /* j = 1728: y^2 = x^3 + A x, isomorphic iff A/A' is a 4th power; compare c4 ratio as 4th power */
      sqok = ispower(u[1]/v[1], 4));
   print(names[k], ":  same j as constructed factor: ", jc == jv, ";  Q(t)-isomorphic (twist class trivial): ", sqok);
   my(E = [0, c[2], 0, c[4], c[5]], y2 = P[1]^3 + c[2]*P[1]^2 + c[4]*P[1] + c[5]);
   print("   P on curve identically: ", y2 == P[2]^2);
   my(f = divpols([0, c[2], 0, c[4], c[5]], 12), bad = Set());
   for(n = 3, 12, my(g = numerator(subst(f[n+1], 'x, P[1]))); if(g == 0, error("generic torsion")); bad = setunion(bad, Set(ratroots(g))));
   print("   rational t with nP = O for some 3<=n<=12: ", bad, ";  y(P) = 0 at t in ", ratroots(numerator(P[2])), ";  disc zero at t in ", ratroots(numerator(ellinit(E).disc))))}
/* E_{a,b}: Y^2 = X(X - a^2 s)(X - b^2 s) with (a^2 b^2, a^3 b^3), a = 1, b = t */
ratroots2(P) = my(fa = factor(P)[,1], R = List()); for(i = 1, #fa, if(poldegree(fa[i]) == 1, listput(R, -polcoeff(fa[i], 0)/polcoeff(fa[i], 1)))); Vec(R);
{my(s = 1 + 't^2, c = [0, -s^2, 0, 't^2*s^2, 0], P = ['t^2, 't^3], bad = Set(), f = divpols(c, 12));
 print("on curve: ", P[2]^2 == P[1]^3 + c[2]*P[1]^2 + c[4]*P[1]);
 for(n = 3, 12, my(g = numerator(subst(f[n+1], 'x, P[1]))); if(g == 0, error("generic torsion")); bad = setunion(bad, Set(ratroots2(g))));
 print("E_{1,t}: rational t with nP=O (3<=n<=12): ", bad, "  disc zero at ", ratroots2(numerator(ellinit(c).disc)))}

quit
