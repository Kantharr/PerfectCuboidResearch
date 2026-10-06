/* Finite check of a fibre through a rank-0 quotient of D_h (Theorem weilres), needing nothing about
   E_{a,b}.

   Fibre (a, b, al, be, ga), sigma = a^2 + b^2 = al be s^2, K = Q(sqrt sigma).
     E': al be ga^2 y^2 = x (x - a^2)(x - b^2),   F = ab (sigma - x)(ab x - al be ga s y),
     D_h: W^2 = h F,  h = (a^2 - x)/(al ga) (which = 3) or (b^2 - x)/(be ga) (which = 4).
   A cuboid point on the fibre gives a rational point of D_h: there x = z^2/t^2 and
   (a^2 - x)/(al ga), (b^2 - x)/(be ga), F are all squares.
   rho(P) = B1 - P with B1 = (sigma, -abs/ga); u = slope of the line through -B1 and P, whose third
   point is rho(P).  With f = hF, T = f(P) + f(rho P) and N = f(P) f(rho P) in Q(u), N = sigma M^2,
   N0 = sqrt(N) in K(u), and D_h / rho~ is  V^2 = T + 2 N0 = q(u) g(u)^2,  q a cubic over K.
   A rational point P of D_h maps to (u(P), V/g) with V = W(P) + W(rho~ P), a K-point of V^2 = q(u).
   If that curve has rank 0 over K (route_d_kdescent.gp on its Weierstrass model), its K-points
   are its torsion, so u(P) is the u-coordinate of a torsion point, or u = oo, or one of the
   finitely many u where g, a denominator or a leading coefficient vanishes or has a pole.
   For each rational candidate u the points P of E'(Q) on that line are listed and tested.

   wrfibre(a, b, al, be, ga, which) -> [rank bound, isogeny bounds, torsion structure, #torsion,
                                        candidate u, rational points of D_h, cuboid points]
   The quotient's j-invariant is checked against E3 / E4 (Theorem weilres, independently).

   2026-10-05: 81:19 (2,3461,1) and (3461,2,1), psi3: quotient Sel2 bound 0 (class group of
   Q(sqrt 6922) certified), torsion (Z/2)^2; candidate u = 81/19, 1539/6922, 50282605/21305916
   and oo; the rational points of D_h over them are O, B1, -B1, B2 = (0,0), B3 and (a^2, 0), all
   with F = 0 or h = 0.  No cuboid point: the line 81:19 is resolved.                         */
\r route_d_kdescent.gp

ratroots(P) = { my(L = List()); if(type(P) != "t_POL", return([]));
  foreach(factor(P)[, 1], f, if(poldegree(f) == 1, listput(L, -polcoeff(f, 0)/polcoeff(f, 1)))); Vec(L); }
issq(q) = q == 0 || (q > 0 && issquare(numerator(q)) && issquare(denominator(q)));

wrfibre(a, b, al, be, ga, which) =
{
  my(sg = a^2 + b^2, s2 = sg / (al*be), s);
  if(!issquare(s2, &s), error("sigma != al be s^2"));
  my(c = al*be*ga^2, cub = 'x*('x - a^2)*('x - b^2), B1 = [sg, -a*b*s/ga]);
  if(c*B1[2]^2 != subst(cub, 'x, B1[1]), error("B1 not on E'"));
  my(h = if(which == 3, (a^2 - 'x)/(al*ga), (b^2 - 'x)/(be*ga)));
  my(Fxy = (X, Y) -> a*b*(sg - X)*(a*b*X - al*be*ga*s*Y));
  /* the line through -B1 = (sigma, abs/ga) with slope u; Q(x) = its other two intersections */
  my(yl = 'u*('x - sg) + a*b*s/ga, dv = divrem(c*yl^2 - cub, 'x - sg, 'x), Qx = dv[1]);
  if(dv[2] != 0, error("x = sigma is not on the line")); if(poldegree(Qx, 'x) != 2, error("Q not quadratic"));
  my(Fm = Mod(h * Fxy('x, yl), Qx), T = trace(Fm), N = norm(Fm));
  /* N = sigma * M^2 with M in Q(u) */
  my(R = N / sg, nn = numerator(R), dd = denominator(R), fn = factor(nn), fd = factor(dd), M = 1);
  for(i = 1, #fn~, if(fn[i, 2] % 2, error("N/sigma: odd factor ", fn[i, 1])); M *= fn[i, 1]^(fn[i, 2]/2));
  for(i = 1, #fd~, if(fd[i, 2] % 2, error("N/sigma: odd factor ", fd[i, 1])); M /= fd[i, 1]^(fd[i, 2]/2));
  my(k = simplify(R / M^2), kr); if(!issq(k), error("N/sigma: constant ", k, " not a square"));
  issquare(k, &kr); M *= kr;
  /* switch u -> x for the work over K (x has priority over the nf variable y) */
  my(nf = nfinit('y^2 - sg), r = Mod('y, 'y^2 - sg), Tx = subst(T, 'u, 'x), Mx = subst(M, 'u, 'x));
  my(fp = Tx + 2*r*Mx, P = numerator(fp) * denominator(fp));
  my(fa = nffactor(nf, P), q = Mod(1, 'y^2 - sg) * pollead(P), sqf = List());
  for(i = 1, #fa~, if(fa[i, 2] % 2, q *= fa[i, 1], listput(sqf, fa[i, 1])));
  if(poldegree(q, 'x) != 3, error("q has degree ", poldegree(q, 'x)));
  my(C = pollead(q), rts = nfroots(nf, q / C));
  if(#rts != 3, error("q does not split over K"));
  rts = apply(z -> Mod(lift(z), 'y^2 - sg), rts);
  /* Weierstrass model: X = C u, Y = C V:  Y^2 = (X - C e1)(X - C e2)(X - C e3) */
  my(e = apply(z -> C*z, rts), kd = kdescent(sg, e));
  my(Ew = ellinit([0, -(e[1] + e[2] + e[3]), 0, e[1]*e[2] + e[1]*e[3] + e[2]*e[3], -e[1]*e[2]*e[3]], nf));
  /* independent check of Theorem weilres on this fibre: same j as the twist E3 / E4 */
  my(ew = wre(a, b, al, be, ga, which), Et = ellinit([0, -(ew[2] + ew[3]), 0, ew[2]*ew[3], 0], nf));
  if(Ew.j != Et.j, error("quotient j != j(E", which, ")"));
  my(tor = elltors(Ew), pts = List([[0]]));
  /* all torsion points from the generators */
  my(g = tor[3], o = tor[2]);
  forvec(v = vector(#g, i, [0, o[i] - 1]), my(Pt = [0]); for(i = 1, #g, Pt = elladd(Ew, Pt, ellmul(Ew, g[i], v[i]))); listput(pts, Pt));
  pts = Set(Vec(pts));
  /* candidate u: rational u-coordinates of torsion points, and the exceptional u */
  my(cand = List());
  foreach(pts, Pt, if(Pt != [0], my(uu = lift(Pt[1] / C)); if(poldegree(uu, 'y) <= 0, listput(cand, simplify(uu)))));
  my(exc = concat([numerator(T), denominator(T), numerator(M), denominator(M), pollead(Qx, 'x), polcoeff(Qx, 0, 'x)], []));
  foreach(exc, f, foreach(ratroots(f), z, listput(cand, z)));
  foreach(sqf, f, if(poldegree(f, 'x) == 1, my(z = lift(-polcoeff(f, 0)/polcoeff(f, 1))); if(poldegree(z, 'y) <= 0, listput(cand, simplify(z)))));
  cand = Set(Vec(cand));
  /* rational points of E' on each candidate line, plus u = oo (P = O or B1) */
  my(Dh = List(), cub_ok = (X, Y) -> c*Y^2 == subst(cub, 'x, X));
  listput(Dh, ["O", "branch point"]);
  my(hB1 = subst(h, 'x, B1[1]) * Fxy(B1[1], B1[2]));
  listput(Dh, [B1, if(issq(hB1), "on D_h", "not on D_h")]);
  foreach(cand, uu, my(Qu = subst(Qx, 'u, uu));
    if(poldegree(Qu, 'x) < 2, next);
    foreach(ratroots(Qu), X, my(Y = subst(subst(yl, 'u, uu), 'x, X));
      if(!cub_ok(X, Y), error("point off E'"));
      my(hf = subst(h, 'x, X) * Fxy(X, Y));
      if(issq(hf), listput(Dh, [[X, Y], uu]))));
  /* cuboid test: x, (a^2 - x)/(al ga), (b^2 - x)/(be ga), F all squares, F != 0 */
  my(cub_pts = List());
  foreach(Dh, D, if(type(D[1]) != "t_VEC", next); my(X = D[1][1], Y = D[1][2], Fv = Fxy(X, Y));
    if(Fv != 0 && issq(X) && issq((a^2 - X)/(al*ga)) && issq((b^2 - X)/(be*ga)) && issq(Fv), listput(cub_pts, D[1])));
  [kd[1], kd[2], tor[2], #pts, cand, Vec(Dh), Vec(cub_pts)];
}

wrfibre_print(a, b, al, be, ga, which) =
{
  my(t = getabstime(), r = wrfibre(a, b, al, be, ga, which));
  print(a, ":", b, " (", al, ",", be, ",", ga, ") psi", which, ":  quotient Sel2 bound ", r[1], "  isogeny ", r[2],
        "  torsion ", r[3], " (", r[4], " points)");
  print("   candidate u (", #r[5], "): ", r[5]);
  print("   rational points of D_h over them: ", r[6]);
  print("   cuboid points: ", r[7], "   (", getabstime() - t, " ms)");
}
