/* Structural rational points on the Q-split Prym factors E_+-: V^2 = q(u), u = slope of the line
   through -T and P on E': y^2 = x(x-a^2)(x-b^2)/(c2c3).  q is a cubic here; Weierstrass model
   Y^2 = X^3 + q2 X^2 + L q1 X + L^2 q0 via X = L u, Y = L V (L = leading coefficient). */
\r route_d_prym_split.gp
cubic2ell(q) = my(L = polcoeff(q, 3), c = Vec(q)); if(poldegree(q) != 3, error("not cubic")); ellinit([0, c[2], 0, L*c[3], L^2*c[4]]);
uval(T, P) = if(P == [0], oo, if(P[1] == T[1], if(P[2] == -T[2], "tangent", oo), (P[2] + T[2]) / (P[1] - T[1])));
/* special rational points of E' */
specials(a, b, al, be, ga, s) =
{
  my(S2 = a^2 + b^2, kc = al*be*ga*s, x0 = a^2*b^2/S2, cc = al*be*ga^2);
  [["O", [0]], ["B1", [S2, -a*b*s/ga]], ["B2", [0, 0]], ["B3", [x0, a*b*x0/kc]],
   ["P*", [S2, a*b*s/ga]], ["-B3", [x0, -a*b*x0/kc]], ["(a^2,0)", [a^2, 0]], ["(b^2,0)", [b^2, 0]]];
}
tangentslope(a, b, cc, P) = my(x = P[1], y = P[2], dg = a^2*b^2 - 2*(a^2 + b^2)*x + 3*x^2); dg / (2*cc*y);
structpts(a, b, al, be, ga, s, which) =
{
  my(S2 = a^2 + b^2, cc = al*be*ga^2, x0 = a^2*b^2/S2, kc = al*be*ga*s);
  my(T = if(which == 1, [x0, a*b*x0/kc], [S2, -a*b*s/ga]), hi = which);   /* psi1 <-> r_B3, psi2 <-> r_B1 */
  my(Q = quotcurves(a, b, al, be, ga, s, T, hi), out = vector(2));
  for(e = 1, 2, my(q = Q[e][1], E = cubic2ell(q), L = polcoeff(q, 3), pts = List(), names = List());
    foreach(specials(a, b, al, be, ga, s), sp, my(u = uval(T, sp[2]));
      if(u == "tangent", u = tangentslope(a, b, cc, sp[2]));
      if(u == oo, next);
      my(v2 = subst(q, 'x, u), v); if(type(q) == "t_POL" && variable(q) != 'x, v2 = subst(q, variable(q), u));
      if(issquare(v2, &v), my(Pt = [L*u, L*v]); if(!ellisoncurve(E, Pt), error("not on curve"));
        listput(pts, Pt); listput(names, sp[1])));
    my(H = if(#pts, matdet(ellheightmatrix(E, Vec(pts))), 0));
    out[e] = [Vec(names), apply(P -> ellheight(E, P), Vec(pts)), ellrank(E)[1..2]]);
  out;
}
/* the images of the 2-torsion points (a^2,0), (b^2,0) of E' on E_+- ; returns [E, [Pa, Pb]] */
torsimages(a, b, al, be, ga, s, which) =
{
  my(S2 = a^2 + b^2, x0 = a^2*b^2/S2, kc = al*be*ga*s);
  my(T = if(which == 1, [x0, a*b*x0/kc], [S2, -a*b*s/ga]));
  my(Q = quotcurves(a, b, al, be, ga, s, T, which));
  vector(2, e, my(q = Q[e][1], E = cubic2ell(q), L = polcoeff(q, 3));
    [E, vector(2, k, my(P = [[a^2, 0], [b^2, 0]][k], u = uval(T, P), v); if(!issquare(subst(q, variable(q), u), &v), [0], [L*u, L*v]))]);
}
/* full MW data: rank, saturated basis, index of the structural subgroup */
mwindex(E, S) =
{
  my(r = ellrank(E), k = 1);
  while(r[1] < r[2] && k <= 4, r = ellrank(E, k, r[4]); k++);
  if(r[1] != r[2], return([Str(r[1..2]), "?", "rank unproven", apply(P -> ellheight(E, P), S)]));
  my(G = ellsaturation(E, r[4], 100), R = if(#G, matdet(ellheightmatrix(E, G)), 1));
  my(Sf = select(P -> P != [0] && ellheight(E, P) > 1e-20, S), Hs = if(#Sf, ellheightmatrix(E, Sf), [;]));
  my(rs = if(#Sf, matrank(Hs), 0), Sind = if(rs == #Sf, Sf, Sf[1..1]));
  my(idx = if(rs == r[1] && #Sind == rs, sqrt(matdet(ellheightmatrix(E, Sind)) / R), "n/a"));
  [r[1], rs, if(type(idx) == "t_STR", idx, round(idx, &er)), apply(P -> ellheight(E, P), S)];
}
