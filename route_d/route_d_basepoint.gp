/* rational points on the Route D fiber a^2 t^2 - z^2 = al*ga*u2^2,  b^2 t^2 - z^2 = be*ga*u3^2
   via the conic  ga*al*u2^2 - ga*be*u3^2 = (a^2-b^2) t^2  and a quartic search with hyperellratpoints. */
fiberpoints(a, b, al, be, ga, H) =
{
  my(G = matdiagonal([ga*al, -ga*be, -(a^2 - b^2)]), s = qfsolve(G), M, v, Q, pts, out = List());
  if(type(s) != "t_COL", return([]));
  M = qfparam(G, s);
  v = M * [x^2, x, 1]~;                       
  Q = a^2*v[3]^2 - ga*al*v[1]^2;              
  pts = hyperellratpoints(Q, H);
  for(i = 1, #pts, my(m = pts[i][1], z = pts[i][2], u2 = subst(v[1], x, m), u3 = subst(v[2], x, m), t = subst(v[3], x, m), d);
    if(t == 0 || z == 0 || u2 == 0 || u3 == 0, next);
    d = lcm([denominator(t), denominator(z), denominator(u2), denominator(u3)]);
    my(P = [t, z, u2, u3] * d, g = gcd(P)); P = P / g;
    if(P[1] < 0, P = -P);
    if(a^2*P[1]^2 - P[2]^2 != ga*al*P[3]^2 || b^2*P[1]^2 - P[2]^2 != ga*be*P[4]^2, error("point not on fiber"));
    listput(out, P));
  vecsort(Vec(out), (p, q) -> abs(p[1]) - abs(q[1]));
}
