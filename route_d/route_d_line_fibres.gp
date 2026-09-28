/* All fibres of a line a:b that carry a rational point, from the image of E(Q)/2E(Q).

   Every triple with x:y = a:b lies on a fibre with a rational point, and a fibre with kernel
   (al, be, ga) is the 2-covering of E = E_{a,b} of class (sigma, -sigma al ga)  [Kummer map
   P -> (X, X - a^2 sigma) modulo squares; see route_d_fiber_descent.gp].  So the fibres of the line
   with a rational point are exactly those whose class is d(P) for some P in E(Q), with first
   coordinate sigma.  From such a class (d1, d2):
       al*ga = core(-sigma d2),   be*ga = core(-sigma d1 d2)   (third coordinate d3 = d1 d2),
   and a triple x > y > z > 0 needs al*ga > 0 and be*ga > 0.  Then ga = gcd(al ga, be ga).
   The fibres with al*ga = core(a^2 - b^2) (through (a,b,b)) and core(a^4 - b^4) (through
   (a^2,ab,b^2)) are the two degenerate ones; all others are clean.

   linefibres(a, b) returns [status, rank, list] with list entries
       [al, be, ga, kind, base point [t, z, u2, u3]]     kind = "clean", "y=z" or "case1".
   batchentries(a, b) gives the clean ones as [a, b, al, be, ga, bp] for route_d_batch.py.      */
\r route_d_fiber_descent.gp

sqrtq(q) = my(r); if(q < 0 || !issquare(q, &r), 0, r);

linefibres(a, b) =
{
  my(sg = a^2 + b^2, e = [0, a^2*sg, b^2*sg], E = ellinit([0, -(e[2] + e[3]), 0, e[2]*e[3], 0]));
  my(rk = ellrank(E, 4), eff = 4);
  while(rk[1] != rk[2] && eff < 8, eff++; rk = ellrank(E, eff));
  if(rk[1] != rk[2], return(["rank not proven", rk[1..3], []]));
  my(G = rk[4]); if(#G < rk[1], G = isogpts(E, G, rk[1], 8));
  if(#G < rk[1], return(["generators incomplete", rk[1..3], []]));
  G = ellsaturation(E, G, 2);
  my(gens = concat(G, elltors(E)[3]), n = #gens, imgs = apply(P -> kum(E, P, e), gens));
  my(PR = Set(concat(apply(v -> concat(primesof(v[1]), primesof(v[2])), imgs))));
  my(M = matconcat(apply(v -> concat(sqvec(v[1], PR), sqvec(v[2], PR))~, imgs)));
  my(n2 = #twotors(E), dimE = rk[1] + if(n2 == 3, 2, n2));
  if(matrank(M*Mod(1, 2)) != dimE, error("Kummer image has the wrong dimension on ", [a, b]));
  my(dy = core(a^2 - b^2), dc = core(a^4 - b^4), out = List(), seen = Map());
  forvec(x = vector(n, i, [0, 1]),
    my(c = [1, 1]); for(i = 1, n, if(x[i], c = [core(c[1]*imgs[i][1]), core(c[2]*imgs[i][2])]));
    if(c[1] != core(sg) || mapisdefined(seen, c), next); mapput(seen, c, 1);
    my(ag = core(-sg*c[2]), bg = core(-sg*c[1]*c[2]));
    if(ag < 0 || bg < 0, next);                              /* no triple x > y > z > 0 */
    my(ga = gcd(ag, bg), al = ag/ga, be = bg/ga);
    if(!issquare(sg/(al*be)), error("sigma/(al be) not a square on ", [a, b, al, be, ga]));
    my(kind = if(ag == dy, "y=z", if(ag == dc, "case1", "clean")));
    /* a point with this class, moved off the 2-torsion x-coordinates if necessary */
    my(P = [0]); for(i = 1, n, if(x[i], P = elladd(E, P, gens[i])));
    my(bp = 0);
    for(k = 0, 6, my(Q = if(k == 0 || #G == 0, P, elladd(E, P, ellmul(E, G[1], 2*k))));
      if(Q == [0], next);
      my(X = Q[1], r = [sqrtq(X/sg), sqrtq((X - e[2])/(-sg*al*ga)), sqrtq((X - e[3])/(-sg*be*ga))]);
      if(X == e[2] || X == e[3] || (r[1] == 0 && X != 0) || (r[2] == 0 && X != e[2]) || (r[3] == 0 && X != e[3]), next);
      my(d = lcm([denominator(r[1]), denominator(r[2]), denominator(r[3])]));
      bp = [d, r[1]*d, r[2]*d, r[3]*d]; break);
    if(bp == 0 && kind == "clean", error("no base point found for ", [a, b, al, be, ga]));
    if(bp != 0 && (a^2*bp[1]^2 - bp[2]^2 != al*ga*bp[3]^2 || b^2*bp[1]^2 - bp[2]^2 != be*ga*bp[4]^2),
      error("base point check failed on ", [a, b, al, be, ga]));
    listput(out, [al, be, ga, kind, bp]));
  ["ok", rk[1], Vec(out)];
}

batchentries(a, b) =
{
  my(r = linefibres(a, b));
  if(r[1] != "ok", return(r));
  [r[1], r[2], [[a, b, f[1], f[2], f[3], f[5]] | f <- r[3], f[4] == "clean"]];
}
