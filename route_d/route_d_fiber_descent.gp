/* Does a Route D fibre have a rational point?  Exact 2-descent membership test.

   Fibre X (ratio a:b, kernel al,be,ga):  a^2 t^2 - z^2 = al*ga*u2^2,  b^2 t^2 - z^2 = be*ga*u3^2.
   With sigma = a^2+b^2 and E = E_{a,b}: Y^2 = X(X - a^2 sigma)(X - b^2 sigma), the map
   X = sigma z^2/t^2 makes the fibre the 2-covering of E with Kummer class
       c(X) = ( sigma, -sigma*al*ga )   (a pair of rational square classes),
   for the Kummer map P -> (X(P) - 0, X(P) - a^2 sigma)  (X - b^2 sigma = -sigma*be*ga then
   follows, since sigma = al*be*s^2).  Hence
       X(Q) nonempty  <=>  c(X) lies in the image of E(Q)/2E(Q).
   Given a rank that is proven (ellrank lower = upper bound) and generators saturated at 2, the image
   is the F_2-span of the Kummer images of the generators and of E(Q)_tors, so the test is exact.
   When the class is in the image, a point P with that image gives a rational base point
   (t : z : u2 : u3) = (1 : sqrt(X/sigma) : sqrt((X - a^2 sigma)/(-sigma al ga)) : ...).       */

\r route_d_isogpoints.gp

kum(E, P, e) =                         /* Kummer image (X - e1, X - e2), e = [e1, e2, e3] */
{
  if(P == [0], return([1, 1]));
  my(x = P[1], v = vector(2, i, if(x == e[i], (e[i] - e[3 - i])*(e[i] - e[3]), x - e[i])));
  apply(q -> core(numerator(q)*denominator(q)), v);
}
primesof(n) = if(abs(n) == 1, [], factor(abs(n))[,1]~);
/* square classes -> F_2 vectors over the primes of the given set (with -1 first) */
sqvec(c, PR) = concat([c < 0], vector(#PR, i, valuation(c, PR[i]) % 2));

fiberdescent(a, b, al, be, ga) =
{
  my(sg = a^2 + b^2, e = [0, a^2*sg, b^2*sg], E = ellinit([0, -(e[2] + e[3]), 0, e[2]*e[3], 0]));
  my(rk = ellrank(E, 4), eff = 4);
  while(rk[1] != rk[2] && eff < 8, eff++; rk = ellrank(E, eff));
  if(rk[1] != rk[2], return(["rank not proven", rk[1..3]]));
  my(G = rk[4]);
  if(#G < rk[1], G = isogpts(E, G, rk[1], 8));                 /* rank proven, points missing */
  if(#G < rk[1], return(["generators incomplete", rk[1..3], #G]));
  G = ellsaturation(E, G, 2);                                  /* saturate at 2 */
  my(T = elltors(E)[3], gens = concat(G, T), c = [core(sg), core(-sg*al*ga)]);
  my(imgs = apply(P -> kum(E, P, e), gens));
  my(PR = Set(concat(apply(v -> concat(primesof(v[1]), primesof(v[2])), concat(imgs, [c])))));
  my(M = matconcat(apply(v -> concat(sqvec(v[1], PR), sqvec(v[2], PR))~, imgs)));
  my(w = concat(sqvec(c[1], PR), sqvec(c[2], PR))~);
  /* the Kummer map is injective on E(Q)/2E(Q), of F_2-dimension rank + dim E(Q)[2]; a smaller span
     would mean the generators are not 2-saturated */
  my(n2 = #twotors(E), dimE = rk[1] + if(n2 == 3, 2, n2), dimI = matrank(M*Mod(1, 2)));
  if(dimI != dimE, error("Kummer image has dimension ", dimI, " != rank + dim E(Q)[2] = ", dimE));
  my(sol = matsolvemod(M, 2, w));                              /* M * x = w over F_2 ? */
  if(type(sol) == "t_INT" && sol == 0, return(["NO RATIONAL POINT", rk[1..3], #G]));
  /* build P = sum x_i gens_i and a base point on the fibre */
  my(P = [0]); for(i = 1, #gens, if(sol[i] % 2, P = elladd(E, P, gens[i])));
  if(kum(E, P, e) != c, error("kummer mismatch"));
  my(x = P[1], q = [x/sg, (x - e[2])/(-sg*al*ga), (x - e[3])/(-sg*be*ga)], r = vector(3));
  if(P == [0] || !issquare(q[1], &r[1]) || !issquare(q[2], &r[2]) || !issquare(q[3], &r[3]),
    return(["IN IMAGE (point needs a torsion shift)", rk[1..3], #G, P]));
  my(d = lcm([denominator(r[1]), denominator(r[2]), denominator(r[3])]), bp = [d, r[1]*d, r[2]*d, r[3]*d]);
  if(a^2*bp[1]^2 - bp[2]^2 != al*ga*bp[3]^2 || b^2*bp[1]^2 - bp[2]^2 != be*ga*bp[4]^2, error("base point check"));
  ["HAS POINT", rk[1..3], #G, bp];
}
