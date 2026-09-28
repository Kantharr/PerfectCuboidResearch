/* Rank-1 lines: every clean fibre has no rational point.

   E = E_{a,b}: Y^2 = X(X - a^2 s)(X - b^2 s), s = sigma = a^2 + b^2, e = [0, a^2 s, b^2 s].
   Kummer map d(P) = (X - e1, X - e2) modulo squares (with the usual rule at 2-torsion points).
     d(0,0)        = (a^2 b^2 s^2, -a^2 s)          = (1, -s)
     d(a^2 s, 0)   = (a^2 s, a^2 s * (a^2-b^2) s)   = (s, a^2 - b^2)
     d(P1), P1 = (a^2 b^2, a^3 b^3):  (a^2 b^2, -a^4) = (1, -1)
   For s not a square these are independent, so if rank E(Q) = 1 they span the image of
   E(Q)/2E(Q) (dimension 1 + 2).  A fibre with kernel (al, be, ga) is the 2-covering of class
   (s, -s al ga), so it has a rational point iff al*ga = a^2 - b^2 or s(a^2 - b^2) mod squares
   (al*ga > 0 and a > b rule out the other two elements with first coordinate s): the fibres
   through (a, b, b) and through (a^2, ab, b^2).

   Part 1 checks the three images symbolically; part 2 checks, on every line a > b, a <= AMAX,
   a, b odd and coprime, with rank proven 1 by ellrank, that the image of E(Q)/2E(Q) computed from
   ellrank's generator (2-saturated) equals the span above.                                     */

default(parisize, 1000000000);
sq(q) = core(numerator(q)*denominator(q));
kum(P, e) =
{
  if(P == [0], return([1, 1]));
  my(x = P[1]); vector(2, i, sq(if(x == e[i], (e[i] - e[3 - i])*(e[i] - e[3]), x - e[i])));
}

print("Part 1: symbolic Kummer images (a, b indeterminates)");
{
  my(s = 'a^2 + 'b^2, e = [0, 'a^2*s, 'b^2*s], f(X) = X*(X - e[2])*(X - e[3]));
  if(f('a^2*'b^2) != ('a^3*'b^3)^2, error("P1 not on E"));
  my(t1 = [(e[1] - e[2])*(e[1] - e[3]), -e[2]], t2 = [e[2], (e[2] - e[1])*(e[2] - e[3])], p1 = ['a^2*'b^2, 'a^2*'b^2 - e[2]]);
  if(t1 != ['a^2*'b^2*s^2, -'a^2*s], error("T1"));
  if(t2 != ['a^2*s, 'a^2*s^2*('a^2 - 'b^2)], error("T2"));
  if(p1 != ['a^2*'b^2, -'a^4], error("P1 image"));
  print("  ok  P1 = (a^2 b^2, a^3 b^3) lies on E_{a,b}");
  print("  ok  d(0,0) = (a^2 b^2 s^2, -a^2 s) = (1, -s);  d(a^2 s, 0) = (a^2 s, a^2 s^2 (a^2 - b^2)) = (s, a^2 - b^2)");
  print("  ok  d(P1) = (a^2 b^2, -a^4) = (1, -1)   [all modulo squares]");
}

/* F_2-span of square-class pairs; membership by linear algebra over the primes involved */
primesof(n) = if(abs(n) == 1, [], factor(abs(n))[,1]~);
vec2(v, PR) =
{
  concat(concat([v[1] < 0], vector(#PR, i, valuation(v[1], PR[i]) % 2)),
         concat([v[2] < 0], vector(#PR, i, valuation(v[2], PR[i]) % 2)))~;
}
spanof(L) =
{
  my(PR = Set(concat(apply(v -> concat(primesof(v[1]), primesof(v[2])), L))));
  [PR, matconcat(apply(v -> vec2(v, PR), L))];
}
inspan(S, v) =
{
  my(PR = Set(concat(apply(c -> concat(primesof(c[1]), primesof(c[2])), concat(S[3], [v])))));
  my(M = matconcat(apply(c -> vec2(c, PR), S[3])));
  type(matsolvemod(M, 2, vec2(v, PR))) != "t_INT";
}

AMAX = 99;
print("\nPart 2: all lines a > b, a <= ", AMAX, ", a and b odd and coprime");
{
  my(nl = 0, n1 = 0, bad = List(), other = [0, 0, 0]);
  forstep(a = 3, AMAX, 2, forstep(b = 1, a - 2, 2, if(gcd(a, b) != 1, next);
    nl++;
    my(s = a^2 + b^2, e = [0, a^2*s, b^2*s], E = ellinit([0, -(e[2] + e[3]), 0, e[2]*e[3], 0]), rk = ellrank(E, 4));
    if(rk[1] != rk[2], other[3]++; next);
    if(rk[1] != 1, other[if(rk[1] == 0, 1, 2)]++; next);
    n1++;
    my(G = rk[4]); if(#G < 1, listput(bad, [a, b, "no generator"]); next);
    G = ellsaturation(E, G, 2);
    my(L3 = [[1, -s], [s, a^2 - b^2], [1, -1]], S = [0, 0, L3]);
    my(M3 = spanof(L3)); if(matrank(M3[2]*Mod(1, 2)) != 3, listput(bad, [a, b, "span dim < 3"]); next);
    /* the full image: generator plus torsion */
    my(img = apply(P -> kum(P, e), concat(G, elltors(E)[3])));
    if(matrank(spanof(img)[2]*Mod(1, 2)) != 3, listput(bad, [a, b, "image dim != 3"]); next);
    for(i = 1, #img, if(!inspan(S, img[i]), listput(bad, [a, b, "generator image not in span"])))));
  print("  lines: ", nl, ";  rank proven 1: ", n1, ";  rank 0: ", other[1], ", rank >= 2: ", other[2], ", rank not proven: ", other[3]);
  print("  rank-1 lines where the image differs from span{d(T1), d(T2), d(P1)}: ", Vec(bad));
  if(#bad == 0, print("  ok  on every rank-1 line the image of E(Q)/2E(Q) is span{(1,-s), (s, a^2-b^2), (1,-1)}"));
}
quit
