/* Symbolic proof, valid on every Route D fibre, that the Prym surfaces psi3, psi4 of the cuboid
   cover C are Weil restrictions from K = Q(sqrt(a^2+b^2)) of explicit twists of curves over Q.

   Setting (perfect_cuboid.tex, Section 6).  Fibre (a,b,al,be,ga,s) with sigma = a^2+b^2 = al*be*s^2.
   E': al*be*ga^2 y^2 = x(x-a^2)(x-b^2),  F = ab(sigma-x)(ab x - al*be*ga*s y),
   D_h: W^2 = h F,  psi3 = Prym(D_h/E') for h = (a^2-x)/(al ga),  psi4 for h = (b^2-x)/(be ga).
   Reduction to the line (by hand, as for h = 1, x in the paper): y = s y'/ga turns E', F into
   sigma y'^2 = x(x-a^2)(x-b^2), ab(sigma-x)(ab x - sigma y'); the constant 1/(al ga) in h is a
   quadratic twist of D_h by its deck involution W -> -W, which acts as -1 on the Prym.  Hence
     psi3(fibre) = (Prym of W^2 = (a^2-x)F on the line model)^(al*ga)   (quadratic twist),
     psi4(fibre) = (Prym of W^2 = (b^2-x)F on the line model)^(be*ga),
   and x = a^2 X, y' = a^2 Y (square factors only) normalises to a = 1, b = t.

   Line model over Q(t):  S y^2 = x(x-1)(x-t^2),  S = 1+t^2,  F = t(S-x)(t x - S y),
   B1 = (S, -t),  rho(P) = B1 - P,  u = slope of the line through -B1 and P, Q(E')^rho = Q(u).
   K(t) = Q(t, r), r^2 = S, is the rational function field Q(w):  t = (1-w^2)/2w, r = (1+w^2)/2w;
   Galois conjugation r -> -r is w -> -1/w.

   Checked here, all by exact arithmetic:
   (1) Nm(hF) = S * M^2 with M in Q(t)[u]  => rho lifts to an involution of D_h over K (not over Q).
   (2) f+- = Tr +- 2 r M = q+- * g+-^2 in Q(w)(u), q+- = C * (three distinct linear factors in u):
       both quotients D_h/rho~ are genus 1 (Kani-Rosen: 3 = 1 + 1 + 1), and f-(w) = f+(-1/w),
       so the second quotient is the Galois conjugate of the first.
   (3) The Jacobian A+ of V^2 = q+ is K(t)-isomorphic to the twist E_k^(delta_k) of
         E_3: Y^2 = X(X^2 - 4t^2 S X - 4t^2 S^2),   delta_3 = -2(1 + r)
         E_4: Y^2 = X(X^2 - 4 S X - 4t^2 S^2),     delta_4 = 2t(r - t)
       (and A- to the twist by the conjugate).  Homogenised (t = b/a):
         E_3: Y^2 = X(X^2 - 4b^2 sigma X - 4a^2b^2 sigma^2),  delta_3 = -2a(a + sqrt sigma)
         E_4: Y^2 = X(X^2 - 4a^2 sigma X - 4a^2b^2 sigma^2),  delta_4 = 2b(sqrt sigma - b).
   (4) Nm_{K/Q}(delta_k) = -(square): the twist is not in Q* K*^2 (D4 closure).
   (5) The finitely many rational t where a denominator, leading coefficient or discriminant met
       above vanishes, and the rational t where E_3 or E_4 has CM (rational CM j-invariants).
   (6) Specialisation to 11:3 (65,2,1) reproduces the published curves [0,0,0,-532,-2064] twisted
       by 33(11+sqrt130) and [0,-1,0,-681,7065] twisted by -4290(3+sqrt130), up to conjugation.   */

default(parisize, 1000000000);
NOK = 0;
ok(c, msg) = if(!c, error("FAIL: ", msg)); NOK++; print("  ok   ", msg);
nd(R) = my(D = denominator(R), N = R*D); if(denominator(N) != 1, error("nd")); [N, D];
sqrtrat(q) = sqrtint(numerator(q)) / sqrtint(denominator(q));
isratsq(q) = q > 0 && issquare(numerator(q)) && issquare(denominator(q));
/* is the rational function R (in any variables) a square: all factor exponents even, constant a square */
isfsq(R) =
{
  my(v = nd(R), fn = factor(v[1]), fd = factor(v[2]), g = 1);
  for(i = 1, #fn~, if(fn[i,2] % 2, return(0)); g *= fn[i,1]^(fn[i,2]/2));
  for(i = 1, #fd~, if(fd[i,2] % 2, return(0)); g /= fd[i,1]^(fd[i,2]/2));
  my(k = simplify(R / g^2)); (type(k) == "t_INT" || type(k) == "t_FRAC") && isratsq(k);
}
S = 1 + 't^2;
ts = (1 - 'w^2)/(2*'w); rs = (1 + 'w^2)/(2*'w);
tw(f) = subst(subst(f, 'r, rs), 't, ts);                /* Q(t, r) -> Q(w) */
sig(f) = subst(f, 'w, -1/'w);                           /* r -> -r */

trnm(k) =
{
  my(h = if(k == 3, 1 - 'x, 't^2 - 'x), kx = 'x*('x - 1)*('x - 't^2)/S, xT = S, yT = -'t);
  my(yl = 'u*('x - xT) - yT, Q = (yl^2 - kx)/('x - xT));
  if(poldegree(numerator(Q), 'x) != 2, error("Q"));
  my(Fm = Mod(h*'t*(S - 'x)*('t*'x - S*yl), Q));
  [trace(Fm), norm(Fm)];
}
sqrtN(Nm) =
{
  my(v = nd(Nm / S), fn = factor(v[1]), fd = factor(v[2]), M = 1);
  for(i = 1, #fn~, if(fn[i,2] % 2, error("odd factor ", fn[i,1])); M *= fn[i,1]^(fn[i,2]/2));
  for(i = 1, #fd~, if(fd[i,2] % 2, error("odd factor ", fd[i,1])); M /= fd[i,1]^(fd[i,2]/2));
  my(k2 = simplify(Nm / (S * M^2))); if(!isratsq(k2), error("constant ", k2));
  M * sqrtrat(k2);
}
kern(f) =
{
  my(v = nd(f), fn = factor(v[1]), fd = factor(v[2]), q = 1, g = 1);
  for(i = 1, #fn~, q *= fn[i,1]^(fn[i,2] % 2); g *= fn[i,1]^(fn[i,2] \ 2));
  for(i = 1, #fd~, q *= fd[i,1]^(fd[i,2] % 2); g /= fd[i,1]^((fd[i,2] + 1) \ 2));
  my(k = simplify(f / (q * g^2)), c = core(numerator(k)*denominator(k))); q *= c; g *= sqrtrat(k / c);
  [q, g];
}
ainv3(R) = [0, -(R[1] + R[2] + R[3]), 0, R[1]*R[2] + R[1]*R[3] + R[2]*R[3], -R[1]*R[2]*R[3]];
cinv(a) = { my(b2 = 4*a[2], b4 = 2*a[4], b6 = 4*a[5], b8 = b2*a[5] - a[4]^2);
  [b2^2 - 24*b4, -b2^3 + 36*b2*b4 - 216*b6, -b2^2*b8 - 8*b4^3 - 27*b6^2 + 9*b2*b4*b6]; }
jof(a) = my(c = cinv(a)); c[1]^3 / c[3];
/* A = E^d for curves with j != 0, 1728: equal j and c6(A) c4(E) / (c6(E) c4(A) d) a square */
istwist(A, E, d) = my(u = cinv(A), v = cinv(E)); jof(A) == jof(E) && isfsq(u[2]*v[1] / (v[2]*u[1]*d));
twist(E, d) = [0, d*E[2], 0, d^2*E[4], d^3*E[5]];

E3 = [0, -4*'t^2*S, 0, -4*'t^2*S^2, 0];  d3 = -2*(1 + 'r);
E4 = [0, -4*S, 0, -4*'t^2*S^2, 0];       d4 = 2*'t*('r - 't);
BAD = List();                                   /* rational functions whose zeros must be avoided */
addbad(f) = listput(BAD, f);

print("(0) the conic parametrisation");
ok(tw(S) == rs^2 && sig(ts) == ts && sig(rs) == -rs, "t = (1-w^2)/2w, r = (1+w^2)/2w: r^2 = 1+t^2, and w -> -1/w fixes t, negates r");

{for(k = 3, 4,
  my(tn = trnm(k), Tr = tn[1], Nm = tn[2], M = sqrtN(Nm), E0 = if(k == 3, E3, E4), d0 = if(k == 3, d3, d4));
  print("\npsi", k, "  (h = ", if(k == 3, "a^2 - x", "b^2 - x"), " on the line)");
  ok(Nm == S * M^2, "(1) Nm(hF) = (1+t^2) * M^2 exactly, M in Q(t)[u]");
  ok(!isfsq(Nm), "(1) Nm is not a square in Q(t)(u): rho lifts over K = Q(sqrt(1+t^2)) but not over Q");
  addbad(Tr); addbad(M);
  my(fp = tw(Tr + 2*'r*M), fm = tw(Tr - 2*'r*M));
  ok(fm == sig(fp), "(2) f-(w) = f+(-1/w): the two quotients are Galois conjugate over K");
  for(e = 0, 1, my(f = if(e, fm, fp), kq = kern(f), q = kq[1], g = kq[2]);
    my(C = polcoeff(q, 3, 'u), fa = factor(q)[,1], rt = []);
    for(i = 1, #fa, if(poldegree(fa[i], 'u) == 1, rt = concat(rt, [-polcoeff(fa[i], 0, 'u)/polcoeff(fa[i], 1, 'u)])));
    ok(f == q*g^2 && poldegree(q, 'u) == 3 && #rt == 3 && q == C*prod(i = 1, 3, 'u - rt[i]),
       Str("(2) f", if(e, "-", "+"), " = q * g^2, q = C (u-e1)(u-e2)(u-e3) over Q(w)"));
    ok(rt[1] != rt[2] && rt[1] != rt[3] && rt[2] != rt[3], "(2)    e1, e2, e3 distinct: the quotient has genus 1");
    addbad(C); addbad(g); for(i = 1, 3, addbad(rt[i]); for(j = i + 1, 3, addbad(rt[i] - rt[j])));
    my(A = ainv3(C*rt), dd = tw(if(e, subst(d0, 'r, -'r), d0)));
    ok(istwist(A, tw(E0), dd), Str("(3) Jacobian of the ", if(e, "- ", "+ "), "quotient = E_", k, " twisted by ",
       if(e, "the conjugate of ", ""), "delta_", k, " over K(t)"));
    addbad(jof(A)); addbad(cinv(A)[1]); addbad(cinv(A)[2]));
  ok(simplify(tw(d0)*sig(tw(d0))) == tw(-4*'t^2),
     Str("(4) Nm(delta_", k, ") = -4t^2 = -(square): delta_", k, " is not in Q* K*^2"));
  addbad(cinv(E0)[3]); addbad(cinv(E0)[1]); addbad(cinv(E0)[2]))}

/* (5) exceptional parameters.  A factor p(w) can vanish at w0 = -t0 +- sqrt(1+t0^2) only if
   Res_w(p, w^2 + 2 t w - 1) vanishes at t0; factors in t alone are used directly. */
ratroots(P) = my(fa = factor(P)[,1], Rr = List()); for(i = 1, #fa, if(poldegree(fa[i]) == 1, listput(Rr, -polcoeff(fa[i], 0)/polcoeff(fa[i], 1)))); Set(Rr);
tpolys(f) =
{
  my(v = nd(f), L = List());
  for(j = 1, 2, my(fa = factor(v[j])[,1]);
    for(i = 1, #fa, my(p = fa[i]);
      if(type(p) != "t_POL", next);
      if(variable(p) == 'u || poldegree(p, 'u) > 0, p = polcoeff(p, poldegree(p, 'u), 'u));
      if(poldegree(p, 'w) > 0, p = polresultant(p, 'w^2 + 2*'t*'w - 1, 'w));
      if(type(p) == "t_POL" && poldegree(p, 't) > 0, listput(L, p))));
  L;
}
{print("\n(5) exceptional rational t");
 my(bad = Set());
 for(i = 1, #BAD, my(L = tpolys(BAD[i])); for(j = 1, #L, bad = setunion(bad, ratroots(L[j]))));
 print("  rational t where some denominator / leading coefficient / discriminant / c4 / c6 vanishes: ", bad);
 ok(setminus(bad, [-1, 0, 1]) == [], "(5) all lie in {0, +-1} (the degenerate lines b = 0, a = +-b)");
 my(cmj = [0, 1728, -3375, 8000, -32768, 54000, 287496, -884736, -12288000, 16581375, -884736000, -147197952000, -262537412640768000], cm = Set());
 for(k = 3, 4, my(j = jof(if(k == 3, E3, E4)));
   for(i = 1, #cmj, cm = setunion(cm, ratroots(numerator(j - cmj[i])))));
 print("  rational t where E_3 or E_4 has CM: ", cm);
 ok(setminus(cm, [-1, 0, 1]) == [], "(5) E_3, E_4 have no CM for t outside {0, +-1}")}

/* (6) the published 11:3 (65,2,1) curves.  nf-level check in K = Q(sqrt130), variable y. */
XX = varhigher("XX");
nfsq(K, z) = #nfroots(K, XX^2 - z) > 0;     /* z in K, as a polynomial in y */
{print("\n(6) specialisation to the fibre 11:3 (65,2,1), K = Q(sqrt 130)");
 my(K = nfinit('y^2 - 130), a = 11, b = 3, al = 65, be = 2, ga = 1, sg = a^2 + b^2, r = Mod('y, 'y^2 - 130));
 my(H3 = [0, -4*b^2*sg, 0, -4*a^2*b^2*sg^2, 0], H4 = [0, -4*a^2*sg, 0, -4*a^2*b^2*sg^2, 0]);
 my(D3 = al*ga*(-2*a*(a + r)), D4 = be*ga*(-2*b*(b + r)));
 my(P3 = [0, 0, 0, -532, -2064], Q3 = 33*(11 + r), P4 = [0, -1, 0, -681, 7065], Q4 = -4290*(3 + r));
 for(k = 3, 4, my(A = twist(if(k == 3, H3, H4), if(k == 3, D3, D4)), B = if(k == 3, P3, P4), dq = if(k == 3, Q3, Q4));
   my(u = cinv(A), cB = cinv(B), found = "none");
   for(e = 0, 1, my(dd = if(e, subst(lift(dq), 'y, -'y), dq), Bt = twist(B, Mod(dd, 'y^2 - 130)), v = cinv(Bt));
     if(jof(A) == jof(Bt) && nfsq(K, lift(u[2]*v[1] / (v[2]*u[1]))), found = if(e, "conjugate of published twist", "published twist")));
   ok(found != "none", Str("(6) psi", k, ": closed form = published curve (", found, ")")))}
if(NOK == 25, print("\nALL 25 CHECKS PASSED"), print("\nINCOMPLETE: only ", NOK, " of 25 checks ran"));
quit
