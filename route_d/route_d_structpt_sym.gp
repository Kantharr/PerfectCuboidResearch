/* Symbolic (in t = b/a) version of the psi1/psi2 elliptic factors and the structural section P_a.
   Normalisation: a = 1, b = t, al = 1 + t^2, be = ga = s = 1 (only c2c3 = kc = 1 + t^2 matters for h = 1, x). */
\r route_d_prym_split.gp
/* squarefree kernel of a rational function in (u, t): keep odd-multiplicity irreducible factors */
sqfker2(R) =
{
  my(n = numerator(R) * denominator(R), f = factor(n), P = 1, c = 1);
  for(i = 1, #f~, my(g = f[i,1]); if(type(g) != "t_POL", c *= g^f[i,2]; next); if(f[i,2] % 2, P *= g));
  core(numerator(c)*denominator(c)) * P;
}
symfactors(which) =
{
  my(a = 1, b = 't, S2 = 1 + 't^2, x0 = 't^2/S2);
  my(T = if(which == 1, [x0, 't*x0/S2], [S2, -'t]));
  my(d = splitdata(a, b, S2, 1, 1, 1, T, which), sp = sqpart(d[2]));
  [d, sp, T];
}
/* R = c * M^2 * rest, c squarefree rational, factoring fully in (u, t) */
sqpart2(R) =
{
  my(fn = factor(numerator(R)), fd = factor(denominator(R)), M = 1, rest = 1, c = 1);
  for(i = 1, #fn~, my(g = fn[i,1], e = fn[i,2]); if(type(g) != "t_POL", c *= g^e, M *= g^(e\2); rest *= g^(e%2)));
  for(i = 1, #fd~, my(g = fd[i,1], e = fd[i,2]); if(type(g) != "t_POL", c /= g^e, M /= g^((e+1)\2); rest *= g^(e%2)));
  my(N = numerator(c)*denominator(c), cc = core(abs(N)), res = [sign(c)*cc, M * sqrtint(abs(N)/cc) / denominator(c), rest]);
  if(res[1] * res[2]^2 * res[3] != R, error("sqpart2: R != c * M^2 * rest"));
  res;
}
symfactors(which) =
{
  my(a = 1, b = 't, S2 = 1 + 't^2, x0 = 't^2/S2);
  my(T = if(which == 1, [x0, 't*x0/S2], [S2, -'t]));
  my(d = splitdata(a, b, S2, 1, 1, 1, T, which), sp = sqpart2(d[2]));
  [d, sp, T];
}
/* curve E_t (coefficient vector [0,A2,0,A4,A6] over Q(t)) and section P(t) = image of (a^2,0) = (1,0) */
symcurve(which, e) =
{
  my(r = symfactors(which), q = sqfker2(r[1][1] + 2*(-1)^(e+1)*r[2][2]), T = r[3]);
  if(poldegree(q, 'u) != 3, error("not cubic"));
  my(L = polcoeff(q, 3, 'u), c2 = polcoeff(q, 2, 'u), c1 = polcoeff(q, 1, 'u), c0 = polcoeff(q, 0, 'u));
  my(ua = (0 + T[2]) / (1 - T[1]), qa = subst(q, 'u, ua), v);
  if(!issquare(qa, &v), error("q(u_a) not a square in Q(t)"));
  [[0, c2, 0, L*c1, L^2*c0], [L*ua, L*v], q];
}
/* division polynomials f_n in x for y^2 = x^3 + A2 x^2 + A4 x + A6 (PARI convention: psi_n = f_n (n odd), f_n*2y (n even)) */
divpols(c, N) =
{
  my(A2 = c[2], A4 = c[4], A6 = c[6 - 1], b2 = 4*A2, b4 = 2*A4, b6 = 4*A6, b8 = b2*A6 - A4^2 + 0);
  b8 = 4*A2*A6 - A4^2;
  my(F = 4*'x^3 + b2*'x^2 + 2*b4*'x + b6, f = vector(N + 2));   /* f[k+1] = f_k, with F = (2y)^2 */
  f[1] = 0; f[2] = 1; f[3] = 1;
  f[4] = 3*'x^4 + b2*'x^3 + 3*b4*'x^2 + 3*b6*'x + b8;
  f[5] = 2*'x^6 + b2*'x^5 + 5*b4*'x^4 + 10*b6*'x^3 + 10*b8*'x^2 + (b2*b8 - b4*b6)*'x + (b4*b8 - b6^2);
  for(n = 5, N, my(m = n \ 2);
    if(n % 2, f[n+1] = if(m % 2, f[m+3]*f[m+1]^3 - F^2*f[m]*f[m+2]^3, F^2*f[m+3]*f[m+1]^3 - f[m]*f[m+2]^3),
              f[n+1] = f[m+1] * (f[m+3]*f[m]^2 - f[m-1]*f[m+2]^2)));
  f;
}
