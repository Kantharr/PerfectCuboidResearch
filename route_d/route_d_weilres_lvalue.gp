/* Central value L(E/K, 1) for an elliptic curve E over a real quadratic field K, by the explicit
   series of the approximate functional equation.  Used for the psi3/psi4 Weil restrictions of
   Theorem 6.5 (L(Res_{K/Q} E, s) = L(E/K, s)).

   Lambda(s) = A^s Gamma(s)^2 L(s),  A = sqrt(N)/(4 pi^2),  N = disc(K)^2 * Nm(cond(E)),
   Lambda(s) = eps * Lambda(2 - s).   Gamma(s)^2 is the Mellin transform of 2 K_0(2 sqrt x); splitting
   the Mellin integral at t0 > 0 gives, for every t0,
     L(1) = sum_n a_n/n * ( G(n t0 / A) + eps * G(n / (t0 A)) ),   G(z) = 2 sqrt(z) K_1(2 sqrt(z)).
   Independence of t0 checks conductor, root number and coefficients together (like lfuncheckfeq).
   Terms decay like exp(-2 sqrt(n/A)); nmax(t0) is chosen so that 2 sqrt(n t0'/A) >= ZCUT for the
   smaller of t0, 1/t0.

   lvalue(E, K, T0, ZCUT): E = ellinit(..., K).  Returns [L(1) for each t0 in T0, N, eps, nmax].  */

Gz(z) = my(u = 2*sqrt(z)); u * besselk(1, u);

lvalue(E, K, T0, ZCUT) =
{
  my(N = abs(K.disc)^2 * idealnorm(K, ellglobalred(E)[1]), eps = ellrootno(E), A = sqrt(N)/(4*Pi^2));
  my(tmin = vecmin(concat(T0, apply(t -> 1/t, T0))), nmax = ceil(A * (ZCUT/2)^2 / tmin));
  my(t0 = getabstime(), an = ellan(E, nmax));
  print("   N = ", N, " = ", factor(N), ",  eps = ", eps, ",  A = ", A, ",  nmax = ", nmax,
        "  (ellan ", (getabstime() - t0) \ 1000, " s)");
  my(S = vector(#T0), t1 = getabstime());
  for(n = 1, nmax, my(a = an[n]); if(!a, next);
    for(j = 1, #T0, my(x1 = n*T0[j]/A, x2 = n/(T0[j]*A), g = 0.);
      if(2*sqrt(x1) < ZCUT, g += Gz(x1)); if(2*sqrt(x2) < ZCUT, g += eps*Gz(x2));
      S[j] += a*g/n));
  print("   series ", (getabstime() - t1) \ 1000, " s");
  [S, N, eps, nmax];
}
