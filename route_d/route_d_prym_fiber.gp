/* Frobenius traces on the four Prym surfaces of the cuboid cover C: W^2 = F over a Route D
   fiber, computed DIRECTLY on the fiber model in P^3 (independent of any Weierstrass model):
     fiber:  a^2 t^2 - z^2 = c2 u2^2,  b^2 t^2 - z^2 = c3 u3^2   (c2 = al*ga, c3 = be*ga)
     F = ab t^3 z (S2 t^2 - z^2)(ab t z - kc u2 u3),  S2 = a^2 + b^2,  kc = al*be*ga*s.
   E[2]-translations are the fixed-point-free sign changes id, s23 = (u2,u3)->-, sz2, sz3.
   Over F_q (q = p^k):  S_T = sum over points v with Frob_q(v) = sigma_T(v) of the contribution
     chi_q(F(v))            if F(v) != 0,
     0                      at a simple zero of F (branch point: one point on C),
     chi_q(residue)         at the double zeros S = G = 0 (residue of F/S^2 = ab z G/S, via
                            the ratio of directional derivatives along the fiber).
   tr(Frob_q | V_psi) = -(1/4) sum_T psi(T) S_T.                                           */
fibertraces(a, b, al, be, ga, s, p, k = 1) =
{
  my(q = p^k, g = ffgen([p, 2*k], 'w), one = g^0, c2 = al*ga, c3 = be*ga, S2 = a^2 + b^2, kc = al*be*ga*s, ab = a*b);
  my(chi(v) = my(c = v^((q - 1) / 2)); if(c == 1, 1, if(c == -1, -1, error("chi not +-1"))));
  my(sig = [[1,1,1], [1,-1,-1], [-1,-1,1], [-1,1,-1]]);         /* on (z,u2,u3): id, s23, sz2, sz3 */
  my(Sv = vector(4), nb = 0, nd = 0);
  my(normalize(v) = my(i = 1); while(v[i] == 0, i++); v / v[i]);
  my(contrib(v) =
       my(t = v[1], z = v[2], u2 = v[3], u3 = v[4], S = S2*t^2 - z^2, G = ab*t*z - kc*u2*u3, F = ab*t^3*z*S*G);
       if(F != 0, return(chi(F)));
       if(t != 0 && S == 0 && G == 0,
         /* chart t = 1: gradients in (z,u2,u3) */
         my(gQ1 = [-2*z, -2*c2*u2, 0], gQ2 = [-2*z, 0, -2*c3*u3],
            w = [gQ1[2]*gQ2[3] - gQ1[3]*gQ2[2], gQ1[3]*gQ2[1] - gQ1[1]*gQ2[3], gQ1[1]*gQ2[2] - gQ1[2]*gQ2[1]],
            dS = -2*z*w[1], dG = ab*w[1] - kc*u3*w[2] - kc*u2*w[3]);
         if(dS == 0, error("S not simple at a double zero"));
         nd++; return(chi(ab*z*dG/dS)));
       nb++; 0);
  my(pts = List());
  /* chart t = 1 */
  forvec(cs = vector(2*k, i, [0, p-1]), my(z = sum(i = 1, 2*k, cs[i] * g^(i-1)));
    my(r2 = (a^2 - z^2) / c2 * one, r3 = (b^2 - z^2) / c3 * one, y2, y3);
    if(!issquare(r2, &y2) || !issquare(r3, &y3), next);
    my(U2 = if(y2 == 0, [y2], [y2, -y2]), U3 = if(y3 == 0, [y3], [y3, -y3]));
    for(i = 1, #U2, for(j = 1, #U3, listput(pts, [one, z*one, U2[i], U3[j]]))));
  /* chart t = 0, z = 1 */
  my(r2 = -one / c2, r3 = -one / c3, y2, y3);
  if(issquare(r2, &y2) && issquare(r3, &y3),
    foreach([[y2, y3], [y2, -y3], [-y2, y3], [-y2, -y3]], uu, listput(pts, [0*one, one, uu[1], uu[2]])));
  for(n = 1, #pts, my(v = pts[n], Fv = normalize(apply(c -> c^q, v)));
    for(j = 1, 4, my(sv = normalize([v[1], sig[j][1]*v[2], sig[j][2]*v[3], sig[j][3]*v[4]]));
      if(Fv == sv, Sv[j] += contrib(v); break)));
  my(chars = [[1,1,1,1], [1,1,-1,-1], [1,-1,1,-1], [1,-1,-1,1]]);
  [vector(4, c, -sum(j = 1, 4, chars[c][j] * Sv[j]) / 4), [nb, nd], Sv];
}
rhcheck(t1, t2, p) =
{
  my(b = (t1^2 - t2) / 2, P = 'x^4 - t1*'x^3 + b*'x^2 - p*t1*'x + p^2);
  if(type(b) != "t_INT", return([P, 0]));
  [P, vecmax(abs(abs(polroots(P)) - vector(4, i, sqrt(p))~)) < 1e-8];
}
