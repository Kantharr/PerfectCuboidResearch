/* Explicit genus-3 quotients of the cuboid cover C over a Route D fiber.
   E[2]-invariants on the fiber (chart t = 1): x = z^2, y = z*u2*u3.  Quotient elliptic curve
     E':  c2*c3*y^2 = x*(a^2 - x)*(b^2 - x),       (c2 = al*ga, c3 = be*ga)
   and F = ab*(S2 - x)*(ab*x - kc*y) is a function on E'.  K(C)/K(E') is (Z/2)^3; its quadratic
   subfields are the three isogenous genus-1 curves K(E')(sqrt h), h in {x, (a^2-x)/c2, (b^2-x)/c3},
   and the four genus-3 curves  D_h: W^2 = h*F,  h in {1, x, (a^2-x)/c2, (b^2-x)/c3}.
   Jac(D_h) ~ E' x P_h over Q.  dcount returns the Frobenius data of P_h at p:
   [a1, s2] with a1 = tr(Frob_p), s2 = tr(Frob_p^2), from point counts over F_p and F_{p^2}. */
dnpts(a, b, al, be, ga, s, hi, p, k) =
{
  my(c2 = al*ga, c3 = be*ga, S2 = a^2 + b^2, kc = al*be*ga*s, ab = a*b, cc = c2*c3);
  my(g = ffgen([p, k], 'w), one = g^0, q = p^k);
  my(chi(v) = my(c = v^((q - 1) / 2)); if(c == 1, 1, if(c == -1, -1, error("chi"))));
  my(gx(x) = x*(a^2 - x)*(b^2 - x), dg(x) = a^2*b^2 - 2*(a^2 + b^2)*x + 3*x^2);
  my(h(x) = [one, x, (a^2 - x)/c2, (b^2 - x)/c3][hi]);
  my(hroot = [-1, 0, a^2, b^2][hi], hc = [1, 1, -c2, -c3][hi]);   /* h = (x - hroot)/hc */
  my(nD = 1, nE = 1);                                               /* the point at infinity */
  forvec(cs = vector(k, i, [0, p - 1]), my(x = sum(i = 1, k, cs[i] * g^(i - 1)), r = gx(x) / cc * one, y);
    if(!issquare(r, &y), next);
    my(Y = if(y == 0, [y], [y, -y]));
    nE += #Y;
    for(j = 1, #Y, my(yy = Y[j], F = ab*(S2 - x)*(ab*x - kc*yy), v = h(x) * F);
      if(v != 0, nD += 1 + chi(v); next);
      if(x == S2 && ab*S2 == kc*yy,                               /* double zero of F */
        my(yp = dg(x) / (2*cc*yy), res = -ab*(ab - kc*yp) * h(x));
        if(res == 0, error("degenerate double zero")); nD += 1 + chi(res); next);
      if(yy == 0 && x == hroot && hi > 2,                          /* double zero of h */
        my(F0 = ab*(S2 - x)*(ab*x), res = cc / (hc * dg(x)) * F0);
        if(res == 0, error("degenerate h zero")); nD += 1 + chi(res); next);
      nD += 1));
  [nD, nE];
}
dcount(a, b, al, be, ga, s, hi, p) =
{
  my(n1 = dnpts(a, b, al, be, ga, s, hi, p, 1), n2 = dnpts(a, b, al, be, ga, s, hi, p, 2));
  my(tD1 = p + 1 - n1[1], tE1 = p + 1 - n1[2], tD2 = p^2 + 1 - n2[1], tE2 = p^2 + 1 - n2[2]);
  [tD1 - tE1, tD2 - tE2, tE1];
}
lpoly(a1, s2, p) = my(b = (a1^2 - s2) / 2); 'x^4 - a1*'x^3 + b*'x^2 - p*a1*'x + p^2;
rh(P, p) = vecmax(abs(abs(polroots(P)) - vector(4, i, sqrt(p))~)) < 1e-8;
