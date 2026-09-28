/* Independent numerical check of route_d_weilres_sym.gp on many fibres: the L-polynomial of
   psi3 / psi4 from point counts on D_h (route_d_quotients.gp) must equal that of
   Res_{K/Q}(E_k^d), K = Q(sqrt sigma), with
     psi3: E_3 = X(X^2 - 4b^2 sigma X - 4a^2b^2 sigma^2),  d = al*ga * (-2a(a + sqrt sigma))
     psi4: E_4 = X(X^2 - 4a^2 sigma X - 4a^2b^2 sigma^2),  d = be*ga * 2b(sqrt sigma - b).
   Split p: (x^2 - a_P x + p)(x^2 - a_P' x + p);  inert p: x^4 - a_P x^2 + p^2.            */
\r route_d_quotients.gp
default(parisize, 400000000);
reslpoly(K, E, p) =
{
  my(dec = idealprimedec(K, p));
  if(#dec == 2, prod(i = 1, 2, 'x^2 - ellap(E, dec[i])*'x + p),
     if(dec[1].f == 2, 'x^4 - ellap(E, dec[1])*'x^2 + p^2, error("ramified")));
}
{fibres = [[11,3,65,2,1,1], [19,7,5,82,39,1], [23,11,13,2,3,5], [27,1,146,5,13,1], [39,23,82,1,1,5],
          [31,3,194,5,17,1], [45,37,1,3394,1,1], [33,19,2,29,13,5], [43,1,2,37,33,5], [11,3,2,65,1,1]];}
{my(tot = 0, bad = 0);
 foreach(fibres, fb, my([a, b, al, be, ga, s] = fb, sg = a^2 + b^2, K = nfinit('y^2 - sg), r = Mod('y, 'y^2 - sg), np = 0, nb = 0);
   if(sg != al*be*s^2, error("not a fibre ", fb));
   my(E = [ellinit([0, -4*b^2*sg*al*ga*(-2*a*(a + r)), 0, -4*a^2*b^2*sg^2*(al*ga*(-2*a*(a + r)))^2, 0], K),
           ellinit([0, -4*a^2*sg*be*ga*(2*b*(r - b)), 0, -4*a^2*b^2*sg^2*(be*ga*(2*b*(r - b)))^2, 0], K)]);
   my(N = abs(nfeltnorm(K, E[1].disc) * nfeltnorm(K, E[2].disc)) * a*b*al*be*ga*s*sg);
   forprime(p = 17, 110, if(N % p == 0, next);
     for(hi = 3, 4,
       my(v = iferr(dcount(a, b, al, be, ga, s, hi, p), err, 0));
       if(v == 0, next);                       /* point-count formula degenerate at p */
       my(P1 = lpoly(v[1], v[2], p), P2 = reslpoly(K, E[hi - 2], p));
       np++; if(P1 != P2, nb++; print("   MISMATCH ", fb, " psi", hi, " p=", p, ": ", P1, " vs ", P2))));
   tot += np; bad += nb;
   print(fb, "  sigma = ", sg, " = ", core(sg), " * square:  ", np - nb, " / ", np, " (prime, psi) pairs agree"));
 print(if(bad, "FAILED", "ALL AGREE"), ": ", tot - bad, " of ", tot)}
quit
