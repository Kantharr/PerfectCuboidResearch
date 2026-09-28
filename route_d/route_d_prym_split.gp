/* Explicit elliptic factors of the Prym surfaces via an involution of E' permuting the branch points.
   E': y^2 = kx(x) = x(x - a^2)(x - b^2)/(c2 c3);  D_h: W^2 = h*F,  F = ab(S2 - x)(ab x - kc y).
   Reflection r(P) = T - P.  u = slope of the line through -T and P is r-invariant of degree 2, so
   K(E')^r = Q(u).  With Tr = hF(P) + hF(rP) and Nm = hF(P) hF(rP) in Q(u): if Nm = c*M^2 then r lifts
   to D_h over Q(sqrt c), and the two genus-1 quotients are  V^2 = Tr +- 2 sqrt(c) M.                  */
splitdata(a, b, al, be, ga, s, T, hi) =
{
  my(c2 = al*ga, c3 = be*ga, S2 = a^2 + b^2, kc = al*be*ga*s, ab = a*b);
  my(kx = 'x*('x - a^2)*('x - b^2)/(c2*c3), xT = T[1], yT = T[2]);
  my(h = [1, 'x, (a^2 - 'x)/c2, (b^2 - 'x)/c3][hi]);
  my(yl = 'u*('x - xT) - yT, cub = yl^2 - kx, Q = cub / ('x - xT));
  if(type(Q) != "t_POL" || poldegree(Q, 'x) != 2, error("T not on curve?"));
  my(Fm = Mod(h*ab*(S2 - 'x)*(ab*'x - kc*yl), Q));
  my(Tr = trace(Fm), Nm = norm(Fm));
  [Tr, Nm];
}
/* write Nm = c * M^2 with c squarefree in Q, M in Q(u) */
sqpart(R) =
{
  my(n = numerator(R), d = denominator(R), fn = factor(n), fd = factor(d), c = content(n)/content(d), M = 1, rest = 1);
  n = n/content(n); d = d/content(d);
  fn = factor(n); fd = factor(d);
  for(i = 1, #fn~, if(poldegree(fn[i,1]) > 0, M *= fn[i,1]^(fn[i,2]\2); rest *= fn[i,1]^(fn[i,2]%2)));
  for(i = 1, #fd~, if(poldegree(fd[i,1]) > 0, M /= fd[i,1]^((fd[i,2]+1)\2); rest *= fd[i,1]^(fd[i,2]%2)));
  my(cc = core(abs(numerator(c)*denominator(c))), q = sqrtint(abs(numerator(c)*denominator(c)) / abs(cc)) / denominator(c));
  [sign(c)*cc, M*q, rest];
}
/* squarefree polynomial kernel of a rational function R (so V^2 = R ~ V^2 = sqf) */
sqfker(R) =
{
  my(n = numerator(R) * denominator(R), c = content(n), f, P = 1);
  n /= c; f = factor(n);
  for(i = 1, #f~, if(f[i,2] % 2, P *= f[i,1]));
  core(numerator(c) * denominator(c)) * P;
}
/* the two quotient curves for reflection T, twist hi (only when c = 1) */
quotcurves(a, b, al, be, ga, s, T, hi) =
{
  my(d = splitdata(a, b, al, be, ga, s, T, hi), sp = sqpart(d[2]));
  if(sp[3] != 1, error("Nm not c*square"));
  if(sp[1] != 1, return([sp[1]]));
  my(M = sp[2]);
  vector(2, e, my(q = sqfker(d[1] + 2*(-1)^(e+1)*M)); [q, if(poldegree(q) <= 4 && poldegree(q) >= 3, ellinit(ellfromeqn('y^2 - subst(q, 'u, 'x))), 0)]);
}
