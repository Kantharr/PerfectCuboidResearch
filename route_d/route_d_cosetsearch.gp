/* Step A of the missing-generator plan (referee_notes, 2026-10-02): search the 2-coverings of EVERY
   class in the coset Sel2 \ span(d(G1), d(T1), d(T2)), not only ell2cover's basis covers.

   E = E_{a,b}: Y^2 = X(X - e2)(X - e3), e2 = a^2 s, e3 = b^2 s, s = a^2 + b^2; Kummer map
   P -> (X, X - e2) mod squares.  The 2-covering of a class (d1, d2), d3 = core(d1 d2), is
       X = d1 U^2,  X - e2 = d2 V^2,  X - e3 = d3 W^2   (affine),
   so  d2 V^2 - d3 W^2 = (e3 - e2) T^2  is a conic.  Parametrise it (qfsolve, qfparam) as
   (V, W, T) = M (x^2, x, 1); then d1 U^2 = e2 T^2 + d2 V^2 gives the quartic
       y^2 = Q(x) = d1 (e2 T(x)^2 + d2 V(x)^2)        (y = d1 U T-scaled),
   which is made integral, minimised (hyperellminimalmodel) and reduced (hyperellred) before
   hyperellratpoints.  A point maps back to x by the Mobius maps of the two reductions, and then
   to X = e2 + d2 (V/T)^2 on E.

   cosetgens(a, b, SEL, H): SEL = the 2-Selmer group as a list of classes [d1, d2] (from
   route_d_selmer_lines.py).  Returns [status, G] with G a full set of saturated generators when
   one is found.

   Tested 2026-10-02: correct (on 43:9 every class in the known span yields points with exactly that
   Kummer class), but the 8 coset classes of 43:9, 49:5 and 79:11 have no point up to height 1e6
   (43:9's G2 is found in 2 s on a 2-cover of an isogenous curve instead). So on these lines the
   missing generators are large on every 2-covering of E; see the Step B (4-descent) plan.     */
\r route_d_fiber_descent.gp

mobius(m, x0) = my(M = m[2], den = M[2,1]*x0 + M[2,2]); if(den == 0, "inf", (M[1,1]*x0 + M[1,2]) / den);

covpts(e2, e3, d1, d2, H) =
{
  my(d3 = core(d1*d2), G = matdiagonal([d2, -d3, -(e3 - e2)]), s = qfsolve(G), out = List());
  if(type(s) != "t_COL", return([]));
  my(M = qfparam(G, s), v = M * ['x^2, 'x, 1]~, Q = d1*(e2*v[3]^2 + d2*v[1]^2));
  Q = Q * denominator(content(Q))^2;                      /* integral; a square factor only */
  my(c = content(Q), cs = core(c)); Q = Q / (c / cs);      /* strip the square part of the content */
  if(!issquarefree(Q) || poldegree(Q) < 3, return([]));
  my(m1, m2, Qm = hyperellminimalmodel(Q, &m1), Qr = hyperellred(Qm, &m2));
  if(type(Qr) == "t_VEC", Qr = Qr[1] + Qr[2]^2/4);
  my(pts = iferr(hyperellratpoints(Qr, H), err, []));
  foreach(pts, p,
    my(x1 = mobius(m2, p[1])); if(x1 == "inf", next);
    my(x0 = mobius(m1, x1)); if(x0 == "inf", next);
    my(V = subst(v[1], 'x, x0), T = subst(v[3], 'x, x0));
    if(T == 0, next);
    my(X = e2 + d2*(V/T)^2, Y2 = X*(X - e2)*(X - e3), Y);
    if(!issquare(Y2, &Y), error("covpts: point does not lift to E at class ", [d1, d2]));
    listput(out, [X, Y]));
  Vec(out);
}

cosetgens(a, b, SEL, H) =
{
  my(s = a^2 + b^2, e = [0, a^2*s, b^2*s], E = ellinit([0, -(e[2] + e[3]), 0, e[2]*e[3], 0]));
  my(rk = ellrank(E, 4)); if(rk[1] != rk[2], return(["rank not proven", []]));
  my(G = rk[4]); if(#G >= rk[1], return(["already complete", ellsaturation(E, G, 1000)]));
  my(T = elltors(E)[3], known = concat(G, T), imgs = apply(P -> kum(E, P, e), known));
  /* coset: Selmer classes outside the span of the known images */
  my(PR = Set(concat(apply(v -> concat(primesof(v[1]), primesof(v[2])), concat(imgs, SEL)))));
  my(Mk = matconcat(apply(v -> concat(sqvec(v[1], PR), sqvec(v[2], PR))~, imgs)));
  my(coset = [c | c <- SEL, type(matsolvemod(Mk, 2, concat(sqvec(c[1], PR), sqvec(c[2], PR))~)) == "t_INT"]);
  my(tried = 0, found = 0);
  foreach(coset, c,
    tried++;
    foreach(covpts(e[2], e[3], c[1], c[2], H), P,
      if(#G < rk[1] && indep(E, concat(G, [P])), G = concat(G, [P]); found = c));
    if(#G >= rk[1], break));
  if(#G < rk[1], return([Str("not found in ", tried, " of ", #coset, " coset classes"), G]));
  [Str("found at class ", found, " (", tried, " of ", #coset, " classes tried)"), ellsaturation(E, G, 1000)];
}
