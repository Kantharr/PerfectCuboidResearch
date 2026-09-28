/* Validation of route_d_weilres_lvalue.gp against PARI lfun on small-conductor curves over real
   quadratic fields, including Q(sqrt 130) and two root-number -1 cases (L(1) must vanish). */
\r route_d_weilres_lvalue.gp
default(parisize, 2000000000);
default(parisizemax, 8000000000);
default(realprecision, 28);
{foreach([[130, [0,-1,1,-10,-20]], [130, [0,0,1,-1,0]], [5, [0,0,1,-1,0]]], c,
  my(K = nfinit('y^2 - c[1]), E = ellinit(c[2], K));
  print("E = ", c[2], " over Q(sqrt ", c[1], ")");
  my(r = lvalue(E, K, [1, 1.15, 1.4], 30), ref = lfun(lfuncreate(E), 1));
  print("   series L(1) at t0 = 1, 1.15, 1.4: ", r[1], "\n   PARI lfun:                         ", ref))}
quit
