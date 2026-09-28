/* L(E/K, 1) for the psi3 / psi4 curves of the fibre 11:3, kernel (65,2,1), K = Q(sqrt 130),
   from the closed forms of Theorem 6.5:  psi3 = Res E_3^(al ga delta_3), psi4 = Res E_4^(be ga delta_4).
   Set before reading this file:  WHICH = 3 or 4;  T0 = vector of split points;  ZCUT = cutoff.
     put  WHICH=3; T0=[1]; ZCUT=24;  in params.gp, then  gp -q params.gp route_d_weilres_lvalue_run.gp
   Validation of the method against PARI's lfun: see route_d_weilres_lvalue_test.gp.            */
\r route_d_weilres_lvalue.gp
default(parisize, 2000000000);
default(parisizemax, 16000000000);
default(realprecision, 15);
{
  my(a = 11, b = 3, al = 65, be = 2, ga = 1, sg = a^2 + b^2, K = nfinit('y^2 - sg), r = Mod('y, 'y^2 - sg));
  my(tw(E, d) = [0, d*E[2], 0, d^2*E[4], d^3*E[5]]);
  my(E3 = [0, -4*b^2*sg, 0, -4*a^2*b^2*sg^2, 0], E4 = [0, -4*a^2*sg, 0, -4*a^2*b^2*sg^2, 0]);
  my(E = if(WHICH == 3, tw(E3, al*ga*(-2*a*(a + r))), tw(E4, be*ga*(2*b*(r - b)))));
  my(EK = ellinit(E, K));
  print("psi", WHICH, " on 11:3 (65,2,1): E = ", lift(E), " over Q(sqrt ", sg, "),  T0 = ", T0, ",  ZCUT = ", ZCUT);
  my(res = lvalue(EK, K, T0, ZCUT));
  for(j = 1, #T0, print("   L(E/K, 1) with t0 = ", T0[j], " :  ", res[1][j]));
}
quit
