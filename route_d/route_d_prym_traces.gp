/* Frobenius traces on the four Prym surfaces A_psi of the cuboid cover C -> E of a Route D
   fiber, over F_q (q = p^k), via twisted point counts:
     tr(Frob_q | V_psi) = -(1/4) sum_T psi(T) S_T,
     S_T = sum over P in E(F_{q^2}) with Frob_q(P) = P + T of chi_q(F(psi(P))).
   F o psi is E[2]-invariant, so it is evaluated at a 2-torsion translate wherever the explicit
   formula has a pole; a point where every translate fails is a zero/pole of F (chi = 0). */
prymtraces(EW, TS, p, k = 1) =
{
  my(q = p^k, g = ffgen([p, 2*k], 'w), E = ellinit(EW, g), T1 = [TS[1][1] * g^0, TS[1][2] * g^0], T2 = [TS[2][1] * g^0, TS[2][2] * g^0]);
  my(TT = [[0], T1, T2, elladd(E, T1, T2)], S = vector(4), bad = 0);
  my(chi(v) = my(c = v^((q - 1) / 2)); if(c == 1, 1, if(c == -1, -1, "bad")));
  my(Fval(P) = my(v = "u"); for(m = 1, 4, my(Q = elladd(E, P, TT[m])); if(Q != [0], v = iferr(psiF(Q[1], Q[2]), e, "u"); if(type(v) != "t_STR" && v != 0, return(v)))); "u");
  my(elts = ffgen([p, 2*k], 'w)); 
  my(N = p^(2*k), base = vector(2*k, i, g^(i-1)));
  forvec(cs = vector(2*k, i, [0, p-1]), my(x = sum(i = 1, 2*k, cs[i] * base[i]), ys = ellordinate(E, x));
    for(t = 1, #ys, my(P = [x, ys[t]], FP = [x^q, ys[t]^q]);
      for(j = 1, 4, if(FP == elladd(E, P, TT[j]),
        my(v = Fval(P)); if(type(v) != "t_STR", my(c = chi(v)); if(type(c) == "t_STR", bad++, S[j] += c));
        break))));
  my(v = Fval([0])); if(type(v) != "t_STR", my(c = chi(v)); if(type(c) == "t_STR", bad++, S[1] += c));
  my(chars = [[1,1,1,1], [1,-1,1,-1], [1,1,-1,-1], [1,-1,-1,1]]);
  [vector(4, c, -sum(j = 1, 4, chars[c][j] * S[j]) / 4), bad, S];
}
/* characteristic polynomial of Frob_p on V_psi from the traces over F_p and F_{p^2};
   RH check: all roots of absolute value sqrt(p). */
rhcheck(t1, t2, p) =
{
  my(b = (t1^2 - t2) / 2, P = x^4 - t1*x^3 + b*x^2 - p*t1*x + p^2);
  if(type(b) != "t_INT", return([P, 0]));
  [P, vecmax(abs(abs(polroots(P)) - vector(4, i, sqrt(p))~)) < 1e-8];
}
