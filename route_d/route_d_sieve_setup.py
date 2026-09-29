"""Emit the PARI files for a Mordell-Weil sieve of the cuboid cover W^2 = F on a
Route D fiber, generalizing the 39:37 run.

Usage: python route_d_sieve_setup.py a b al be ga t0 z0 u20 u30 NMAX LMAX tag
Writes route_d_psiF_<tag>.gp and route_d_mwsieve_data_<tag>.gp. The data file
(one line per usable prime) is sieve_data_<tag>.txt, consumed by route_d_mwsieve.py.

Checks built into the generated script (all learned the hard way on 39:37):
 * every discrete log is verified by recomposition (PARI's elllog can silently
   return wrong answers for points outside <g1>);
 * a genuine direct-sum basis <g1> + <h> is built (ellgroup's generators are not
   one in general), with order and bijectivity checks;
 * F o psi is evaluated at a rational-2-torsion translate wherever the explicit
   inverse map has a pole (F o psi is invariant under E[2]-translation: those act
   on the fiber by sign changes fixing F); a point is conservatively "allowed"
   only if every translate fails.
"""
import sys, subprocess, os
sys.set_int_max_str_digits(0)   # exact coordinates can exceed 4300 digits
import sympy as sp
from route_d_fiber_model import build, W_to_fiber

GP = os.environ.get("PARI_GP_PATH", "gp")
ISOG = os.path.join(os.path.dirname(os.path.abspath(__file__)), "route_d_isogpoints.gp").replace("\\", "/")


def main():
    a, b, al, be, ga, t0, z0, u20, u30, NMAX, LMAX = map(int, sys.argv[1:12])
    tag = sys.argv[12]
    s2 = sp.Rational(a * a + b * b, al * be)
    s = sp.sqrt(s2)
    assert s.is_rational, "a^2+b^2 must be alpha*beta times a square"
    kc = al * be * ga * s
    M = build(a, b, al, be, ga, (t0, z0, u20, u30))
    qd = M['qd'].all_coeffs()[::-1]
    c_, d_ = sp.Rational(qd[2]), sp.Rational(qd[1])      # exact; not sp.nsimplify (see route_d_fiber_model)
    q = M['q']
    ab, S2 = a * b, a * a + b * b
    psi = f"""psiF(x, y) = {{
  my(U = (2*({q})*(x + ({c_})) - ({d_})^2/(2*({q})))/y,
     V = -({q}) + U*(U*x - ({d_}))/(2*({q})),
     L = U + ({M['lam0']}),
     z = subst({sp.sstr(M['zl']).replace('lam','LL')}, LL, L),
     u2 = subst({sp.sstr(M['u2l']).replace('lam','LL')}, LL, L),
     u3 = V/(({M['c3']})*subst({sp.sstr(M['den']).replace('lam','LL')}, LL, L)));
  {ab}*z*({S2} - z^2)*({ab}*z - ({kc})*u2*u3);
}}
""".replace('**', '^')
    open(f"route_d_psiF_{tag}.gp", "w").write(psi)
    W = ",".join(sp.sstr(c) for c in M['W'])
    # generators + torsion from PARI
    # default(parisize) must be on its own line: gp discards the rest of that line
    # rank must be proven AND a full set of independent generators found (ellrank can
    # certify the rank without exhibiting every generator; a sieve on a partial set is unsound)
    out = subprocess.run([GP, "-q"], input=f"default(parisize,1000000000);\nEW=ellinit([{W}]); "
                         f"r=ellrank(EW); e=1; while(#r[4] < r[1] && e <= 4, r=ellrank(EW, e, r[4]); e++); "
                         # ellrank can prove the rank yet list fewer points (43:9): 2-isogeny fallback
                         f"read(\"{ISOG}\"); if(r[1] == r[2] && #r[4] < r[1], r[4] = isogpts(EW, r[4], r[1], 8)); "
                         f"if(r[1]!=r[2], error(\"rank not proven\")); "
                         f"if(#r[4] != r[1], error(\"generators incomplete\")); G=ellsaturation(EW,r[4],200); "
                         f"print(G); print(elltors(EW)[3]); print(r[1]);\nquit;\n",
                         capture_output=True, text=True).stdout.strip().splitlines()
    gens, tors, rank = out[-3], out[-2], int(out[-1])
    # exact self-check over Q: psiF (PARI) == F via verified python inverse map, at each generator
    G = [tuple(sp.Rational(v) for v in P.strip("[]").split(", ")) for P in gens.strip("[]").split("], [")]
    chk = [f'read("route_d_psiF_{tag}.gp");']
    for P in G:
        chk.append(f"print(iferr(psiF({P[0]}, {P[1]}), e, \"undef\"));")
    got = subprocess.run([GP, "-q"], input="\n".join(chk) + "\nquit;\n", capture_output=True, text=True).stdout.split()
    for P, g in zip(G, got):
        if g == "undef":
            print("  (formula pole at generator", P, "- skipped in self-check)")
            continue
        _, z, u2, u3 = W_to_fiber(M, P)
        Fpy = sp.Rational(ab * z * (S2 - z**2) * (ab * z - kc * u2 * u3))
        assert sp.Rational(g) == Fpy, (P, g, Fpy)
    print("psiF self-check against the python inverse map: OK")
    ntor = len(tors.strip("[]").split("], ["))
    data = f"""default(parisize, 2000000000);
read("route_d_psiF_{tag}.gp");
EW = ellinit([{W}]);
PTS = concat({gens}, {tors});
NG = {rank}; NT = {ntor};
D = numerator(EW.disc)*denominator(EW.disc)*30*{ab}*{al*be*ga}*{a*a-b*b}*{S2}*lcm(apply(denominator, Vec(EW[1..5])));
red(P, l) = if(denominator(P[1]) % l == 0, [0], [Mod(P[1], l), Mod(P[2], l)]);
dlog(E, P, g1, c1, g2, c2) =
{{
  my(Q = P);
  for(b = 0, c2 - 1,
    my(a = iferr(elllog(E, Q, g1, c1), err, -1));
    if(a >= 0 && ellmul(E, g1, a) == Q, return([a, b]));
    Q = ellsub(E, Q, g2));
  error("dlog failed");
}}
evalF(R, l) =
{{
  if(R == [0], return("bad"));
  my(v = iferr(psiF(lift(R[1])*Mod(1, l), lift(R[2])*Mod(1, l)), err, "bad"));
  if(type(v) == "t_STR" || v == 0, return("bad"));
  v;
}}
allowedQ(R, l, TR, E) =
{{
  my(cands = [R, elladd(E, R, TR[1]), elladd(E, R, TR[2]), elladd(E, R, TR[3])]);
  for(i = 1, 4, my(v = evalF(cands[i], l)); if(type(v) != "t_STR", return(issquare(v))));
  1;
}}
doprime(l, NMAX, fh) =
{{
  my(E = ellinit(EW, l), G = ellgroup(E, , 1), cyc, gg, c1, c2, g1, g2, co, bits, Rb, R, TR);
  cyc = G[2]; gg = G[3];
  if(NMAX % cyc[1] != 0, return(0));
  c1 = cyc[1]; c2 = if(#cyc > 1, cyc[2], 1); g1 = gg[1]; g2 = if(#gg > 1, gg[2], [0]);
  if(ellorder(E, g1) != c1, error(Str("g1 order wrong at l=", l)));
  if(c2 > 1,
    my(m = elllog(E, ellmul(E, g2, c2), g1, c1));
    if(ellmul(E, g1, m) != ellmul(E, g2, c2) || m % c2 != 0, error(Str("SNF step failed at l=", l)));
    g2 = elladd(E, g2, ellmul(E, g1, -(m / c2)));
    if(ellorder(E, g2) != c2, error(Str("h order wrong at l=", l))));
  co = vector(NG + NT, i, dlog(E, red(PTS[i], l), g1, c1, g2, c2));
  for(i = 1, NG + NT, if(elladd(E, ellmul(E, g1, co[i][1]), ellmul(E, g2, co[i][2])) != red(PTS[i], l), error(Str("recompose fail at l=", l))));
  TR = [red(PTS[NG+1], l), red(PTS[NG+2], l), elladd(E, red(PTS[NG+1], l), red(PTS[NG+2], l))];
  bits = vector(c1*c2); Rb = [0];
  for(b = 0, c2 - 1, R = Rb; for(a = 0, c1 - 1, bits[b*c1 + a + 1] = allowedQ(R, l, TR, E); R = elladd(E, R, g1)); Rb = elladd(E, Rb, g2));
  if(#Set(concat(vector(c2, b, vector(c1, a, elladd(E, ellmul(E, g1, a-1), ellmul(E, g2, b-1)))))) != ellcard(E), error(Str("enumeration not bijective at l=", l)));
  write(fh, l, " ", c1, " ", c2, " ", co, " ", concat(apply(x -> Str(x), bits)));
  1;
}}
nl = 0;
forprime(l = 7, {LMAX}, if(D % l == 0, next); nl += doprime(l, {NMAX}, "sieve_data_{tag}.txt"));
print("wrote data for ", nl, " primes (every discrete log verified by recomposition)");
quit;
"""
    open(f"route_d_mwsieve_data_{tag}.gp", "w").write(data)
    import json
    json.dump({"a": a, "b": b, "al": al, "be": be, "ga": ga, "base": [t0, z0, u20, u30], "rank": rank,
               "gens": gens, "tors": tors, "W": W}, open(f"fiber_{tag}.json", "w"))
    print(f"rank {rank}, generators {gens}, torsion {tors}")
    print(f"wrote route_d_psiF_{tag}.gp and route_d_mwsieve_data_{tag}.gp")


if __name__ == "__main__":
    main()
