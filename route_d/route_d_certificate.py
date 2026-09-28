"""Bit-table-independent certificate that a Route D fiber carries no rational point
with F = mS(m-k) a nonzero square (hence no perfect cuboid), for a rank-r fiber
whose generators are saturated at every prime dividing N.

Usage: python route_d_certificate.py a b al be ga t0 z0 u20 u30 tag N
Uses route_d_psiF_<tag>.gp and sieve_data_<tag>.txt (for the list of primes l with
exponent(E(F_l)) | N). Steps:
 1. for every representative sum n_i G_i + T (0 <= n_i < N, T in E[2]) compute F
    exactly over Q (at a 2-torsion translate where the explicit formula is regular;
    all regular translates must agree) and find l with F an l-unit non-residue;
 2. check every killing prime is good: E_W disc nonzero mod l, fiber pencil
    nondegenerate mod l, l divides no coefficient of the model / inverse map;
 3. recompute a random sample of representatives with the independent python
    inverse map and re-verify the killing primes.
"""
import sys, os, random, subprocess
sys.set_int_max_str_digits(0)   # exact coordinates can exceed 4300 digits
import sympy as sp
from route_d_fiber_model import build, W_to_fiber

GP = os.environ.get("PARI_GP_PATH", "gp")


def main():
    a, b, al, be, ga, t0, z0, u20, u30 = map(int, sys.argv[1:10])
    tag, N = sys.argv[10], int(sys.argv[11])
    s = sp.sqrt(sp.Rational(a*a + b*b, al*be)); kc = al*be*ga*s
    ab, S2, c2, c3 = a*b, a*a + b*b, al*ga, be*ga
    M = build(a, b, al, be, ga, (t0, z0, u20, u30))
    W = ",".join(sp.sstr(c) for c in M['W'])
    L = [int(l.split()[0]) for l in open(f"sieve_data_{tag}.txt") if N % int(l.split()[1]) == 0]
    info = subprocess.run([GP, "-q"], input=f"default(parisize,1000000000);\nEW=ellinit([{W}]); "
                          f"r=ellrank(EW); e=1; while(#r[4] < r[1] && e <= 4, r=ellrank(EW, e, r[4]); e++); "
                          f"if(r[1]!=r[2], error(\"rank not proven\")); "
                          f"if(#r[4] != r[1], error(\"generators incomplete\")); G=ellsaturation(EW,r[4],200); "
                          f"print(G); print(elltors(EW)[3]); print(r[1]); "
                          f"print(matdet(ellheightmatrix(EW,r[4]))/matdet(ellheightmatrix(EW,G)));\nquit;\n",
                          capture_output=True, text=True).stdout.strip().splitlines()
    gens, tors, rank, ratio = info[-4], info[-3], int(info[-2]), info[-1]
    print(f"rank {rank} (proven), torsion {tors}, saturated at p<=200 (regulator ratio {ratio}), primes with exponent | {N}: {L}")
    rng = ",".join([f"[0,{N-1}]"] * rank + ["[0,1]", "[0,1]"])
    gp = f"""default(parisize, 2000000000);
read("route_d_psiF_{tag}.gp");
EW = ellinit([{W}]); GS = {gens}; TS = {tors}; TT = [[0], TS[1], TS[2], elladd(EW, TS[1], TS[2])];
L = {L}; fh = "reps_{tag}.txt"; write1(fh, "");
forvec(v = [{rng}], my(P = [0]); for(i = 1, {rank}, P = elladd(EW, P, ellmul(EW, GS[i], v[i]))); if(v[{rank}+1], P = elladd(EW, P, TS[1])); if(v[{rank}+2], P = elladd(EW, P, TS[2])); \\
  my(fs = List(), qs = List()); for(j = 1, 4, my(Q = elladd(EW, P, TT[j])); if(Q == [0], next); my(y = iferr(psiF(Q[1], Q[2]), e, "u")); if(type(y) != "t_STR", listput(fs, y); listput(qs, Q))); \\
  if(#fs == 0, write(fh, v, " NOREG"); next); if(#Set(Vec(fs)) > 1, error(Str("translate values disagree at ", v))); \\
  my(f = fs[1], kill = 0); \\
  for(i = 1, #L, my(l = L[i]); if(valuation(f, l) != 0 || issquare(Mod(f, l)), next); \\
    for(j = 1, #qs, my(Q = qs[j]); if(denominator(Q[1]) % l == 0 || denominator(Q[2]) % l == 0, next); \\
      my(r = iferr(psiF(Mod(numerator(Q[1]), l)/Mod(denominator(Q[1]), l), Mod(numerator(Q[2]), l)/Mod(denominator(Q[2]), l)), e, "u")); \\
      if(type(r) != "t_STR" && r != 0 && r == Mod(f, l), kill = l; break)); if(kill, break)); \\
  write(fh, v, " ", kill, " ", issquare(f)));
quit;
"""
    open(f"reps_{tag}.gp", "w").write(gp)
    if os.path.exists(f"reps_{tag}.txt"):
        os.remove(f"reps_{tag}.txt")          # PARI's write/write1 append, never truncate
    subprocess.run([GP, "-q", f"reps_{tag}.gp"], stdin=subprocess.DEVNULL, capture_output=True, text=True)
    rows = []
    for l in open(f"reps_{tag}.txt"):
        v, rest = l.split("]", 1)
        rows.append(((v + "]").replace(" ", ""), rest.split()))
    total = len(rows)
    noreg = sum(1 for _, r in rows if r[0] == "NOREG")
    nokill = [v for v, r in rows if r[0] != "NOREG" and r[0] == "0"]
    sq = [v for v, r in rows if r[0] != "NOREG" and r[1] == "1"]
    expected = N**rank * 4
    print(f"representatives: {total} (expected {expected}); no regular translate: {noreg}; with no killing prime: {len(nokill)}; F a rational square: {len(sq)}")
    killers = sorted({int(r[0]) for _, r in rows if r[0] not in ("NOREG", "0")})
    # step 2: good reduction at every killing prime
    qd = M['qd'].all_coeffs()[::-1]
    lam = sp.Symbol('lam')
    consts = [M['q'], qd[1], qd[2], M['lam0'], M['c3']] + list(M['W'])
    for f in (M['zl'], M['u2l'], M['den']):
        consts += list(sp.Poly(sp.numer(sp.together(f)), lam).coeffs()) + list(sp.Poly(sp.denom(sp.together(f)), lam).coeffs())
    # what matters: no l in any coefficient DENOMINATOR, and l does not divide q
    # (the inverse formula divides by q); numerators divisible by l are harmless.
    bad = set(sp.factorint(abs(sp.Rational(M['q']).p)))
    for c in consts:
        bad |= set(sp.factorint(sp.Rational(c).q))
    disc = subprocess.run([GP, "-q"], input=f"EW=ellinit([{W}]); print(EW.disc);\nquit;\n", capture_output=True, text=True).stdout.strip()
    disc = sp.Rational(disc)
    good = all(l not in bad and disc.p % l and disc.q % l and all(x % l for x in (a*a, b*b, c2, c3, a*a - b*b, S2))
               for l in killers)
    print(f"killing primes {killers}: good reduction for model, inverse map, and fiber pencil: {good}")
    # step 3: independent recomputation of a sample
    random.seed(1)
    pick = random.sample([(v, r) for v, r in rows if r[0] != "NOREG"], min(60, total))
    lines = [f"default(parisize,2000000000);", f"EW=ellinit([{W}]); GS={gens}; TS={tors}; TT=[[0],TS[1],TS[2],elladd(EW,TS[1],TS[2])];"]
    for v, r in pick:
        lines.append(f"v={v}; P=[0]; for(i=1,{rank},P=elladd(EW,P,ellmul(EW,GS[i],v[i]))); if(v[{rank}+1],P=elladd(EW,P,TS[1])); if(v[{rank}+2],P=elladd(EW,P,TS[2])); "
                     f"for(j=1,4, Q=elladd(EW,P,TT[j]); if(Q!=[0], print(v,\"|\",Q[1],\"|\",Q[2])));")
    out = subprocess.run([GP, "-q"], input="\n".join(lines) + "\nquit;\n", capture_output=True, text=True).stdout.strip().splitlines()
    X, Y = sp.symbols('X Y'); Unum = sp.numer(sp.together(M['Uf']))
    Fs = {}
    for line in out:
        v, x, y = [s.strip() for s in line.split("|")]
        x, y = sp.Rational(x), sp.Rational(y)
        if y == 0 or Unum.subs({X: x, Y: y}) == 0:
            continue
        _, z, u2, u3 = W_to_fiber(M, (x, y))
        assert a*a - z**2 - c2*u2**2 == 0 and b*b - z**2 - c3*u3**2 == 0
        Fs.setdefault(v.replace(" ", ""), set()).add(sp.Rational(ab*z*(S2 - z**2)*(ab*z - kc*u2*u3)))
    kill = {v: int(r[0]) for v, r in pick}
    ok = 0
    for v, S in Fs.items():
        assert len(S) == 1, ("translates disagree", v)
        F = next(iter(S)); l = kill[v]
        assert l and F.p % l and F.q % l and sp.legendre_symbol(F.p * pow(F.q, -1, l) % l, l) == -1, v
        ok += 1
    print(f"independent python recomputation: {ok} of {len(pick)} sampled representatives confirmed")
    verdict = (total == expected and noreg == 0 and not nokill and not sq and good and ok == len(pick))
    print("CERTIFICATE:", "VALID - no rational point of this fiber has F a nonzero square" if verdict else "NOT ESTABLISHED")


if __name__ == "__main__":
    main()
