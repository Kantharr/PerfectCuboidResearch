"""Ground-truth validation of a fiber's sieve data: at actual rational points
P = sum n_i G_i + T (|n_i| <= B), compute F(psi(P)) EXACTLY over Q with the
independently written python inverse map, at every 2-torsion translate where the
explicit formula is regular (all such values must agree -- F o psi is invariant
under E[2]-translation), and compare with every allowed-bit in the data file.
An "unsound" bit (disallowed while F is actually a unit QR mod l) means the data
is wrong. Also returns the exact F values for pattern statistics.
"""
import ast, json, subprocess, os
import sys; sys.set_int_max_str_digits(0)
from itertools import product
import sympy as sp
from route_d_fiber_model import build, W_to_fiber

GP = os.environ.get("PARI_GP_PATH", "gp")


def validate(tag, B=3, timeout=900):
    info = json.load(open(f"fiber_{tag}.json"))
    a, b, al, be, ga = info["a"], info["b"], info["al"], info["be"], info["ga"]
    r = info["rank"]
    M = build(a, b, al, be, ga, tuple(info["base"]))
    kc = al * be * ga * sp.sqrt(sp.Rational(a * a + b * b, al * be))
    ab, S2 = a * b, a * a + b * b
    rng = ",".join([f"[-{B},{B}]"] * r + ["[0,1]", "[0,1]"])
    gp = f"""default(parisize, 2000000000);
EW = ellinit([{info['W']}]); G = {info['gens']}; T = {info['tors']}; TT = [[0], T[1], T[2], elladd(EW, T[1], T[2])];
forvec(v = [{rng}], my(P = [0]); for(i = 1, {r}, P = elladd(EW, P, ellmul(EW, G[i], v[i]))); if(v[{r}+1], P = elladd(EW, P, T[1])); if(v[{r}+2], P = elladd(EW, P, T[2])); \\
  my(s = Str(v)); for(j = 1, 4, my(Q = elladd(EW, P, TT[j])); s = concat(s, if(Q == [0], "|O", concat(["|", Str(Q[1]), ",", Str(Q[2])])))); print(s));
quit;
"""
    out = subprocess.run([GP, "-q"], input=gp, capture_output=True, text=True, timeout=timeout).stdout.strip().splitlines()
    X, Y = sp.symbols('X Y')
    Unum = sp.numer(sp.together(M['Uf']))

    def Freg(x, y):
        if y == 0 or Unum.subs({X: x, Y: y}) == 0:
            return None
        _, z, u2, u3 = W_to_fiber(M, (x, y))
        assert a * a - z**2 - al * ga * u2**2 == 0 and b * b - z**2 - be * ga * u3**2 == 0
        return sp.Rational(ab * z * (S2 - z**2) * (ab * z - kc * u2 * u3))

    data = []
    for line in open(f"sieve_data_{tag}.txt"):
        l, c1, c2, rest = line.strip().split(" ", 3)
        co, bits = rest.rsplit(" ", 1)
        data.append((int(l), int(c1), int(c2), ast.literal_eval(co), bits))
    res = dict(points=0, checked=0, agree=0, conservative=0, unsound=0, inconsistent=0, noreg=0, squares=0)
    Fvals = []
    for line in out:
        parts = line.split("|")
        v = ast.literal_eval(parts[0])
        vals = set()
        for q in parts[1:]:
            if q == "O":
                continue
            x, y = [sp.Rational(c) for c in q.split(",")]
            f = Freg(x, y)
            if f is not None:
                vals.add(f)
        res["points"] += 1
        if not vals:
            res["noreg"] += 1
            continue
        if len(vals) > 1:
            res["inconsistent"] += 1
            continue
        F = next(iter(vals))
        Fvals.append((v, F))
        if F > 0 and sp.sqrt(F).is_rational:
            res["squares"] += 1
        for l, c1, c2, co, bits in data:
            if F.p % l == 0 or F.q % l == 0:
                continue
            A = sum(vi * cc[0] for vi, cc in zip(v, co)) % c1
            Bc = sum(vi * cc[1] for vi, cc in zip(v, co)) % c2
            bit = bits[Bc * c1 + A] == "1"
            leg = sp.legendre_symbol(F.p * pow(F.q, -1, l) % l, l) == 1
            res["checked"] += 1
            if bit == leg:
                res["agree"] += 1
            elif bit:
                res["conservative"] += 1
            else:
                res["unsound"] += 1
    return res, Fvals
