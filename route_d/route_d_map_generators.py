import sys
from math import gcd, isqrt
from sympy import Rational, simplify, sqrt as ssqrt

sys.path.insert(0, '.')
from route_d_inverse_map import FiberXY, FiberYZ, find_r, pari_point_to_m

def analyze_xyz(x, y, z):
    if x is None:
        return None
    x, y, z = abs(x), abs(y), abs(z)
    if not (x > y > z > 0):
        x, y, z = sorted([x, y, z], reverse=True)
        if not (x > y > z > 0):
            return {"valid": False, "reason": "ordering/zero"}
    R = (x*x+y*y)*(x*x-z*z)*(y*y-z*z)
    if R <= 0:
        return {"valid": False, "reason": "R<=0"}
    k = isqrt(R)
    if k*k != R:
        return {"valid": False, "reason": "R not perfect square"}
    if gcd(gcd(x, y), z) != 1:
        return {"valid": False, "reason": "not primitive"}
    if y*y == x*z:
        return {"valid": False, "reason": "family A (y^2=xz)"}
    m = x*y*z
    h = gcd(m, k)
    m1, k1 = m//h, k//h
    Qpos = m > k
    S = x*x+y*y-z*z
    d = m1-k1
    dS = (d > 0 and S % d == 0)
    e = S//d if dS else None
    m1sq = isqrt(m1)**2 == m1
    esq = (e is not None) and isqrt(e)**2 == e
    result = {"valid": True, "x": x, "y": y, "z": z, "Qpos": Qpos, "m1": m1, "m1sq": m1sq, "dS": dS}
    if dS:
        result["e"] = e
        result["esq"] = esq
    # A^2 = m*S/(m-k)  -- the actual cuboid-existence test
    if m != k:
        from fractions import Fraction
        A2 = Fraction(m*S, m-k)
        if A2 > 0 and A2.denominator == 1:
            a2int = A2.numerator
            asq = isqrt(a2int)
            result["A2"] = a2int
            result["A2_is_perfect_square"] = (asq*asq == a2int)
        else:
            result["A2"] = A2
            result["A2_is_perfect_square"] = False
    return result

fibers_data = [
    dict(label="39:37", kind="xy", alpha=5, beta=2, gamma=19, ab=(39,37),
         seed=(39,37,1), center=(6747,6401,6253),
         ainvs=(0,-115540,0,3326975600,66585736000),
         gens=[(26620,5061600), (Rational(942580,9),Rational(409427200,27)), (Rational(3202480,49),Rational(608657400,343))]),
    dict(label="13:9", kind="xy", alpha=5, beta=2, gamma=11, ab=(13,9),
         seed=(403,279,117), center=(923,639,351),
         ainvs=(0,-8788660,0,15190141215600,4838036478302664000),
         gens=[(-173836,1388022272),(725660,3408090400)]),
    dict(label="93:71", kind="xy", alpha=5, beta=2, gamma=11, ab=(93,71),
         seed=(93,71,27), center=(93,71,39),
         ainvs=(0,-503860,0,54429087600,903784206024000),
         gens=[(14580,39916800),(46260,49420800)]),
    dict(label="223:211", kind="xy", alpha=754, beta=5, gamma=3, ab=(223,211),
         seed=(25199,23843,13603), center=(65339,61823,49733),
         ainvs=(0,-13962810814420,0,37288083563348237452492400,81921104814210451145960529893366152000),
         gens=[(6765178357740,2182430406233638400),(8212244436240,562362956411565400),(16753238278140,38598047881679156000)]),
    dict(label="287:109", kind="xy", alpha=13, beta=290, gamma=11, ab=(287,109),
         seed=(218981,83167,80557), center=(324023,123061,53519),
         ainvs=(0,-680640065777620,0,1635025640789790756877900400,1826721191865659280140465521065102687112000),
         gens=[(-21562190086060,1210368926725665907200),(688395234089940,2574363268605019091200),
               (1623659117154220,49905242909073077803200),(Rational(-105584860382495,4),Rational(9089520940107952118775,8))]),
    dict(label="257:93", kind="xy", alpha=34, beta=13, gamma=1, ab=(257,93),
         seed=(15163,5487,2313), center=(151373,54777,54573),
         ainvs=(0,-445533850996,0,17356089895647328700784,92154437757404471195547807779136),
         gens=[(42763316596,9889965955833600),(Rational(232450328916,121),Rational(14812998835093056000,1331)),
               (1455978013,10792735278869649),(Rational(554570092014484,729),Rational(8707355030060940780800,19683))]),
    dict(label="311:273", kind="xy", alpha=137, beta=2, gamma=19, ab=(311,273),
         seed=(2799,2457,2407), center=(15239,13377,12161),
         ainvs=(0,-5678131044,0,-9483938218937938704,59129025486633598276503757376),
         gens=[(-1119488924,247440972759552),(5496897580,38995631771616),(12027970348,929355098162400)]),
    dict(label="53:49_yz", kind="yz", alpha=5, beta=34, gamma=3, ab=(53,49),
         seed=(2597,2279,2107), center=(4109,3233,2989),
         ainvs=(0,4435370244,0,2687632115455841904,-2093816872435291837382735424),
         gens=[(-1795678584,39895413634440),(-1452689084,17212146041440),(6180885228,648147027661056),
               (Rational(-1161669149732,841),Rational(111424548613865984,24389))]),
]

def find_seed_m(fib, kind, seed_xyz, alpha, beta, gamma):
    """Find the parametrization value m corresponding to a known point,
    handling the t0-chart scaling and (for xy) alpha/beta assignment swap."""
    from sympy import symbols, solve as ssolve
    x, y, z = seed_xyz
    if kind == "xy":
        t = gcd(x, y)
        u2 = isqrt((x*x-z*z)//(alpha*gamma))
        u3 = isqrt((y*y-z*z)//(beta*gamma))
        if not (alpha*gamma*u2*u2 == x*x-z*z and beta*gamma*u3*u3 == y*y-z*z):
            return None  # assignment mismatch (alpha/beta swapped for this point)
        scale = Rational(fib.t0, t)
        sols = ssolve(fib.W2_of_m - u2*scale, fib.m_sym)
        for mv in sols:
            if simplify(fib.W3_of_m.subs(fib.m_sym, mv) - u3*scale) == 0:
                return mv
        return None
    else:
        t = gcd(y, z)
        u1 = isqrt((x*x+y*y)//(alpha*beta))
        u2 = isqrt((x*x-z*z)//(alpha*gamma))
        if not (alpha*beta*u1*u1 == x*x+y*y and alpha*gamma*u2*u2 == x*x-z*z):
            return None
        scale = Rational(fib.t0, t)
        sols = ssolve(fib.U1_of_m - u1*scale, fib.m_sym)
        for mv in sols:
            if simplify(fib.U2_of_m.subs(fib.m_sym, mv) - u2*scale) == 0:
                return mv
        return None

for fd in fibers_data:
    print(f"\n{'='*70}\n=== {fd['label']}  kernel=({fd['alpha']},{fd['beta']},{fd['gamma']}) ===")
    if fd["kind"] == "xy":
        fib = FiberXY(fd["alpha"], fd["beta"], fd["gamma"], *fd["ab"], fd["seed"])
    else:
        fib = FiberYZ(fd["alpha"], fd["beta"], fd["gamma"], *fd["ab"], fd["seed"])

    seed_m = find_seed_m(fib, fd["kind"], fd["center"], fd["alpha"], fd["beta"], fd["gamma"])
    if seed_m is None:
        print("  'center' point has mismatched alpha/beta assignment -- searching for a synthetic")
        print("  centering value m0 (need not correspond to a known triple, just quartic(m0)=square):")
        from sympy import Rational as R, sqrt as sy_sqrt
        found = None
        # check m0=0 first -- trivial, cheap, and easy to miss (it was wrongly excluded before)
        val0 = fib.quartic_val(R(0))
        if val0 >= 0 and sy_sqrt(val0).is_rational:
            found = R(0)
            print(f"  trivial candidate m0=0 works directly: quartic(0)={val0} is a perfect square")
        if found is None:
            for num in list(range(-200, 201)):
                for den in range(1, 20):
                    m0 = R(num, den)
                    if m0 == 0:
                        continue
                    val = fib.quartic_val(m0)
                    if val < 0:
                        continue
                    s = sy_sqrt(val)
                    if s.is_rational:
                        found = m0
                        break
                if found is not None:
                    break
        if found is None:
            print("  no synthetic centering point found in search range -- skipping fiber")
            continue
        seed_m = found
        print(f"  synthetic centering m0 = {seed_m}  (quartic(m0)={fib.quartic_val(seed_m)}, a perfect square)")
    else:
        print(f"  centering m = {seed_m}")

    a2t, a4t, a6t = fd["ainvs"][1], fd["ainvs"][3], fd["ainvs"][4]
    try:
        r, _ = find_r(*fib.build_weierstrass_and_shift(seed_m), target_a2=a2t, target_a4=a4t, target_a6=a6t)
    except Exception as e:
        print("  find_r FAILED:", e)
        continue
    print(f"  r = {r}")

    for gi, (Xg, Yg) in enumerate(fd["gens"]):
        try:
            m_rec = pari_point_to_m(fib, seed_m, r, Rational(Xg), Rational(Yg))
            xyz = fib.m_to_xyz(m_rec)
        except Exception as e:
            print(f"  generator {gi}: ERROR {e}")
            continue
        print(f"  generator {gi} = ({Xg},{Yg})  ->  m={m_rec}  ->  (x,y,z)={xyz}")
        if xyz is not None:
            res = analyze_xyz(*xyz)
            print(f"      analysis: {res}")
