import sys, re
from math import gcd, isqrt
from fractions import Fraction
from sympy import Rational, simplify, sqrt as ssqrt

sys.path.insert(0, '.')
from route_d_inverse_map import FiberXY, find_r, pari_point_to_m

def analyze_xyz(x, y, z):
    x, y, z = abs(x), abs(y), abs(z)
    if not (x > y > z > 0):
        return {"valid": False, "reason": "ordering"}
    R = (x*x+y*y)*(x*x-z*z)*(y*y-z*z)
    if R <= 0:
        return {"valid": False, "reason": "R<=0"}
    k = isqrt(R)
    if k*k != R:
        return {"valid": False, "reason": "R not square"}
    if gcd(gcd(x, y), z) != 1:
        return {"valid": False, "reason": "not primitive"}
    if y*y == x*z:
        return {"valid": True, "family_A": True}
    m = x*y*z
    h = gcd(m, k)
    m1, k1 = m//h, k//h
    Qpos = m > k
    S = x*x+y*y-z*z
    m1sq = isqrt(m1)**2 == m1
    result = {"valid": True, "family_A": False, "Qpos": Qpos, "m1": m1, "m1sq": m1sq}
    if m != k:
        A2 = Fraction(m*S, m-k)
        a2sq = A2 > 0 and A2.denominator == 1 and isqrt(A2.numerator)**2 == A2.numerator
        result["A2_is_perfect_square"] = a2sq
        if a2sq:
            result["A2_VALUE"] = A2.numerator
    return result

# (label, kernel, ab, seed, ainvs, generators)
fibers = [
    ("139:97", (5,34,177), (139,97), (41561,29003,25159),
     (0,-1100938909780,0,59037414405677731276400,73664403564859300874766645330568000),
     [(-155098363140,185184205004999200), (-114964466220,225403665333433600), (1531362100860,1083256444833815200)]),
    ("67:55", (2,13,183), (67,55), (57017,46805,39083),
     (0,-327644197972,0,6054193795615126434416,3049090020941356031819988035875648),
     [(-35368617388,48794002028229120), (120131821332,27957904515188480)]),
    ("125:79", (13,2,3), (125,79), (241375,152549,145825),
     (0,-5162111977204,0,-419915483924927672890000,7199674160601064400922923602525000000),
     [(1162801799900,1141882783602693600), (543174940725,2368294735296291725)]),
    ("193:179", (2,205,21), (193,179), (170033,157699,150539),
     (0,-32451024249940,0,-308226818474986344338304400,11895368451862306573535261548572349576000),
     [(Rational(564879093250416,169),Rational(225553064567751504701144,2197)),
      (Rational(461773629232149,25),Rational(4730986465175179728893,125))]),
    ("157:101", (34,41,129), (157,101), (87449,56257,47975),
     (0,-41038114948900,0,102302961145933564234909424,2610476119170858304497084560087100520000),
     [(Rational(229501615946889324,20449),Rational(5217919959616137690988960,2924207)),
      (Rational(151619991868704,25),Rational(5512119840142478436392,125))]),
    ("73:39", (1,274,1), (73,39), (80081,42783,42705),
     (0,-6036522619300,0,-962035320238069267032336,6065980654384958700580006088391220800),
     [(7202355277988,7720969651908251648), (7670933860772,9739625346199330816),
      (Rational(14031565314624,25),Rational(243709394771157669432,125))]),
    ("127:67", (61,2,15), (127,67), (124079,65459,61849),
     (0,-6803954991604,0,395145728219000176183664,7109462201858399065012226558447489344),
     [(1112465280140,710900810396876352), (8670700806492,12283304427315100192)]),
    ("151:143", (2,865,21), (151,143), (396073,375089,367081),
     (0,-660464787786820,0,-211073161901771522984539651600,146501125927410295345474147480785431135272000),
     [(749780012613060,6201051030846108236800),
      (Rational(1175909250900384,25),Rational(1453529374995576228788152,125)),
      (Rational(5674433776151140,9),Rational(33139614333604151859200,27))]),
    ("47:21", (2,53,13), (47,21), (126195,56385,55007),
     (0,-6175895458836,0,-55512222328542933268368,2769564316939131225295190277905291072),
     [(482217311056,1191144094991974872), (214957434512,1575498741691105000)]),
    ("347:215", (2,493,33), (347,215), (836617,518365,510883),
     (0,-2276193298892692,0,-212332855765914940826671717264,630049721129930566160600107707937274355834688),
     [(3305582977026108,105717463633571775437920),
      (Rational(-572516604163216132,18769),Rational(64764429970358527466519029920,2571353)),
      (Rational(2435588918587636,25),Rational(3032851469234914090089216,125))]),
    ("47:23", (1,2,15), (47,23), (115103,56327,53897),
     (0,-96512812996,0,42300177551974417904,15090876047918571821364372759616),
     [(-9268486844,2368900775646720), (2246907076,3835363160570880)]),
    ("39:23", (1,82,1), (39,23), (114231,67367,65481),
     (0,-3658968578788,0,-258325774492735247225616,1975349633743871233184217466468473408),
     [(-376434349596,1225056878538024960), (4189537167588,3194642653956910080),
      (Rational(10031272819776,25),Rational(145085974522042826376,125))]),
    ("71:69", (29,2,5), (71,69), (147751,143589,127161),
     (0,-4220840737396,0,-2163166245486471180298896,17391965988053038348885641834069354816),
     [(2844323623260,320864787342290016), (7972262159068,15445892450089511904)]),
]

ALARM = False
new_valid_count = 0
already_known_count = 0

for label, kernel, ab, seed, ainvs, gens in fibers:
    print(f"\n{'='*60}\n=== {label}  kernel={kernel} ===")
    alpha, beta, gamma = kernel
    fib = FiberXY(alpha, beta, gamma, *ab, seed)

    # try m0=0 first (cheap, worked most of the time), else fall back to seed-based centering
    val0 = fib.quartic_val(Rational(0))
    if val0 >= 0 and ssqrt(val0).is_rational:
        seed_m = Rational(0)
        print(f"  centering m0=0 (quartic(0)={val0}, perfect square)")
    else:
        # seed itself maps to infinity; search small range as fallback
        found = None
        for num in range(-100, 101):
            for den in range(1, 15):
                if num == 0: continue
                m0 = Rational(num, den)
                v = fib.quartic_val(m0)
                if v < 0: continue
                if ssqrt(v).is_rational:
                    found = m0; break
            if found: break
        if found is None:
            print("  NO CENTERING POINT FOUND -- skipping fiber")
            continue
        seed_m = found
        print(f"  centering m0={seed_m}")

    a2t, a4t, a6t = ainvs[1], ainvs[3], ainvs[4]
    try:
        r, _ = find_r(*fib.build_weierstrass_and_shift(seed_m), target_a2=a2t, target_a4=a4t, target_a6=a6t)
    except Exception as e:
        print("  find_r FAILED:", e)
        continue
    print(f"  r={r}")

    for gi, (Xg, Yg) in enumerate(gens):
        try:
            m_rec = pari_point_to_m(fib, seed_m, r, Rational(Xg), Rational(Yg))
            xyz = fib.m_to_xyz(m_rec)
        except Exception as e:
            print(f"  gen{gi}: ERROR {e}")
            continue
        if xyz is None:
            print(f"  gen{gi}: no valid (x,y,z) (m={m_rec})")
            continue
        res = analyze_xyz(*xyz)
        is_known_seed = (xyz == seed or tuple(sorted(xyz,reverse=True)) == tuple(sorted(seed,reverse=True)))
        tag = "[KNOWN SEED]" if is_known_seed else "[NEW]"
        print(f"  gen{gi} {tag} (x,y,z)={xyz}")
        print(f"      {res}")
        if res.get("valid") and not res.get("family_A") and res.get("A2_is_perfect_square"):
            ALARM = True
            print("  " + "!"*60)
            print("  !!!! A^2 IS A PERFECT SQUARE -- POTENTIAL COUNTEREXAMPLE !!!!")
            print("  " + "!"*60)
        if is_known_seed:
            already_known_count += 1
        elif res.get("valid"):
            new_valid_count += 1

print(f"\n\n{'='*60}")
print(f"TOTALS: new valid triples={new_valid_count}, mapped-to-known-seed={already_known_count}")
print(f"ANY A^2 PERFECT SQUARE FOUND: {ALARM}")
