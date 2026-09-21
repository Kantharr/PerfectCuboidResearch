import os, sys, subprocess
from math import gcd
sys.path.insert(0, '.')
from route_d_inverse_map import FiberXY, recover_abg

# Path to the PARI/GP interpreter. Override with the PARI_GP_PATH environment
# variable if `gp` is not on your PATH (e.g. a Windows install placed under
# AppData\Local\Programs\PariGP\gp.exe with no installer-added PATH entry).
GP = os.environ.get("PARI_GP_PATH", "gp")

def write_gp_script(coeffs, path):
    c4, c3, c2, c1, c0 = coeffs
    gp = f"""
quartic(m) = {c4}*m^4 + ({c3})*m^3 + ({c2})*m^2 + ({c1})*m + ({c0});
f = y^2 - ({c4}*x^4 + ({c3})*x^3 + ({c2})*x^2 + ({c1})*x + ({c0}));
E = ellinit(ellfromeqn(f));
print("AINVS: ", E.a1, " ", E.a2, " ", E.a3, " ", E.a4, " ", E.a6);
D = E.disc;
print("DISC: ", D);
tors = elltors(E);
print("TORS: ", tors);
countquartic(p) = {{my(cnt=0); for(mm=0,p-1, my(v=lift(Mod(quartic(mm),p))); if(v==0, cnt+=1, if(kronecker(v,p)==1, cnt+=2))); if(kronecker({c4},p)==1, cnt+=2, if(Mod({c4},p)==0,cnt+=1)); return(cnt);}};
countE(p) = {{return(p+1-ellap(E,p));}};
for(i=1,6, myp=prime(50+i); if(Mod(D,myp)!=0, cq=countquartic(myp); ce=countE(myp); print("CHECK p=", myp, " quartic=", cq, " E=", ce, " match=", cq==ce)));
r = ellrank(E, 4);
print("RANK: ", r);
"""
    with open(path, 'w') as f:
        f.write(gp)

fibers = [
    ("139:97",  (5,34,177),   (139,97),  (41561,29003,25159)),
    ("67:55",   (2,13,183),   (67,55),   (57017,46805,39083)),
    ("125:79",  (13,2,3),     (125,79),  (241375,152549,145825)),
    ("193:179", (2,205,21),   (193,179), (170033,157699,150539)),
    ("157:101", (34,41,129),  (157,101), (87449,56257,47975)),
    ("73:39",   (1,274,1),    (73,39),   (80081,42783,42705)),
    ("127:67",  (61,2,15),    (127,67),  (124079,65459,61849)),
    ("151:143", (2,865,21),   (151,143), (396073,375089,367081)),
    ("47:21",   (2,53,13),    (47,21),   (126195,56385,55007)),
    ("347:215", (2,493,33),   (347,215), (836617,518365,510883)),
    ("47:23",   (1,2,15),     (47,23),   (115103,56327,53897)),
    ("39:23",   (1,82,1),     (39,23),   (114231,67367,65481)),
    ("71:69",   (29,2,5),     (71,69),   (147751,143589,127161)),
]

results = {}
for label, (alpha,beta,gamma), ab, seed in fibers:
    print(f"\n{'='*60}\n=== {label}  kernel=({alpha},{beta},{gamma}) ===")
    fib = FiberXY(alpha, beta, gamma, *ab, seed)
    coeffs = [fib.a4, fib.a3, fib.a2, fib.a1, fib.a0]
    gp_path = f"pari_batch2_{label.replace(':','_')}.gp"
    write_gp_script(coeffs, gp_path)
    try:
        out = subprocess.run([GP, "-q", gp_path], capture_output=True, text=True, timeout=120)
        print(out.stdout)
        if out.stderr.strip():
            print("STDERR:", out.stderr[:1500])
        results[label] = out.stdout
    except subprocess.TimeoutExpired:
        print("TIMED OUT after 120s")
        results[label] = "TIMEOUT"

import pickle
with open('route_d_batch2_results.pkl', 'wb') as f:
    pickle.dump(results, f)
