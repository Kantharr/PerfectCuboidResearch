import sys, subprocess, pickle
sys.path.insert(0, '.')
from route_d_hasse_minkowski import qfsolve_point, derive_quartic_from_conic_point, GP

with open('route_d_hm_sweep2_results.pkl', 'rb') as f:
    results = pickle.load(f)
plus1 = [r for r in results if r[8] == '1']
plus1.sort(key=lambda r: int(r[7]))

targets = plus1[20:28]

for label, alpha, beta, gamma, a, b, pt, cond, rootno in targets:
    coeffs = derive_quartic_from_conic_point(alpha, beta, gamma, a, b, *pt)
    c4, c3, c2, c1, c0 = coeffs
    script = f"""
quartic(m) = {c4}*m^4 + ({c3})*m^3 + ({c2})*m^2 + ({c1})*m + ({c0});
f = y^2 - ({c4}*x^4 + ({c3})*x^3 + ({c2})*x^2 + ({c1})*x + ({c0}));
E = ellinit(ellfromeqn(f));
D = E.disc;
print("COND: ", ellglobalred(E)[1]);
print("TORS: ", elltors(E));
countquartic(p) = {{my(cnt=0); for(mm=0,p-1, my(v=lift(Mod(quartic(mm),p))); if(v==0, cnt+=1, if(kronecker(v,p)==1, cnt+=2))); if(kronecker({c4},p)==1, cnt+=2, if(Mod({c4},p)==0,cnt+=1)); return(cnt);}};
countE(p) = {{return(p+1-ellap(E,p));}};
allmatch = 1;
for(i=1,4, myp=prime(70+i); if(Mod(D,myp)!=0, cq=countquartic(myp); ce=countE(myp); if(cq!=ce, allmatch=0)));
print("SANITY_OK: ", allmatch);
r = ellrank(E, 4);
print("RANK: ", r);
"""
    print(f"\n=== {label}  cond={cond} ===")
    try:
        out = subprocess.run([GP, "-q"], input=script, capture_output=True, text=True, timeout=90)
        print(out.stdout.strip())
        if out.stderr.strip():
            print("STDERR:", out.stderr[:500])
    except subprocess.TimeoutExpired:
        print("TIMEOUT (90s)")
