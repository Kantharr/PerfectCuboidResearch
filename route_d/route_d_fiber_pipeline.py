"""
Route D fiber pipeline: given a concrete known (x,y,z) triple, automatically
derive the genus-1 quartic for its (kernel, coordinate-ratio) fiber (either
x:y-fixed or y:z-fixed, following the two Vieta-based derivations verified
by hand on 2026-09-20/21), write a PARI/GP script that converts it to
Weierstrass form via ellfromeqn, sanity-checks the transform via point
counts at several primes, and computes the rank via ellrank.

x:y-fixed case (x=a*t, y=b*t fixed, eliminate z between the two difference
equations): identity gamma*(alpha*u2^2 - beta*u3^2) = (a^2-b^2)*t^2.

y:z-fixed case (y=p*t, z=q*t fixed, eliminate x between the sum equation
and one difference equation): identity alpha*(beta*u1^2 - gamma*u2^2)
= (p^2+q^2)*t^2.
"""

from math import gcd, isqrt
from sympy import symbols, expand, simplify, Poly, together, fraction, Rational

def factorize(n):
    f = {}; d = 2; n = abs(n)
    while d * d <= n:
        while n % d == 0:
            f[d] = f.get(d, 0) + 1
            n //= d
        d += 1 if d == 2 else 2
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f

def squarefree_part(n):
    r = 1
    for p, e in factorize(n).items():
        if e % 2 == 1:
            r *= p
    return r

def recover_abg(x, y, z):
    xy = squarefree_part(x * x + y * y)
    xz = squarefree_part(x * x - z * z)
    yz = squarefree_part(y * y - z * z)
    num = xz * yz
    g2 = num // xy
    g = isqrt(g2)
    assert g * g == g2 and num % xy == 0
    alpha = xz // g
    beta = yz // g
    return alpha, beta, g

def derive_quartic_xy(alpha, beta, gamma, a, b, x, y, z, t0):
    """x:y fixed at (a,b); seed from known (x,y,z), t=t0."""
    u2_0 = isqrt((x * x - z * z) // (alpha * gamma))
    u3_0 = isqrt((y * y - z * z) // (beta * gamma))
    assert alpha * gamma * u2_0**2 == x * x - z * z
    assert beta * gamma * u3_0**2 == y * y - z * z

    m, W2 = symbols('m W2')
    W3_line = u3_0 + m * (W2 - u2_0)
    conic = expand(alpha * W2**2 - beta * W3_line**2 - Rational(a*a - b*b, gamma) * t0**2)
    poly = Poly(conic, W2)
    A, B, C = poly.all_coeffs()
    W2_other = simplify(C / (A * u2_0))

    Z2 = a**2 * t0**2 - alpha * gamma * W2_other**2
    Z2 = together(Z2)
    num, den = fraction(Z2)
    num = expand(num)
    return num, (u2_0, u3_0, t0)

def derive_quartic_yz(alpha, beta, gamma, p, q, x, y, z, t0):
    """y:z fixed at (p,q); seed from known (x,y,z), t=t0."""
    u1_0 = isqrt((x * x + y * y) // (alpha * beta))
    u2_0 = isqrt((x * x - z * z) // (alpha * gamma))
    assert alpha * beta * u1_0**2 == x * x + y * y
    assert alpha * gamma * u2_0**2 == x * x - z * z

    m, U1 = symbols('m U1')
    U2_line = u2_0 + m * (U1 - u1_0)
    conic = expand(alpha * beta * U1**2 - alpha * gamma * U2_line**2 - (p*p+q*q) * t0**2)
    poly = Poly(conic, U1)
    A, B, C = poly.all_coeffs()
    U1_other = simplify(C / (A * u1_0))

    X2 = alpha * beta * U1_other**2 - (p * t0)**2
    X2 = together(X2)
    num, den = fraction(X2)
    num = expand(num)
    return num, (u1_0, u2_0, t0)

def quartic_coeffs(num_expr):
    m = symbols('m')
    poly = Poly(num_expr, m)
    c = poly.all_coeffs()
    while len(c) < 5:
        c = [0] + c
    return c  # [c4,c3,c2,c1,c0]

def write_gp_script(label, coeffs, path):
    c4, c3, c2, c1, c0 = coeffs
    gp = f"""
quartic(m) = {c4}*m^4 + ({c3})*m^3 + ({c2})*m^2 + ({c1})*m + ({c0});
f = y^2 - ({c4}*x^4 + ({c3})*x^3 + ({c2})*x^2 + ({c1})*x + ({c0}));
E = ellinit(ellfromeqn(f));
print("LABEL: {label}");
print("AINVS: ", E.a1, " ", E.a2, " ", E.a3, " ", E.a4, " ", E.a6);
D = E.disc;
print("DISC: ", D);
cond = ellglobalred(E)[1];
print("COND: ", cond);
tors = elltors(E);
print("TORS: ", tors);
countquartic(p) = {{my(cnt=0); for(mm=0,p-1, my(v=lift(Mod(quartic(mm),p))); if(v==0, cnt+=1, if(kronecker(v,p)==1, cnt+=2))); if(kronecker({c4},p)==1, cnt+=2, if(Mod({c4},p)==0,cnt+=1)); return(cnt);}};
countE(p) = {{return(p+1-ellap(E,p));}};
for(i=1,10, myp=prime(40+i); if(Mod(D,myp)!=0, cq=countquartic(myp); ce=countE(myp); print("CHECK p=", myp, " quartic=", cq, " E=", ce, " match=", cq==ce)));
r = ellrank(E, 4);
print("RANK: ", r);
"""
    with open(path, 'w') as f:
        f.write(gp)

if __name__ == "__main__":
    import os, subprocess, sys

    # Path to the PARI/GP interpreter. Override with the PARI_GP_PATH
    # environment variable if `gp` is not on your PATH.
    GP = os.environ.get("PARI_GP_PATH", "gp")

    fibers = [
        # (label, kind, (x,y,z), fixed_ratio)
        ("13:9",     "xy", (403, 279, 117), (13, 9)),
        ("93:71",    "xy", (93, 71, 27),    (93, 71)),
        ("223:211",  "xy", (25199, 23843, 13603), (223, 211)),
        ("287:109",  "xy", (218981, 83167, 80557), (287, 109)),
        ("257:93",   "xy", (15163, 5487, 2313), (257, 93)),
        ("311:273",  "xy", (2799, 2457, 2407), (311, 273)),
        ("53:49_yz", "yz", (2597, 2279, 2107), (53, 49)),
    ]

    for label, kind, (x, y, z), (a, b) in fibers:
        alpha, beta, gamma = recover_abg(x, y, z)
        g = gcd(x, y) if kind == "xy" else gcd(y, z)
        t0 = g
        print(f"\n=== {label}: (x,y,z)=({x},{y},{z}) kernel=({alpha},{beta},{gamma}) t0={t0} ===")
        if kind == "xy":
            num, seed = derive_quartic_xy(alpha, beta, gamma, a, b, x, y, z, t0)
        else:
            num, seed = derive_quartic_yz(alpha, beta, gamma, a, b, x, y, z, t0)
        coeffs = quartic_coeffs(num)
        print("quartic coeffs [c4,c3,c2,c1,c0]:", coeffs)
        gp_path = f"pari_fiber_{label.replace(':','_')}.gp"
        write_gp_script(f"{label} kernel=({alpha},{beta},{gamma})", coeffs, gp_path)
        try:
            out = subprocess.run([GP, "-q", gp_path], capture_output=True, text=True, timeout=90)
            print(out.stdout)
            if out.stderr.strip():
                print("STDERR:", out.stderr[:2000])
        except subprocess.TimeoutExpired:
            print("TIMED OUT after 90s")
