# rank of E0^delta over K = Q(sqrt130), delta = 33(11+sqrt130), and the equivalent twist over Q(i),
# delta' = (sqrt(delta) + sqrt(delta^sigma))^2 = 66(11+3i) (same 2-dim irreducible rep of the D4 closure).
import time, sys
E0 = EllipticCurve([0, 0, 0, -532, -2064])
which = sys.argv[1]
if which == "K":
    K.<r> = NumberField(x^2 - 130); d = 33*(11 + r)
else:
    K.<i> = NumberField(x^2 + 1); d = 66*(11 + 3*i)
E = E0.change_ring(K).quadratic_twist(d)
E = E.global_minimal_model() if E.has_global_minimal_model() else E
print(which, E.ainvs(), " torsion", E.torsion_subgroup().invariants(), flush=True)
for lim3 in (100, 400, 1500):
    t0 = time.time()
    lo, up, pts = E.simon_two_descent(lim1=10, lim3=lim3, limtriv=lim3, maxprob=50, limbigprime=60)
    print(f"  lim3={lim3}: rank in [{lo}, {up}], points {pts}  ({time.time()-t0:.0f} s)", flush=True)
    if lo == up:
        break
