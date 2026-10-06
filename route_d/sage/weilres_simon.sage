# Rank bounds over K = Q(sqrt sigma) for the twists E3^(al ga delta3), E4^(be ga delta4) of a fibre
# (Theorem weilres; see route_d_weilres_rank0.gp for why rank 0 settles the fibre).
# Simon's 2-descent over K, escalating effort. The bound depends on the model, so the curves
# 2-isogenous to it (depth 2) are tried too, and the smallest bound kept.
# limbigprime=0: no probabilistic local tests (class groups still assume GRH unless certified).
# Simon's bound is only an upper bound here, model-dependent even with full 2-torsion: on 11:3,
# whose E3 twist has rank 0 (L-value), the best bound over the isogeny class is 3; on 81:19
# (2,3461,1) it is 1 (E>0), against 2, 3, 5 on the other curves (2026-10-05).
#
# Usage: sage weilres_simon.sage a b al be ga E3|E4 [lim3 ...]
import sys, time
a, b, al, be, ga = [int(v) for v in sys.argv[1:6]]
which = sys.argv[6]
lims = [int(v) for v in sys.argv[7:]] or [50, 200]
s = a^2 + b^2
K.<r> = NumberField(x^2 - s)
if which == "E3":
    d = al*ga*(-2*a*(a + r)); lam, mu = -4*b^2*s, -4*a^2*b^2*s^2
else:
    d = be*ga*(2*b*(r - b)); lam, mu = -4*a^2*s, -4*a^2*b^2*s^2
E = EllipticCurve(K, [0, d*lam, 0, d^2*mu, 0])
# Rank is an isogeny invariant but Simon's bound is not: try every curve reachable by 2-isogenies
# (depth 2), each on a reduced model when one is available.
def reduced(M):
    try:
        if M.has_global_minimal_model():
            return M.global_minimal_model()
    except Exception:
        pass
    return M
models, frontier = [("E", E)], [("E", E)]
for depth in (1, 2):
    nxt = []
    for name, M in frontier:
        for i, phi in enumerate(M.isogenies_prime_degree(2)):
            C = phi.codomain()
            if any(C.is_isomorphic(N) for _, N in models):
                continue
            nm = f"{name}>{i}"; models.append((nm, C)); nxt.append((nm, C))
    frontier = nxt
models = [(n, reduced(M)) for n, M in models]
print(f"{a}:{b} ({al},{be},{ga}) {which}  K = Q(sqrt {s})  class group {K.class_group().invariants()}"
      f"  torsion {E.torsion_subgroup().invariants()}", flush=True)
best = None
for name, M in models:
    for lim3 in lims:
        t0 = time.time()
        try:
            lo, up, pts = M.simon_two_descent(lim1=5, lim3=lim3, limtriv=lim3, maxprob=20, limbigprime=0)
        except Exception as e:
            print(f"  {name} lim3={lim3}: error {e}", flush=True); break
        print(f"  {name} lim3={lim3}: rank in [{lo}, {up}], {len(pts)} points  ({time.time()-t0:.0f} s)", flush=True)
        best = up if best is None else min(best, up)
        if lo == up:
            break
    if best == 0 or lo == up:
        break
print(f"RESULT {a}:{b} ({al},{be},{ga}) {which}  upper bound {best}", flush=True)
