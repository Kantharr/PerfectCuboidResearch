# psi3/psi4 of the 11:3 (65,2,1) fiber: P_h ~ Res_{K/Q} E_K with K = Q(sqrt130) and j(E_K) in Q.
# Write E_K = E0^delta (E0 over Q with the same j), analyse delta, root number and 2-Selmer over K.
import time
exec(preparse(open("sage/prym_split.sage").read().split("for name, hi in")[0]))   # reuse helpers only
for hi in (3, 4):
    Tr, Nm = trnm(Ts["B1"], hi)
    c, M = const_times_square(Nm)
    K = NumberField(polygen(QQ)^2 - c, 'r'); r = K.gen()
    Fk = FunctionField(K, 'v'); v = Fk.gen()
    Trk = Fk(Tr.numerator().change_ring(K)(v)) / Fk(Tr.denominator().change_ring(K)(v))
    Mk = Fk(M.numerator().change_ring(K)(v)) / Fk(M.denominator().change_ring(K)(v))
    q = sqf_kernel(Trk + 2*r*Mk, K)
    E = jacobian_of_quartic(q)
    A, B = E.a4(), E.a6()
    E0 = EllipticCurve_from_j(QQ(E.j_invariant())).minimal_model()
    A0, B0 = E0.short_weierstrass_model().a4(), E0.short_weierstrass_model().a6()
    delta = (B*A0)/(A*B0)
    Ed = E0.change_ring(K).quadratic_twist(delta)
    assert Ed.is_isomorphic(E), "twist identification failed"
    nd = delta.norm()
    print(f"psi{hi}: E_K = E0^delta over K = Q(sqrt {c}),  E0 = {E0.ainvs()}  conductor {E0.conductor().factor()}")
    print(f"   delta = {delta}  (norm {nd.factor()}, squarefree class of norm: {nd.squarefree_part()})")
    # is delta in Q^* K^*2 ?  (then Res splits over Q)
    inQ = any((delta/d).is_square() for d in [1, -1] + [s*p for s in (1, -1) for p in divisors(abs(nd.numerator()*nd.denominator()))])
    print(f"   delta in Q* K*^2 (Res would split over Q): {inQ}")
    t0 = time.time()
    Emin = E.global_minimal_model() if E.has_global_minimal_model() else E
    print(f"   E_K torsion: {Emin.torsion_subgroup().invariants()}")
    try:
        print(f"   global root number of E_K over K: {Emin.root_number()}")
    except Exception as ex:
        print("   root number failed:", ex)
    print(f"   rank of E0 over Q: {E0.rank()} ; E0^130 over Q: {E0.quadratic_twist(130).minimal_model().rank()}")
    try:
        lo, up = Emin.rank_bounds(lim1=10, lim3=100, limtriv=100, maxprob=50, limbigprime=60)
        print(f"   Simon 2-descent over K (higher effort): rank in [{lo}, {up}]  ({time.time() - t0:.0f} s)", flush=True)
    except Exception as ex:
        print("   Simon failed:", ex)
    if Emin.two_torsion_rank() > 0:
        print(f"   2-torsion rank over K: {Emin.two_torsion_rank()}")
