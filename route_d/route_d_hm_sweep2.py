"""
Refined sweep: the curve's isomorphism class depends only on (a,b), not on
which solvable (alpha,beta,gamma) realizes it (verified: matching
conductor, j-invariant, and discriminant ratio a perfect 12th power across
3 different kernels at the same (a,b)). So testing many kernels per ratio
is wasted work -- try a SMALL number of kernels per (a,b) just to find one
solvable representative, then move to as many DISTINCT ratios as possible.
"""
import sys
from math import gcd
sys.path.insert(0, '.')
from route_d_hasse_minkowski import (squarefree_part, factorize, valid_alpha_beta_splits,
                                       qfsolve_point, derive_quartic_from_conic_point,
                                       ellrootno_for_quartic)

ab_list = []
for a in range(3, 120):
    for b in range(1, a):
        if gcd(a, b) != 1 or a % 2 == 0 or b % 2 == 0:
            continue
        prod = squarefree_part(a*a + b*b)
        if prod == 1:
            continue
        ab_list.append((a, b, prod))

known_ab = {(39,37),(13,9),(93,71),(223,211),(287,109),(257,93),(311,273),
            (139,97),(67,55),(125,79),(193,179),(157,101),(73,39),(127,67),
            (151,143),(47,21),(347,215),(47,23),(39,23),(71,69),
            (3,1),(5,1),(5,3)}  # already found a representative for these in the first sweep
ab_list = [c for c in ab_list if (c[0], c[1]) not in known_ab]

gamma_tries = [1, 3, 5, 7, 11, 13]
results = []
target_ratios = 100
found = 0

for a, b, prod in ab_list:
    if found >= target_ratios:
        break
    splits = valid_alpha_beta_splits(prod)
    solved = False
    for (alpha, beta) in splits:
        if solved:
            break
        for gamma in gamma_tries:
            if gcd(gamma, alpha * beta) != 1:
                continue
            pt = qfsolve_point(alpha, beta, gamma, a, b)
            if pt is None:
                continue
            coeffs = derive_quartic_from_conic_point(alpha, beta, gamma, a, b, *pt)
            if coeffs is None:
                continue
            out = ellrootno_for_quartic(coeffs)
            cond = rootno = None
            for line in out.splitlines():
                if line.startswith("COND:"):
                    cond = line.split(":",1)[1].strip()
                if line.startswith("ROOTNO:"):
                    rootno = line.split(":",1)[1].strip()
            label = f"({alpha},{beta},{gamma};{a},{b})"
            print(f"{label}: point={pt}  cond={cond}  rootno={rootno}")
            results.append((label, alpha, beta, gamma, a, b, pt, cond, rootno))
            solved = True
            found += 1
            break
    if not solved:
        print(f"(a,b)=({a},{b}): no solvable kernel found among {len(splits)} splits x {len(gamma_tries)} gammas tried")

print(f"\n\n{'='*70}")
print(f"Distinct (a,b) ratios with a found solvable representative: {found}")
pos = sum(1 for r in results if r[8] == '1')
neg = sum(1 for r in results if r[8] == '-1')
print(f"rootno +1: {pos}   rootno -1: {neg}")

import pickle
with open('route_d_hm_sweep2_results.pkl', 'wb') as f:
    pickle.dump(results, f)
