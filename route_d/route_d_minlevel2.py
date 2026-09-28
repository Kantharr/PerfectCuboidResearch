"""Minimal obstruction level per excluded fiber, for both the Mordell-Weil-sieve version
(cosets of N * image of E(Q)) and the pure local version (cosets of N * E(F_l), i.e. every
N-cover pullback C_delta has no l-adic point), over N in a small list.  Reads alldata_<tag>.txt."""
import json, sys
from itertools import product
from route_d_coset_sieve import load, subgroup

LEVELS = [2, 3, 4, 6, 8, 12]


def run(data, r, N, local):
    classes = [g + t for g in product(range(N), repeat=r) for t in product(range(2), repeat=2)]
    killers = set()
    for (l, c1, c2, co, bits) in data:
        H = {(x, y) for x in range(c1) for y in range(c2)} if local else subgroup(co, c1, c2)
        NH = {((N * h[0]) % c1, (N * h[1]) % c2) for h in H}
        if len(NH) == len(H):
            continue
        keep = []
        for c in classes:
            base = (sum(ci * v[0] for ci, v in zip(c, co)) % c1, sum(ci * v[1] for ci, v in zip(c, co)) % c2)
            if any(bits[((base[1] + h[1]) % c2) * c1 + (base[0] + h[0]) % c1] == "1" for h in NH):
                keep.append(c)
            else:
                killers.add(l)
        classes = keep
        if not classes:
            break
    return len(classes), sorted(killers)


if __name__ == "__main__":
    rows = [json.loads(l) for l in open("minlevel_results.jsonl")]
    out = open("minlevel2_results.jsonl", "w")
    for rec in rows:
        tag, r = rec["tag"], rec["rank"]
        data = load(f"alldata_{tag}.txt")
        res = dict(tag=tag, a=rec["a"], b=rec["b"], kernel=rec["kernel"], rank=r, batch_death_N=rec["batch_death_N"])
        for local in (False, True):
            key = "local" if local else "mw"
            res[f"{key}_min"] = None
            for N in LEVELS:
                s, k = run(data, r, N, local)
                if s == 0:
                    res[f"{key}_min"] = N
                    res[f"{key}_killers"] = k
                    break
        out.write(json.dumps(res) + "\n")
        out.flush()
        print(f"{tag:22s} rank {r}  batch N={res['batch_death_N']:5d}  min level (MW sieve): {res['mw_min']}   (pure local): {res['local_min']}  local killers {res.get('local_killers')}", flush=True)
