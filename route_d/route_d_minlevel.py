"""For every excluded fiber: all-prime data (l <= LMAX) and the full coset sieve at small N,
to find the minimal level at which a finite descent obstruction appears."""
import json, re, subprocess, os, sys
sys.set_int_max_str_digits(0)
from route_d_coset_sieve import load, sieve
GP = os.environ.get("PARI_GP_PATH", "gp")
LMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
rows = [json.loads(l) for l in open("batch_results.jsonl") if json.loads(l)["status"] == "EXCLUDED"]
done = set()
if os.path.exists("minlevel_results.jsonl"):
    done = {json.loads(l)["tag"] for l in open("minlevel_results.jsonl")}
for r in rows:
    tag = r["tag"]
    if tag in done: continue
    src = open(f"route_d_mwsieve_data_{tag}.gp").read().replace("  if(NMAX % cyc[1] != 0, return(0));\n", "")
    src = re.sub(r'forprime\(l = 7, \d+, if\(D % l == 0, next\); nl \+= doprime\(l, \d+, "sieve_data_[^"]*"\)\);',
                 f'forprime(l = 7, {LMAX}, if(D % l == 0, next); nl += doprime(l, 0, "alldata_{tag}.txt"));', src)
    open(f"route_d_alldata_{tag}.gp", "w").write(src)
    if os.path.exists(f"alldata_{tag}.txt"): os.remove(f"alldata_{tag}.txt")
    out = subprocess.run([GP, "-q", f"route_d_alldata_{tag}.gp"], stdin=subprocess.DEVNULL, capture_output=True, text=True, timeout=7200).stdout
    m = re.search(r"wrote data for (\d+) primes", out)
    rec = dict(tag=tag, a=r["a"], b=r["b"], kernel=r["kernel"], rank=r["rank"], batch_death_N=r["death_N"], nprimes=int(m.group(1)) if m else 0)
    if m:
        data = load(f"alldata_{tag}.txt")
        for N in (2, 3, 4):
            cls, kil = sieve(data, r["rank"], N)
            rec[f"N{N}_survivors"] = len(cls)
            rec[f"N{N}_killers"] = sorted(set(kil.values()))
    with open("minlevel_results.jsonl", "a") as fh: fh.write(json.dumps(rec) + "\n")
    print(tag, "rank", rec["rank"], "primes", rec["nprimes"], {k: v for k, v in rec.items() if k.endswith("survivors")}, "killers@2:", rec.get("N2_killers"), flush=True)
