"""Summarize batch_results.jsonl: per-fiber table plus the pattern statistics."""
import json, collections, math

rows = [json.loads(l) for l in open("batch_results.jsonl")]
ex = [r for r in rows if r["status"] == "EXCLUDED"]
skip = [r for r in rows if r["status"].startswith("SKIP")]
other = [r for r in rows if r not in ex and r not in skip]

print(f"fibers processed: {len(rows)}   EXCLUDED: {len(ex)}   SKIPPED: {len(skip)}   other: {len(other)}")
print()
print("| line | kernel | rank | death N | classes at death | random-model expected survivors | verification |")
print("|---|---|---|---|---|---|---|")
for r in ex:
    print(f"| {r['a']}:{r['b']} | {tuple(r['kernel'])} | {r['rank']} | {r['death_N']} | {r['classes_at_death_N']} | "
          f"{r['expected_survivors_random_model']:.3g} | {r['verification']} |")
print()
print("death N distribution by rank:", dict(collections.Counter((r['rank'], r['death_N']) for r in ex)))
lr = collections.Counter(tuple(r.get('line_rank') or ['?']) for r in skip)
print("skips by line ellrank [r1 r2 s]:", dict(lr))
print("skip reasons:", dict(collections.Counter(r['status'] for r in skip)))
for r in other:
    print("OTHER:", r['tag'], r['status'], r.get('verification'), r.get('survivors'))
# how far below the random model did fibers die?
logs = [math.log10(max(r['expected_survivors_random_model'], 1e-300)) for r in ex]
if logs:
    print(f"log10(random-model expected survivors at death): min {min(logs):.2f}, median {sorted(logs)[len(logs)//2]:.2f}, max {max(logs):.2f}")
