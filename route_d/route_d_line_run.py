"""Line-level exclusion: list the clean fibers with rational points on every line, then sieve them.

Usage (from a data directory):
    python route_d_line_run.py AMAX [AMIN]      -> writes lines_<AMIN>_<AMAX>.json (fiber list)
    python route_d_line_run.py --lines L.json   -> the lines [[a, b], ...] in L.json; writes lines_<L>.json
                                                  and lines_<AMIN>_<AMAX>_status.txt (per line)
    python route_d_batch.py lines_<AMIN>_<AMAX>.json   -> sieves them (resumable)

For every coprime pair a > b with a, b odd and AMIN <= a <= AMAX, route_d_line_fibres.gp gives
the fibers of the line a:b carrying a rational point (from the image of E(Q)/2E(Q)). The clean
ones, with base points, go to the fiber list; the two degenerate ones are only recorded. A line
whose rank is not proven, or whose generators are incomplete, is recorded as unresolved.
If every clean fiber of a line is excluded by the sieve, no perfect cuboid has x:y = a:b except
possibly on the two degenerate fibers.
"""
import json, math, os, subprocess, sys

GP = os.environ.get("PARI_GP_PATH", "gp")
HERE = os.path.dirname(os.path.abspath(__file__)).replace("\\", "/")


def main():
    if sys.argv[1] == "--lines":
        lines = [tuple(x) for x in json.load(open(sys.argv[2]))]
        tag = "lines_" + os.path.splitext(os.path.basename(sys.argv[2]))[0]
    else:
        amax = int(sys.argv[1])
        amin = int(sys.argv[2]) if len(sys.argv) > 2 else 3
        lines = [(a, b) for a in range(max(3, amin), amax + 1, 2) if a % 2
                 for b in range(1, a, 2) if math.gcd(a, b) == 1]
        tag = f"lines_{amin}_{amax}"
    src = (f'default(parisize, 1000000000);\nread("{HERE}/route_d_line_fibres.gp");\n'
           + "".join(f'{{my(r = iferr(linefibres({a},{b}), err, [Str("error ", err), 0, []]));'
                     f' print("LINE {a} {b} ", r[1], " | ", r[2], " | ", apply(f -> [f[1],f[2],f[3],f[4],f[5]], r[3]))}}\n'
                     for a, b in lines)
           + "quit\n")
    # route_d_line_fibres.gp reads its helpers by relative name, so run gp from this directory
    out = subprocess.run([GP, "-q"], input=src, capture_output=True, text=True, cwd=HERE).stdout
    fibers, status = [], []
    for line in out.splitlines():
        if not line.startswith("LINE "):
            continue
        # LINE a b <status> | <rank> | <list of [al, be, ga, kind, base point]>
        a, b = map(int, line.split()[1:3])
        left, rank, body = line.split(" | ", 2)
        st = left.split(" ", 3)[3]
        ents = json.loads(body) if body.strip() else []
        clean = [e for e in ents if e[3] == "clean"]
        for e in clean:
            fibers.append([a, b, e[0], e[1], e[2], e[4]])
        status.append(f"{a}:{b}  {st}  rank={rank}  clean={len(clean)}  degenerate={len(ents) - len(clean)}")
    json.dump(fibers, open(f"{tag}.json", "w"))
    open(f"{tag}_status.txt", "w").write("\n".join(status) + "\n")
    bad = [s for s in status if " ok " not in s]
    print(f"{len(lines)} lines, {len(status)} reported, {len(bad)} unresolved; {len(fibers)} clean fibers -> {tag}.json")
    for s in bad:
        print("  unresolved:", s)


if __name__ == "__main__":
    main()
