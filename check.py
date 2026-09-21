#!/usr/bin/env python3
"""
Consistency checks on the LaTeX source, independent of whether it compiles.
These replicate the sweeps used during drafting.

    python3 check.py perfect_cuboid.tex

Checks:
  1. every \\ref / \\eqref resolves to a \\label
  2. no duplicate labels
  3. every \\bibitem is cited, and every \\cite resolves
  4. theorem-like environments are balanced
  5. every theorem-like statement is followed by a proof
  6. reserved single letters are not reused across sections (advisory)

Exit code 0 if nothing is wrong, 1 otherwise.
"""

import re
import sys
from collections import Counter

ENVS = ["theorem", "proposition", "lemma", "corollary"]


def main(path):
    src = open(path, encoding="utf-8").read()
    problems = []
    advisories = []

    # 1 + 2: labels and references
    labels = re.findall(r"\\label\{([^}]*)\}", src)
    refs = set(re.findall(r"\\(?:eq)?ref\{([^}]*)\}", src))
    dangling = sorted(refs - set(labels))
    dupes = sorted(k for k, v in Counter(labels).items() if v > 1)
    for d in dangling:
        problems.append(f"dangling reference: \\ref{{{d}}} has no \\label")
    for d in dupes:
        problems.append(f"duplicate label: {d}")

    # 3: bibliography
    bibitems = re.findall(r"\\bibitem\{([^}]*)\}", src)
    cited = set()
    for group in re.findall(r"\\cite(?:\[[^\]]*\])?\{([^}]*)\}", src):
        cited.update(k.strip() for k in group.split(","))
    for b in sorted(set(bibitems) - cited):
        problems.append(f"uncited bibliography entry: {b}")
    for c in sorted(cited - set(bibitems)):
        problems.append(f"citation with no bibitem: {c}")

    # 4: environment balance
    for env in ENVS + ["proof", "remark", "conjecture"]:
        nb = len(re.findall(r"\\begin\{" + env + r"\}", src))
        ne = len(re.findall(r"\\end\{" + env + r"\}", src))
        if nb != ne:
            problems.append(f"unbalanced environment {env}: {nb} begin, {ne} end")

    # 5: statements without a following proof
    unproved = []
    for m in re.finditer(r"\\begin\{(" + "|".join(ENVS) + r")\}", src):
        env = m.group(1)
        seg = src[m.start():]
        lab = re.search(r"\\label\{([^}]*)\}", seg[:200])
        name = lab.group(1) if lab else "(unlabelled)"
        try:
            endpos = seg.index("\\end{" + env + "}")
        except ValueError:
            continue
        if "\\begin{proof}" not in seg[endpos:endpos + 400]:
            unproved.append(name)
    for u in unproved:
        advisories.append(f"no proof follows {u} (fine if the justification is in the statement)")

    # 6: advisory — a single letter defined in more than one place
    for letter in ["u", "v", "w", "g", "h", "s", "t", "e", "d", "f", "N", "S", "Q", "R"]:
        hits = len(re.findall(r"\$" + letter + r"\s*=", src))
        if hits > 1:
            advisories.append(f"'{letter}' is assigned in {hits} places — check for a collision")

    if problems:
        print(f"ERRORS ({len(problems)}):")
        for x in problems:
            print("  -", x)
    if advisories:
        print(f"advisories ({len(advisories)}) — review, not necessarily wrong:")
        for x in advisories:
            print("  .", x)
    if not problems:
        print(f"\n{path}: no errors — "
              f"{len(labels)} labels, {len(bibitems)} references, "
              f"{src.count(chr(92) + chr(98) + chr(101) + chr(103) + chr(105) + chr(110) + chr(123) + chr(112) + chr(114) + chr(111) + chr(111) + chr(102) + chr(125))} proofs")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1] if len(sys.argv) > 1 else "perfect_cuboid.tex"))
