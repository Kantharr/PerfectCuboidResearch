#!/usr/bin/env python3
"""
Cross-check verify.py and the compiled verify.c binary against each other.

Runs both at the same N, parses their summary counts and the list of
"integral A^2" cases out of stdout, and diffs them field by field. This
replaces trusting the README's prose claim that the two implementations
"agree where both run" with an automated check.

Usage:   python3 crosscheck.py [N] [path-to-compiled-binary]
Default: N=2000, binary auto-detected as ./verify(.exe)

Exit code 0 if every compared field matches, 1 otherwise (with a report of
exactly what differs).
"""

import os
import re
import subprocess
import sys

PY_PATTERNS = {
    "famA": r"family A \(y\^2 = xz\)\s+(\d+)",
    "prod": r"product-only \(y\^2 != xz\)\s+(\d+)",
    "qpos": r"Q > 0\s+(\d+)",
    "integral": r"d \| S\s+\(A\^2 an integer\)\s+(\d+)",
    "square": r"A\^2 a perfect square\s+(\d+)",
}
PY_M1SQ = r"m1 a perfect square: famA (\d+)/(\d+), product-only (\d+)/(\d+)"
PY_CASE = (
    r"integral A\^2: \(x,y,z\)=\((\d+),(\d+),(\d+)\)\s+"
    r"m1=(\d+)\s+e=(\d+)\s+A\^2=(\d+)\s+square=(True|False)"
)

C_SUMMARY = (
    r"FINAL N=(\d+): famA (\d+) \(m1 square (\d+)\) \| "
    r"product-only (\d+) \(m1 square (\d+)\)"
)
C_QSTATS = r"Q>0 (\d+) \| d\|S (\d+) \| A\^2 a perfect square (\d+)"
C_CASE = (
    r"integral A\^2: \((\d+),(\d+),(\d+)\)\s+"
    r"m1=(\d+)\s+e=(\d+)\s+A\^2=(\d+)\s+square=(\d)"
)


def parse_python(out):
    fields = {}
    for name, pat in PY_PATTERNS.items():
        m = re.search(pat, out)
        if not m:
            raise ValueError(f"verify.py output: could not find field '{name}'")
        fields[name] = int(m.group(1))

    m = re.search(PY_M1SQ, out)
    if not m:
        raise ValueError("verify.py output: could not find m1-square summary line")
    fields["m1sqA"] = int(m.group(1))
    fields["m1sqC"] = int(m.group(3))

    cases = {}
    for m in re.finditer(PY_CASE, out):
        x, y, z, m1, e, a2, sq = m.groups()
        cases[(int(x), int(y), int(z))] = (int(m1), int(e), int(a2), sq == "True")
    fields["cases"] = cases
    return fields


def parse_c(out):
    fields = {}
    m = re.search(C_SUMMARY, out)
    if not m:
        raise ValueError("verify.c output: could not find FINAL summary line")
    fields["famA"] = int(m.group(2))
    fields["m1sqA"] = int(m.group(3))
    fields["prod"] = int(m.group(4))
    fields["m1sqC"] = int(m.group(5))

    m = re.search(C_QSTATS, out)
    if not m:
        raise ValueError("verify.c output: could not find Q>0/d|S/square line")
    fields["qpos"] = int(m.group(1))
    fields["integral"] = int(m.group(2))
    fields["square"] = int(m.group(3))

    cases = {}
    for m in re.finditer(C_CASE, out):
        x, y, z, m1, e, a2, sq = m.groups()
        cases[(int(x), int(y), int(z))] = (int(m1), int(e), int(a2), sq == "1")
    fields["cases"] = cases
    return fields


def find_binary(explicit):
    if explicit:
        if os.path.exists(explicit):
            return explicit
        raise FileNotFoundError(f"no such binary: {explicit}")
    for candidate in ("./verify.exe", "./verify"):
        if os.path.exists(candidate):
            return candidate
    raise FileNotFoundError(
        "no compiled verify binary found (expected ./verify or ./verify.exe); "
        "build it first with: gcc -O2 -o verify verify.c -lm"
    )


def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 2000
    binary = sys.argv[2] if len(sys.argv) > 2 else None
    binary = find_binary(binary)

    print(f"Cross-checking verify.py against {binary} at N={N} ...\n")

    py_out = subprocess.run(
        [sys.executable, "verify.py", str(N)],
        capture_output=True, text=True, check=True,
    ).stdout
    c_out = subprocess.run(
        [binary, str(N)], capture_output=True, text=True, check=True,
    ).stdout

    py = parse_python(py_out)
    c = parse_c(c_out)

    scalar_fields = ["famA", "prod", "qpos", "integral", "square", "m1sqA", "m1sqC"]
    mismatches = []

    width = max(len(f) for f in scalar_fields)
    print(f"  {'field':<{width}}  {'verify.py':>10}  {'verify.c':>10}")
    for f in scalar_fields:
        ok = py[f] == c[f]
        mark = "OK" if ok else "MISMATCH"
        print(f"  {f:<{width}}  {py[f]:>10}  {c[f]:>10}   {mark}")
        if not ok:
            mismatches.append(f"{f}: verify.py={py[f]} vs verify.c={c[f]}")

    py_keys = set(py["cases"])
    c_keys = set(c["cases"])
    only_py = py_keys - c_keys
    only_c = c_keys - py_keys
    if only_py:
        mismatches.append(f"integral cases only in verify.py: {sorted(only_py)}")
    if only_c:
        mismatches.append(f"integral cases only in verify.c: {sorted(only_c)}")
    for key in sorted(py_keys & c_keys):
        if py["cases"][key] != c["cases"][key]:
            mismatches.append(
                f"integral case {key} differs: "
                f"verify.py={py['cases'][key]} vs verify.c={c['cases'][key]}"
            )

    print()
    if mismatches:
        print(f"DISAGREEMENT ({len(mismatches)}):")
        for m in mismatches:
            print("  -", m)
        return 1

    print(f"AGREEMENT: verify.py and verify.c match on every field at N={N} "
          f"({len(py_keys)} integral case(s) compared).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
