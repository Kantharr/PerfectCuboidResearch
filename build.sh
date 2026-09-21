#!/usr/bin/env bash
# Build perfect_cuboid.tex and report anything a referee would notice.
# Usage: ./build.sh [name]        (default: perfect_cuboid)
set -uo pipefail
NAME="${1:-perfect_cuboid}"
LOG=build.log

command -v latexmk >/dev/null || { echo "latexmk not found. Install TeX Live / MacTeX / MiKTeX."; exit 1; }

rm -f "$NAME".{aux,log,out,fls,fdb_latexmk,toc} "$LOG"
latexmk -pdf -interaction=nonstopmode "$NAME.tex" > "$LOG" 2>&1
STATUS=$?

ERR=$(grep -c '^!' "$LOG")
OVER=$(grep -c 'Overfull' "$LOG")
UNDER=$(grep -c 'Underfull' "$LOG")
UNRES=$(awk '/Run number 2/,0' "$LOG" | grep -c 'undefined')

echo "build exit      : $STATUS"
echo "latex errors    : $ERR"
echo "overfull boxes  : $OVER"
echo "underfull boxes : $UNDER"
echo "unresolved refs : $UNRES   (after final pass)"

if [ "$ERR" -gt 0 ]; then
  echo; echo "--- errors ---"; grep -n -A3 '^!' "$LOG" | head -40
fi
if [ "$OVER" -gt 0 ]; then
  echo; echo "--- overfull locations ---"; grep 'Overfull' "$LOG" | sort -u | head -20
fi

grep -o "Output written on $NAME.pdf.*" "$LOG" | tail -1
latexmk -c "$NAME.tex" >/dev/null 2>&1
[ "$ERR" -eq 0 ] && [ "$STATUS" -eq 0 ]
