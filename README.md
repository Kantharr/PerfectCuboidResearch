# Perfect Cuboid Tools

Companion computational toolchain for:

> John Odom, *A Three-Parameter Reduction of the Perfect Cuboid Problem, and
> the Resolution of a Distinguished Family* (independent researcher; not yet
> submitted — this repository will be linked from the paper once it is).

The paper reduces the perfect cuboid problem to a search over primitive,
all-odd integer triples `x > y > z > 0` for which
`R = (x²+y²)(x²−z²)(y²−z²)` is a perfect square, resolves one sub-family
completely (`y² = xz`, via two elliptic curves), and studies the
complementary "product-only" family (`y² ≠ xz`) computationally and
conjecturally. Everything in this repository was built to search, verify,
or find structure in that complementary family — none of it is needed to
follow the paper's proofs, but all of it produced numbers the paper cites.

This repo does **not** contain the paper's LaTeX source, only the tools.

## Layout

```
.
├── verify.c, verify.py, check.py, crosscheck.py   -- core verification (§2-3, funnel table)
├── build.sh, Makefile                             -- build/verify automation (needs the paper source)
├── route_a_kernel/                                -- kernel decomposition & Gaussian-integer search (§4, Route A)
├── route_e/                                       -- Theorem 3.9 criterion scan (§6, Route E)
├── route_f/                                       -- squarefree-kernel / survivor scan (§6, Route F, Conjecture 6.3)
└── route_d/                                       -- elliptic-curve fiber construction (§6, Route D, Conjecture 6.3)
    └── pari/                                      -- example PARI/GP scripts (quartic → Weierstrass → rank)
```

"Route" names (A, D, E, F) are internal research labels, not something the
paper itself uses by that name — they refer to the lines of attack pursued
on the open `y² ≠ xz` case, kept here because the tools were built and
discussed under those names throughout development.

## Requirements

- A C compiler (`gcc`; developed against WinLibs/MinGW-w64 on Windows, but
  the code is portable C using `__int128`, so any GCC/Clang with 128-bit
  integer support works).
- Python 3 (`verify.py`, `check.py`, `crosscheck.py` have no dependencies
  beyond the standard library; the `route_a_kernel` and `route_d` scripts
  need [`sympy`](https://www.sympy.org/)).
- [PARI/GP](https://pari.math.u-bordeaux.fr/) for the `route_d` rank
  computations (`ellfromeqn`, `ellrank`). Tested against version 2.17.4.
  The `route_d` scripts that shell out to `gp` look for it on your `PATH`
  under the name `gp`; if it isn't there, set the `PARI_GP_PATH`
  environment variable to the full path of the `gp` executable.
- `latexmk` (any TeX distribution) only if you also want to run
  `build.sh`/`make all` — those targets build the paper's PDF and expect
  `perfect_cuboid.tex` to be present alongside these files (i.e. run them
  from a checkout of the paper's own repository with this tooling copied
  in, not from this repository in isolation).

## Core verification (repo root)

These four files work together and are the paper's primary computational
backbone — the funnel-table counts, the exhaustive `x ≤ N` checks, and the
Conjecture 6.3 sample sizes cited in §6 all come from these.

- **`verify.c`** — the fast, `__int128`-exact-arithmetic version. Given a
  bound `N`, exhaustively checks every primitive all-odd triple `x ≤ N` for
  `R` a perfect square, classifies it as family A (`y²=xz`) or product-only,
  and reports `m₁`-squareness (Conjecture 6.3), `d∣S` survivor status, and
  `A²`-squareness. This is what produced the "`7202` triples with `x≤50000`"
  figure in §6.
- **`verify.py`** — a slower, pure-Python re-implementation of the same
  logic, kept specifically so its output can be diffed against `verify.c`'s
  as an independent cross-check (see `crosscheck.py`) rather than trusting
  one implementation's arithmetic.
- **`check.py`** — a static consistency checker for the paper's own LaTeX
  source (label/reference/proof cross-referencing, variable-reuse
  advisories). Takes a `.tex` file as its argument; run it against
  `perfect_cuboid.tex` from the paper's own repository.
- **`crosscheck.py`** — runs `verify.py` and a freshly-built `verify.c`
  over the same range and diffs their output line by line, so "these two
  independent implementations agree" is a checked fact, not a claim.
- **`build.sh`** — builds the paper's PDF via `latexmk` and reports errors,
  overfull/underfull boxes, and unresolved references — the pass/fail
  criteria a referee would notice. Requires `perfect_cuboid.tex` alongside it.
- **`Makefile`** — `make check`, `make verify`, `make verify-crosscheck`,
  `make verify-big`, and `make all` (the PDF) wire the above together.

## `route_a_kernel/` — kernel decomposition, line searches, Gaussian-integer prediction

Theorem 4.1 in the paper (the "kernel decomposition") shows every
product-only solution factors as `x²+y²=αβu₁²`, `x²−z²=αγu₂²`,
`y²−z²=βγu₃²` for pairwise-coprime squarefree `α,β,γ`. These tools extract
that decomposition from real solutions, search along fixed coordinate-ratio
lines for more of them, and — the main finding of this branch — use
Gaussian integer arithmetic (Cornacchia's algorithm) to *predict* which
coordinate ratios are likely to be productive before searching, rather than
only recognizing productive ratios after a search happens to find them.

- **`kernel_decomp.c`** — given a range of `x`, extracts the full
  `(α,β,γ,u₁,u₂,u₃)` decomposition for every `Q>0` product-only triple found,
  with an internal self-check that the decomposition satisfies Theorem 4.1's
  own defining equations exactly.
- **`kernel_line_search.c`** — fixes a coordinate ratio `x:y = p:q` and
  searches over the third coordinate for solutions along that line; much
  cheaper than a full 3-variable search once a productive ratio is known
  or suspected.
- **`kernel_line_search2.c`** — generalization of the above: any one of the
  three coordinate pairs (`xy`, `xz`, or `yz`) can be the fixed ratio.
- **`kernel_line_search2_debug.c`** — an instrumented copy of
  `kernel_line_search2.c` with progress logging and internal sanity checks
  on the integer square-root routine, built to diagnose an apparent
  multi-hour hang that turned out to be a tooling artifact (see the paper
  project's own development notes) rather than a computational one. Kept as
  a template for diagnosing similar issues in future long-running searches.
- **`gaussian_predict.py`** — implements Cornacchia's algorithm (representing
  a prime `p ≡ 1 (mod 4)` as a sum of two squares) and uses it to generate,
  for a given kernel `(α,β)`, candidate coordinate ratios `a:b` compatible
  with that kernel — turning "recognize a productive line after finding it"
  into "predict a productive line before searching it."
- **`scratch_overnight_driver.py`** — batch-tests many `(α,β)` kernels'
  predicted ratios against `kernel_line_search2`, tallying hit rates. Despite
  the filename (an artifact of when it was written for a single overnight
  run), it is general-purpose sweep infrastructure, not a one-off script.

## `route_e/` — Theorem 3.9's prime criterion

- **`route_e.c`** — scans product-only triples for violations of
  Theorem 3.9's criterion (no odd prime may divide exactly two of `x,y,z`
  with certain valuation parity). Cited in §6 as an independent filter that
  excludes about 10% of eligible triples — a real but non-closing
  restriction on the family.

## `route_f/` — the squarefree-kernel equality and Conjecture 6.3's survivors

- **`route_f_check.c`** — checks the parity of `v_p(Q)` at two-variable
  primes, the mechanism behind Proposition 6.1's `d∣S` survivor analysis.
- **`route_f_scan.c`** — the main survivor-finding scan: for each product-only
  triple with `Q>0`, computes `m₁`, `e`, and whether `d∣S`; flags every
  `d∣S` "survivor" and classifies whether it has a one-variable-prime
  obstruction to `sf(m₁)=sf(e)` or is a genuine "escape risk" candidate.
  This is the tool behind the survivor counts discussed in §6's Route F
  material and the paper's `A²` non-squareness evidence.

## `route_d/` — elliptic-curve fibers for Conjecture 6.3

The newest and most involved branch, and the source of §6's paragraph on
proved elliptic-curve ranks. Fixing a kernel `(α,β,γ)` *and* a coordinate
ratio `x:y=a:b` turns the identity `x²−y²=γ(αu₂²−βu₃²)` (used in the
paper's own proof of Theorem 4.1) into a single conic in `(u₂,u₃,t)`; given
one known integer solution, that conic is rational, and substituting its
parametrization into `x²−z²=αγu₂²` and demanding a perfect square produces
a quartic model of a genus-1 curve. PARI/GP's `ellfromeqn` converts it to
Weierstrass form and `ellrank` proves its rank; a hand-derived (and
carefully round-trip-verified) birational map then converts the curve's own
rational points back into new integer `(x,y,z)` candidates, independent of
any brute-force search.

- **`route_d_fiber_pipeline.py`** — given a concrete `(x,y,z)` seed and its
  `(α,β,γ,a,b)` fiber data, derives the quartic symbolically (via `sympy`),
  writes a PARI/GP script, and runs the full convert → sanity-check → rank
  pipeline. Ships with 7 example fibers hard-coded (`13:9` through the
  `y:z`-fixed `53:49` case) — the first batch extending beyond the original
  hand-worked `39:37` example (see `pari/` below).
- **`route_d_inverse_map.py`** — the core, reusable library: derives the
  quartic-to-Weierstrass point map from scratch (not a memorized formula —
  the derivation is in the module docstring and comments), for both the
  `x:y`-fixed and `y:z`-fixed cases, and inverts it to recover `(x,y,z)`
  from a point on the Weierstrass model. Includes a self-test
  (`if __name__ == "__main__"`) that round-trips known triples through the
  forward and inverse maps before trusting the map on new data — run this
  first if adapting the code, to catch the kind of sign/scaling bugs its
  own development turned up.
- **`route_d_map_generators.py`** and **`route_d_batch2.py`** /
  **`route_d_batch2_recover.py`** — batch drivers that apply the pipeline
  and inverse map across many fibers at once (the two batches correspond to
  two rounds of fiber selection during development), each printing a full
  validity/`m₁`-squareness report per recovered triple.
- **`pari/`** — three example PARI/GP scripts for the first fiber worked by
  hand (kernel `(5,2,19)`, ratio `39:37`): converting the quartic to
  Weierstrass form, cross-checking that conversion against the quartic via
  point counts at several primes, and computing the rank. Useful as a
  minimal, standalone worked example — the Python drivers above generate
  scripts like these automatically for other fibers rather than requiring
  them to be written by hand.

## Reproducing the paper's key computational claims

```bash
# funnel table / Conjecture 6.3 sample sizes (§6)
gcc -O2 -o verify_bin verify.c -lm
./verify_bin 50000        # -> "7202 triples ... m1 square in 5089 ... none of the 2113"

# cross-check verify.c against verify.py at a smaller, faster range
python3 crosscheck.py 2000

# Route E's ~10% exclusion rate (§6)
gcc -O2 -o route_e_bin route_e/route_e.c -lm
./route_e_bin 7000

# Route D: reproduce several fibers' proved ranks (needs PARI/GP on PATH as `gp`)
cd route_d
python3 route_d_inverse_map.py       # self-test: round-trips known points first
python3 route_d_fiber_pipeline.py    # derives quartics for 7 example fibers, calls PARI/GP, prints each rank
```

## Notes

- No license has been chosen yet for this code; treat it as "all rights
  reserved, shared for verification purposes" until the author adds one.
- Several `.gp` and Python scripts print extensive diagnostic output by
  design (they were built as research instruments, not polished
  command-line tools) — this is intentional, since the point is to make
  every intermediate check visible rather than only the final answer.
