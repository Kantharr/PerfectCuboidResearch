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
└── route_d/                                       -- elliptic-curve fiber construction (§6, Route D, Conjecture 6.3),
    │                                                 fiber exclusion (Mordell–Weil sieve), and the Jacobian of the
    │                                                 cuboid cover C (Theorems 6.4 and 6.5)
    ├── pari/                                      -- example PARI/GP scripts (quartic → Weierstrass → rank)
    └── sage/                                      -- SageMath scripts for the Prym surfaces of the 11:3 fiber
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
- [SageMath](https://www.sagemath.org/) only for `route_d/sage/` (tested
  with the `sagemath/sagemath:10.9` Docker image).
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

### Fiber exclusion: the Mordell–Weil sieve on the cuboid cover

On a fiber, a perfect cuboid gives a rational point on the double cover
`C: W² = F`, `F = mS(m−k)`. These scripts prove `C(ℚ) = ∅` fiber by fiber
(the 63 excluded fibers of §6). Run them from inside `route_d/`; they write
their generated PARI files and result tables into the current directory.

- **`route_d_clean_fibers.py`** — enumerates the kernels on a ratio line,
  tests solvability, searches for points, and classifies each fiber as
  Case‑1, `y = z`, or clean.
- **`route_d_fiber_local.py`**, **`route_d_cover_local.py`** — exact `p`-adic
  solvability tests (Hensel-certified tree search) for the fiber and for the
  cover `C`.
- **`route_d_basepoint.gp`** — rational base points on a fiber via its conic
  and `hyperellratpoints`.
- **`route_d_fiber_model.py`** — explicit Weierstrass model of a fiber with
  forward and inverse maps, verified symbolically.
- **`route_d_sieve_setup.py`** — emits the per-fiber PARI files
  (`route_d_psiF_<tag>.gp`, `route_d_mwsieve_data_<tag>.gp`) for the sieve.
- **`route_d_mwsieve.py`** — the staged Mordell–Weil sieve itself.
- **`route_d_certificate.py`** — an independent certificate (exact `F` at a
  representative of every residue class, plus a non-residue prime); writes
  `reps_<tag>.gp`.
- **`route_d_validate.py`** — ground-truth check of the sieve data against
  exact values of `F` at actual rational points.
- **`route_d_batch.py`** / **`route_d_batch_analyze.py`** — run the whole
  pipeline over a JSON list of fibers and summarize `batch_results.jsonl`. A
  fiber entry may carry a known base point as a sixth element
  (`[a, b, α, β, γ, [t, z, u₂, u₃]]`, e.g. from `route_d_fiber_descent.gp`),
  which skips the height search. It can run from any directory; generated files
  go to the current one. Fibers with at most `ROUTE_D_CERT_MAX` classes at death (default 20000) get
  the full exact certificate, the rest the ground-truth cross-check; large batches
  use a lower value (2500 for the a <= 99 line run). For hard (rank 3-4) fibers,
  `ROUTE_D_CHAIN`, `ROUTE_D_CLASS_CAP`, `ROUTE_D_STREAM_CAP` and `ROUTE_D_LMAX`
  set a finer level chain, the class caps (a streamed lift in `route_d_mwsieve.py`
  keeps only survivors in memory) and the prime bound; defaults are unchanged.
  With `ROUTE_D_SIEVE_BIN` set to a build of **`route_d_sieve_stage.c`**
  (`gcc -O2 -o route_d_sieve_stage route_d_sieve_stage.c`), each streamed stage runs
  in C: identical survivors and per-prime counts, about 60 times faster (~6M
  classes/s), which makes rank-4 fibers (10^9-10^10 lifted classes) feasible.
- **`route_d_image_model.py`**, **`route_d_coset_sieve.py`**,
  **`route_d_minlevel.py`**, **`route_d_minlevel2.py`** — the "early death"
  analysis: an independence benchmark within the image of `E(ℚ)`, the full
  coset sieve at a fixed level, and the minimal obstruction level per fiber.
- **`route_d_fiber_descent.gp`** (driver **`route_d_fiber_descent_run.gp`**) —
  decides whether a fiber has a rational point at all. The fiber is the
  2-covering of `E_{a,b}` with Kummer class `(σ, −σαγ)`; with a proven rank and
  2-saturated generators, it has a point iff that class lies in the image of
  `E(ℚ)/2E(ℚ)`. It checks that the image has dimension exactly rank + 2, and
  when a point exists it returns an explicit base point. On the 128 clean
  fibers of the survey it proves that the 60 fibers on lines with nontrivial
  `Sha[2]` have no rational points, and gives base points (11–18 digits) for
  the other 5 unresolved ones.
- **`route_d_line_fibres.gp`** — lists every fiber of a line `a:b` that carries
  a rational point, straight from the image of `E(ℚ)/2E(ℚ)` (no kernel survey):
  the classes with first coordinate `σ` and `αγ, βγ > 0`, flagged as the two
  degenerate fibers (through `(a,b,b)` and `(a²,ab,b²)`) or clean, each with a base
  point. `batchentries(a, b)` gives the clean ones in `route_d_batch.py` format. On
  the 54 survey lines it finds exactly the 68 clean fibers with points.
- **`route_d_line_run.py`** — runs `route_d_line_fibres.gp` over every odd coprime
  line up to a bound and writes the clean fibers as a `route_d_batch.py` fiber list
  (`lines_<AMIN>_<AMAX>.json`), plus a per-line status file (rank, clean and
  degenerate counts, unresolved lines). `--lines L.json` takes an explicit list.
- **`route_d_findgens.gp`** (driver **`route_d_findgens_run.gp`**) — finds the
  missing generators when `ellrank` proves the rank but lists too few points:
  rational points on the 2-covers of `E` and of its 2-isogenous curves
  (`ell2cover` + `hyperellratpoints`), then `ellrank` at higher effort. Results
  go into a `KNOWNGENS` file; set `ROUTE_D_KNOWNGENS` to its path and every
  stage (line enumeration, sieve setup, certificate) picks the points up through
  `route_d_isogpoints.gp`.
- **`route_d_selmer_lines.py`** — line-level test from the 2-Selmer group alone:
  a fiber with a rational point has its class in `Sel2(E_{a,b})`, so a line whose
  Selmer group has no clean class has no clean fiber with a point, with no
  generators or proven rank needed. It returns the Selmer elements (not just the
  dimension, as `route_d_selmer2.py` does). On the 54 survey lines its clean
  classes are exactly the survey's locally solvable clean kernels.
- **`route_d_analytic_rank.gp`** — root number and analytic rank of `E_{a,b}` for
  lines whose rank `ellrank` cannot prove; `L'(E,1) ≠ 0` with root number −1 gives
  rank exactly 1 (Gross–Zagier, Kolyvagin), so the rank-one theorem applies.
- **`route_d_isocoset.gp`** — missing generators from the 2-isogenous curve
  `E' = E/<(0,0)>`, which also has full rational 2-torsion: the 2-coverings of every
  class in the missing coset of `Sel2(E')` are searched (`route_d_cosetsearch.gp`)
  and points are sent back by the dual isogeny, which halves their height first.
  On 43:9 it finds the generator in under a second where `E`'s own coset classes
  have no point up to height 10^6. `route_d_selmer_lines.py --isogenous` supplies
  `Sel2(E')`. (`route_d_cosetsearch.gp`: the same search on `E` itself;
  `route_d_fourdescent.gp`: an incomplete 4-descent, see its header.)
- **`route_d_isoclass.gp`** — missing generators from the whole isogeny class of
  `E_{a,b}` (6 curves: degrees 1, 2, 4, 4, 2, 2). Regulators across the class differ
  by powers of 2 and `ellbsd` predicts the ratios, so `ellrank` is run on each curve,
  smallest predicted regulator first, and points come back through the dual isogeny
  from `ellisomat`. On a curve with a quarter of `E`'s regulator the missing
  generator has about a quarter of its height: on 2026-10-02 it found 6 of the 14
  missing generators (59:31, 63:1, 81:47, 83:81, 99:31, 99:79) in under 2 minutes
  each, 4 of them on a 4-isogenous curve that the earlier searches never used.
- **`route_d_g2height.gp`** — BSD estimate of how large a missing generator is on each
  curve of the isogeny class (`L''(E,1)` from `ellanalyticrank`, regulator ratios
  from `ellbsd`, Sha assumed trivial). On the 8 lines still missing a generator it
  gives heights of about 160–370 on the best curve, beyond any height search here.
- **`route_d_rank1_lines.gp`** — the rank-one line theorem: on a line where
  `E_{a,b}` has rank 1, the image of `E(ℚ)/2E(ℚ)` is generated by the Kummer
  images of the two 2-torsion points and the universal point
  `(a²b², a³b³)`, so only the two degenerate fibers have rational points. It
  checks the images symbolically, then compares with `ellrank` on every odd
  coprime line with `a ≤ 99` (369 of 1003 have proven rank 1; all agree).
- **`route_d_isogpoints.gp`** — when `ellrank` proves the rank but lists fewer
  points (the line 43:9), finds the missing generators on the 2-isogenous
  curves and maps them back; used by the descent test, `route_d_sieve_setup.py`
  and `route_d_certificate.py`.
- **`route_d_selmer2.py`** (needs **`route_d_selmer2_p2table.json`** beside
  it) and **`route_d_selmer2_proofcheck.py`** — an independent 2-Selmer
  computation for `E(a,b)` by complete 2-descent, and a mechanical check of
  the written local-image proofs.

### The Jacobian of the cover `C` (Theorems 6.4 and 6.5)

`Jac(C)` splits as `E_{a,b}` times four Prym surfaces of genus-3 double covers
`D_h` of a quotient curve `E'`. These scripts compute and prove that splitting.

- **`route_d_prym_fiber.gp`**, **`route_d_prym_traces.gp`** — Frobenius traces
  of the four Prym surfaces, directly on the fiber model.
- **`route_d_quotients.gp`** — the explicit quotients `D_h: W² = hF` and fast
  `O(p²)` point counts (`dcount`); **`route_d_quotients_run.gp`** runs it on
  the 11:3 fiber, and **`cremona_match.gp`** searches Cremona's tables for
  the resulting trace pairs (it reads `quot_11_3_65_2_1.txt`, the output of
  the run script).
- **`route_d_prym_split.gp`** — the reflection construction: trace and norm
  of `hF` down to `ℚ(u)`, and the genus-1 quotients.
- **`route_d_structpt.gp`**, **`route_d_structpt_sym.gp`**,
  **`route_d_structpt_proof.gp`**, **`route_d_structpt_closed_check.gp`** —
  Theorem 6.4: the four elliptic factors of `Prym(D₁)` and `Prym(D_x)` over
  `ℚ(t)`, their closed forms, and the proof that the structural points have
  infinite order.
- **`route_d_weilres_sym.gp`** — Theorem 6.5: the symbolic proof that the
  two remaining Prym surfaces are Weil restrictions from `ℚ(√(a²+b²))` of
  explicit twists, on every fiber. It prints `ALL 25 CHECKS PASSED` only if
  every check ran.
- **`route_d_weilres_check.gp`** — an independent point-count check of
  Theorem 6.5 on 10 fibers (410 surface/prime pairs, all agreeing).
- **`route_d_weilres_lvalue.gp`** — the central value `L(E/K, 1)` of an elliptic
  curve over a real quadratic field by the explicit approximate-functional-equation
  series; independence of the split point `t0` checks conductor, root number and
  coefficients. **`route_d_weilres_lvalue_test.gp`** validates it against PARI's
  `lfun` on small-conductor curves (including over `ℚ(√130)` and two root-number −1
  cases), and **`route_d_weilres_lvalue_run.gp`** runs it on the ψ₃/ψ₄ curves of the
  11:3 fiber (set `WHICH`, `T0`, `ZCUT` in a file read first, e.g.
  `gp -q params.gp route_d_weilres_lvalue_run.gp`; about 2·10⁸ coefficients, 8 GB).

### `sage/` — SageMath scripts (11:3 fiber)

Number-field computations that PARI does not cover conveniently:
`prym_split.sage` and `prym_twist.sage` (the Prym factors over `ℚ(√130)` and
their twist data), `prym_psi3_rank.sage` (Simon 2-descent on the ψ₃ curve),
`quotients.sage` (plane models of the `D_h`) and `sanity.sage` (installation
check). Run them from `route_d/` as `sage sage/<file>.sage`; `prym_twist.sage`
reads `sage/prym_split.sage` by that relative path. They were run with the
`sagemath/sagemath:10.9` Docker image.

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

# Theorems 6.4 and 6.5 (the decomposition of Jac(C)), still inside route_d/
gp -q route_d_structpt_proof.gp < /dev/null    # Theorem 6.4: splitting and infinite-order points over Q(t)
gp -q route_d_weilres_sym.gp < /dev/null       # Theorem 6.5: prints "ALL 25 CHECKS PASSED"
gp -q route_d_weilres_check.gp < /dev/null     # point-count cross-check: "ALL AGREE: 410 of 410"
```

## Notes

- No license has been chosen yet for this code; treat it as "all rights
  reserved, shared for verification purposes" until the author adds one.
- Several `.gp` and Python scripts print extensive diagnostic output by
  design (they were built as research instruments, not polished
  command-line tools) — this is intentional, since the point is to make
  every intermediate check visible rather than only the final answer.
