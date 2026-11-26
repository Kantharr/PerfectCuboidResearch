import PerfectCuboid.Master

/-!
# Section 5: the family `y² = xz`, conditional on the quartic

`QuarticHyp` is the statement the paper proves in `thm:quartic` through the elliptic curve
`V² = U³ - 7U - 6` (rank `0`, torsion `ℤ/2 × ℤ/2`): the curve `Y² = -W⁴ + 3W² - 1` has
only the rational points with `W = ±1`. In integers: `3p²q² - p⁴ - q⁴` is a square only
when `p² = q²`. The paper's rank computation needs the Mordell-Weil theorem, which Mathlib
does not have, so it is stated here as a hypothesis; `Quartic.lean` then proves it by an
elementary infinite descent (`quarticHyp`), making `thm:case1` unconditional
(`Cuboid.not_case1'`, `exists_iff_case2'`).

* `quartic_of_hyp`: the paper's form of `thm:quartic` (`3a⁴b⁴ - a⁸ - b⁸ = c²` forces
  `a = ±b`) follows, with `p = a²`, `q = b²`.
* `no_case1`: `thm:case1`, conditional on `QuarticHyp`. The proof here is shorter than the
  paper's and needs neither `lem:case1param` nor `lem:normalise`: for `y² = xz`,
  `R = y²(x² - z²)²`, so `κ = y(x² - z²)`, and the surviving branch becomes
  `A² (z² + xz - x²) = y² (x² + xz - z²)`. The factor `z² + xz - x²` must be positive (the
  paper's `a/b < √φ`), and then `3x²z² - x⁴ - z⁴ = (x² + xz - z²)(z² + xz - x²)` is a square.
* `Cuboid.not_case1`: no cuboid in normal form has `y² = xz`.
-/

namespace PerfectCuboid

/-- `thm:quartic`, in the general form its proof gives: `3p²q² - p⁴ - q⁴` is a square only
when `p² = q²`. Taken as a hypothesis (see the module doc). -/
def QuarticHyp : Prop := ∀ p q c : ℤ, 3 * p ^ 2 * q ^ 2 - p ^ 4 - q ^ 4 = c ^ 2 → p ^ 2 = q ^ 2

/-- The paper's statement of `thm:quartic` follows from `QuarticHyp`. -/
theorem quartic_of_hyp (hq : QuarticHyp) {a b c : ℤ}
    (h : 3 * a ^ 4 * b ^ 4 - a ^ 8 - b ^ 8 = c ^ 2) : a = b ∨ a = -b := by
  have h2 := hq (a ^ 2) (b ^ 2) c (by linear_combination h)
  have h4 : (a ^ 2 - b ^ 2) * (a ^ 2 + b ^ 2) = 0 := by linear_combination h2
  rcases mul_eq_zero.mp h4 with h5 | h5
  · have : (a - b) * (a + b) = 0 := by linear_combination h5
    rcases mul_eq_zero.mp this with h6 | h6
    · left; linarith
    · right; linarith
  · have ha : a ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
    have hb : b ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
    left; rw [pow_eq_zero_iff two_ne_zero |>.mp ha, pow_eq_zero_iff two_ne_zero |>.mp hb]

/-- For `y² = xz` the radicand is `y² (x² - z²)²`. -/
theorem R_of_case1 {x y z : ℤ} (h : y ^ 2 = x * z) :
    R x y z = (y * (x ^ 2 - z ^ 2)) ^ 2 := by
  unfold R
  linear_combination (x ^ 2 - z ^ 2) * (y ^ 2 + x * z) * h

/-- `thm:case1`, conditional on `QuarticHyp`: on the surviving branch with
`x > y > z > 0`, the condition `y² = xz` is impossible. -/
theorem no_case1 (hq : QuarticHyp) {A x y z κ : ℤ} (hz : 0 < z) (hzy : z < y) (hyx : y < x)
    (hκ : 0 < κ) (hκ2 : κ ^ 2 = R x y z)
    (hA : A ^ 2 * (m x y z - κ) = m x y z * S x y z) (h : y ^ 2 = x * z) : False := by
  have hy : 0 < y := hz.trans hzy
  have hx : 0 < x := hy.trans hyx
  have hxz : z ^ 2 < x ^ 2 := pow_lt_pow_left₀ (hzy.trans hyx) hz.le two_ne_zero
  -- `κ = y (x² - z²)`
  have ht : 0 < y * (x ^ 2 - z ^ 2) := mul_pos hy (by linarith)
  have hκe : κ = y * (x ^ 2 - z ^ 2) := by
    have h0 : (κ - y * (x ^ 2 - z ^ 2)) * (κ + y * (x ^ 2 - z ^ 2)) = 0 := by
      linear_combination hκ2 + R_of_case1 h
    rcases mul_eq_zero.mp h0 with h1 | h1
    · linarith
    · linarith
  subst hκe
  -- the branch equation becomes `A² N = y² P`
  set P := x ^ 2 + x * z - z ^ 2 with hP
  set N := z ^ 2 + x * z - x ^ 2 with hN
  have hmain : y * (A ^ 2 * N - y ^ 2 * P) = 0 := by
    unfold m S at hA
    linear_combination hA - y * (x ^ 2 - z ^ 2) * h
  have hmain' : A ^ 2 * N = y ^ 2 * P := by
    have := (mul_eq_zero.mp hmain).resolve_left hy.ne'
    linarith
  have hPpos : 0 < P := by
    have : 0 < x * z := mul_pos hx hz
    linarith
  -- `N > 0`: otherwise the left side is `≤ 0 < y² P`
  have hNpos : 0 < N := by
    by_contra hle
    replace hle := not_lt.mp hle
    have h1 : A ^ 2 * N ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg A) hle
    have h2 : 0 < y ^ 2 * P := by positivity
    linarith
  -- `(A N)² = y² (P N)`, so `y ∣ A N` and `P N` is a square
  have hsq : (A * N) ^ 2 = y ^ 2 * (P * N) := by linear_combination N * hmain'
  obtain ⟨t, ht⟩ : y ∣ A * N :=
    (Int.pow_dvd_pow_iff two_ne_zero).mp ⟨P * N, hsq⟩
  have hPN : P * N = t ^ 2 := by
    rw [ht, mul_pow] at hsq
    exact (mul_left_cancel₀ (pow_ne_zero 2 hy.ne') hsq).symm
  have hquart : 3 * x ^ 2 * z ^ 2 - x ^ 4 - z ^ 4 = t ^ 2 := by
    rw [← hPN, hP, hN]; ring
  have := hq x z t hquart
  linarith

namespace Cuboid

variable (c : Cuboid)

/-- `thm:case1` for cuboids, conditional on `QuarticHyp`: no perfect cuboid in normal form
(`A` the odd edge, `B < C`) has `y² = xz`. -/
theorem not_case1 (hq : QuarticHyp) (hA : Odd c.A) (hBC : c.B < c.C) :
    c.y ^ 2 ≠ c.x * c.z := by
  obtain ⟨-, -, -, hyx, hzy, hz, -, κ, hκ2, hκ, -, hsimp⟩ := c.necessary hA hBC
  exact fun h => no_case1 hq hz hzy hyx hκ hκ2 hsimp h

end Cuboid

/-- Conditional on `QuarticHyp`, a perfect cuboid exists iff one exists in normal form with
`y² ≠ xz` (the open family of Section 6). -/
theorem exists_iff_case2 (hq : QuarticHyp) :
    FormalConjecturesStatement ↔
      ∃ c : Cuboid, c.IsPrimitive ∧ Odd c.A ∧ c.B < c.C ∧ c.y ^ 2 ≠ c.x * c.z := by
  rw [formalConjectures_iff]
  constructor
  · rintro ⟨c⟩
    obtain ⟨c', hp, hA, hBC⟩ := exists_normal c
    exact ⟨c', hp, hA, hBC, c'.not_case1 hq hA hBC⟩
  · rintro ⟨c, -⟩
    exact ⟨c⟩

end PerfectCuboid
