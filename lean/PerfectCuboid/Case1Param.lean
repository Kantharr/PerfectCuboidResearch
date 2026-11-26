import PerfectCuboid.Case1

/-!
# Section 5 as stated: `lem:case1param` and `prop:case1form`

`Case1.lean` proves `thm:case1` without these; they are formalized here as the paper
states them.

* `case1param`: `lem:case1param`. If `y² = xz` with `x > y > z > 0`, `x, z` odd and no prime
  dividing all three, then `(x, y, z) = (a², ab, b²)` with coprime odd `a > b > 0`.
* `case1_quantities`, `case1_kappa`: for `(a², ab, b²)`, `R = (ab(a⁴ - b⁴))²`, `m = a³b³`,
  `S = a⁴ + a²b² - b⁴`, and `κ = ab(a⁴ - b⁴)`.
* `case1form`: `prop:case1form`, `A² N₋ = -a²b² N₊` with `N± = a⁴ ± a²b² - b⁴`; `N₊ > 0`;
  and `Nminus_pos_iff`: `N₋ > 0` iff `a/b > √φ`, `φ` the golden ratio.
-/

namespace PerfectCuboid

/-- `lem:case1param`. -/
theorem case1param {x y z : ℤ} (hz : 0 < z) (hzy : z < y) (hyx : y < x) (hx : Odd x)
    (hzo : Odd z) (hcop : ∀ p : ℕ, p.Prime → ¬ ((p : ℤ) ∣ x ∧ (p : ℤ) ∣ y ∧ (p : ℤ) ∣ z))
    (h : y ^ 2 = x * z) :
    ∃ a b : ℤ, 0 < b ∧ b < a ∧ Odd a ∧ Odd b ∧ IsCoprime a b ∧
      x = a ^ 2 ∧ y = a * b ∧ z = b ^ 2 := by
  have hy : 0 < y := hz.trans hzy
  have hx0 : 0 < x := hy.trans hyx
  -- `x` and `z` are coprime: a common prime divides `y² = xz`, hence `y`
  have hxz : IsCoprime x z := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    apply Nat.coprime_of_dvd
    intro k hk hkx hkz
    have hkx' : (k : ℤ) ∣ x := Int.natCast_dvd.mpr hkx
    have hkz' : (k : ℤ) ∣ z := Int.natCast_dvd.mpr hkz
    have hky : (k : ℤ) ∣ y :=
      (Nat.prime_iff_prime_int.mp hk).dvd_of_dvd_pow (h ▸ hkx'.mul_right z)
    exact hcop k hk ⟨hkx', hky, hkz'⟩
  obtain ⟨a₀, ha₀⟩ := Int.sq_of_isCoprime hxz h.symm
  obtain ⟨b₀, hb₀⟩ := Int.sq_of_isCoprime hxz.symm (by rw [mul_comm]; exact h.symm)
  have hxa : x = |a₀| ^ 2 := by
    rcases ha₀ with h1 | h1
    · rw [h1, sq_abs]
    · have := sq_nonneg a₀; linarith
  have hzb : z = |b₀| ^ 2 := by
    rcases hb₀ with h1 | h1
    · rw [h1, sq_abs]
    · have := sq_nonneg b₀; linarith
  set a := |a₀|
  set b := |b₀|
  have ha0 : 0 ≤ a := abs_nonneg _
  have hb0 : 0 ≤ b := abs_nonneg _
  have hb : 0 < b := by
    rcases hb0.lt_or_eq with h1 | h1
    · exact h1
    · rw [← h1] at hzb; simp at hzb; omega
  have hab : b < a := lt_of_pow_lt_pow_left₀ 2 ha0 (by rw [← hxa, ← hzb]; exact hzy.trans hyx)
  have hyab : y = a * b := by
    have h0 : (y - a * b) * (y + a * b) = 0 := by rw [hxa, hzb] at h; linear_combination h
    rcases mul_eq_zero.mp h0 with h1 | h1
    · linarith
    · nlinarith
  refine ⟨a, b, hb, hab, ?_, ?_, ?_, hxa, hyab, hzb⟩
  · exact (Int.odd_pow' two_ne_zero).mp (hxa ▸ hx)
  · exact (Int.odd_pow' two_ne_zero).mp (hzb ▸ hzo)
  · exact (IsCoprime.pow_iff two_pos two_pos).mp (by rw [← hxa, ← hzb]; exact hxz)

/-- The converse of `lem:case1param`, and the quantities of the family. -/
theorem case1_quantities (a b : ℤ) :
    (a * b) ^ 2 = a ^ 2 * b ^ 2 ∧
    R (a ^ 2) (a * b) (b ^ 2) = (a * b * (a ^ 4 - b ^ 4)) ^ 2 ∧
    m (a ^ 2) (a * b) (b ^ 2) = a ^ 3 * b ^ 3 ∧
    S (a ^ 2) (a * b) (b ^ 2) = a ^ 4 + a ^ 2 * b ^ 2 - b ^ 4 := by
  refine ⟨by ring, ?_, ?_, ?_⟩ <;> first | (unfold R; ring) | (unfold m; ring) | (unfold S; ring)

/-- On the surviving branch, `κ = ab(a⁴ - b⁴)`. -/
theorem case1_kappa {a b κ : ℤ} (hb : 0 < b) (hab : b < a) (hκ : 0 < κ)
    (hκ2 : κ ^ 2 = R (a ^ 2) (a * b) (b ^ 2)) : κ = a * b * (a ^ 4 - b ^ 4) := by
  have ha : 0 < a := hb.trans hab
  have h4 : b ^ 4 < a ^ 4 := pow_lt_pow_left₀ hab hb.le (by norm_num)
  have hpos : 0 < a * b * (a ^ 4 - b ^ 4) := mul_pos (mul_pos ha hb) (by linarith)
  have h0 : (κ - a * b * (a ^ 4 - b ^ 4)) * (κ + a * b * (a ^ 4 - b ^ 4)) = 0 := by
    linear_combination hκ2 + (case1_quantities a b).2.1
  rcases mul_eq_zero.mp h0 with h1 | h1
  · linarith
  · linarith

/-- `prop:case1form`: `A² N₋ = -a²b² N₊`. -/
theorem case1form {a b κ A : ℤ} (hb : 0 < b) (hab : b < a) (hκ : 0 < κ)
    (hκ2 : κ ^ 2 = R (a ^ 2) (a * b) (b ^ 2))
    (hA : A ^ 2 * (m (a ^ 2) (a * b) (b ^ 2) - κ) =
      m (a ^ 2) (a * b) (b ^ 2) * S (a ^ 2) (a * b) (b ^ 2)) :
    A ^ 2 * (a ^ 4 - a ^ 2 * b ^ 2 - b ^ 4) = -(a ^ 2 * b ^ 2 * (a ^ 4 + a ^ 2 * b ^ 2 - b ^ 4)) := by
  have ha : 0 < a := hb.trans hab
  rw [case1_kappa hb hab hκ hκ2] at hA
  obtain ⟨-, -, hm, hS⟩ := case1_quantities a b
  rw [hm, hS] at hA
  have h0 : (a * b) * (A ^ 2 * (a ^ 4 - a ^ 2 * b ^ 2 - b ^ 4) +
      a ^ 2 * b ^ 2 * (a ^ 4 + a ^ 2 * b ^ 2 - b ^ 4)) = 0 := by
    linear_combination -hA
  have := (mul_eq_zero.mp h0).resolve_left (mul_pos ha hb).ne'
  linarith

/-- `prop:case1form`: `N₊ > 0` for `a > b > 0`. -/
theorem Nplus_pos {a b : ℤ} (hb : 0 < b) (hab : b < a) : 0 < a ^ 4 + a ^ 2 * b ^ 2 - b ^ 4 := by
  have h4 : b ^ 4 < a ^ 4 := pow_lt_pow_left₀ hab hb.le (by norm_num)
  have : 0 < a ^ 2 * b ^ 2 := by have := hb.trans hab; positivity
  linarith

/-- `prop:case1form`: `N₋ > 0` iff `a/b > √φ`. -/
theorem Nminus_pos_iff {a b : ℤ} (hb : 0 < b) (hab : b < a) :
    0 < a ^ 4 - a ^ 2 * b ^ 2 - b ^ 4 ↔ √Real.goldenRatio < (a : ℝ) / b := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have haR : (0 : ℝ) < a := by exact_mod_cast hb.trans hab
  set σ : ℝ := ((a : ℝ) / b) ^ 2 with hσ
  have hσ0 : 0 < σ := by positivity
  -- `N₋ = b⁴ (σ - φ)(σ - ψ)` with `σ - ψ > 0`
  have hN : ((a ^ 4 - a ^ 2 * b ^ 2 - b ^ 4 : ℤ) : ℝ) =
      (b : ℝ) ^ 4 * ((σ - Real.goldenRatio) * (σ - Real.goldenConj)) := by
    have e1 := Real.goldenRatio_add_goldenConj
    have e2 := Real.goldenRatio_mul_goldenConj
    have hs : σ * (b : ℝ) ^ 2 = (a : ℝ) ^ 2 := by rw [hσ, div_pow]; field_simp
    push_cast
    linear_combination ((b : ℝ) ^ 2 - (σ * (b : ℝ) ^ 2 + (a : ℝ) ^ 2)) * hs
      + ((b : ℝ) ^ 4 * σ) * e1 - (b : ℝ) ^ 4 * e2
  have hψ : 0 < σ - Real.goldenConj := by have := Real.goldenConj_neg; linarith
  have hb4 : (0 : ℝ) < (b : ℝ) ^ 4 := by positivity
  rw [Real.sqrt_lt' (div_pos haR hbR), ← hσ]
  constructor
  · intro h
    have h' : (0 : ℝ) < ((a ^ 4 - a ^ 2 * b ^ 2 - b ^ 4 : ℤ) : ℝ) := by exact_mod_cast h
    rw [hN] at h'
    have := pos_of_mul_pos_left (pos_of_mul_pos_right h' hb4.le) hψ.le
    linarith
  · intro h
    have : (0 : ℝ) < ((a ^ 4 - a ^ 2 * b ^ 2 - b ^ 4 : ℤ) : ℝ) := by
      rw [hN]; exact mul_pos hb4 (mul_pos (by linarith) hψ)
    exact_mod_cast this

end PerfectCuboid
