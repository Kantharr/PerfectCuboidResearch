import PerfectCuboid.Converse

/-!
# Exact prime powers in `ℤ`, and the two-variable case (`thm:twovar`, `lem:twovar`)

`ExactPow p e n`: `n = pᵉ u` with `p ∤ u`, i.e. `v_p(n) = e`. The basic rules (`unique`,
`mul`, `add_of_dvd`, `of_sq`, `dvd_iff`) are all the valuation arithmetic needed.

The two-variable lemmas are proved once, abstractly (`twovar_lt`, `twovar_eq_good`,
`twovar_eq_bad`), for a prime `p` and integers with `m = u v w`, `κ² = (u² + ε v²) U` where
`ε = ±1`, and `p ∤ w`, `p ∤ U`, `p ∤ S`. With `u = pᵉ¹ u₀`, `v = pᵉ² v₀`, `p ∤ u₀ v₀`:
* `twovar_lt`: if `e₁ < e₂` then `v_p(A²) = e₂` (`lem:twovar` (i));
* `twovar_eq_good`: if `e₁ = e₂ = e ≥ 1` and `p ∤ u₀² + ε v₀²` then `v_p(A²) = e`;
* `twovar_eq_bad`: if `e₁ = e₂ = e ≥ 1` and `p ∣ u₀² + ε v₀²` then `pᵉ ∤ A²`.
These are `lem:twovar` (ii) in the form `thm:converse-full` uses (`δ = 0` versus `δ > 0`);
the exact values `e - δ`, `0`, `≤ 0` in the `δ > 0` cases are not needed and not formalized.
The three pairs `(x, y)`, `(x, z)`, `(y, z)` of the paper are the instances
`ε = 1, U = (x² - z²)(y² - z²)`; `ε = -1, U = (x² + y²)(y² - z²)`; and
`ε = -1, U = (x² + y²)(x² - z²)` (see `ConverseFull.lean`).
-/

namespace PerfectCuboid

/-- `p^e` divides `n` exactly. -/
def ExactPow (p e : ℕ) (n : ℤ) : Prop := ∃ u : ℤ, n = (p : ℤ) ^ e * u ∧ ¬ (p : ℤ) ∣ u

namespace ExactPow

variable {p : ℕ}

theorem of_not_dvd {u : ℤ} (h : ¬ (p : ℤ) ∣ u) : ExactPow p 0 u := ⟨u, by simp, h⟩

theorem mk {e : ℕ} {u : ℤ} (h : ¬ (p : ℤ) ∣ u) : ExactPow p e ((p : ℤ) ^ e * u) := ⟨u, rfl, h⟩

theorem dvd {e : ℕ} {n : ℤ} (h : ExactPow p e n) : (p : ℤ) ^ e ∣ n := by
  obtain ⟨u, rfl, -⟩ := h; exact dvd_mul_right _ _

theorem not_dvd_succ (hp : p.Prime) {e : ℕ} {n : ℤ} (h : ExactPow p e n) :
    ¬ (p : ℤ) ^ (e + 1) ∣ n := by
  obtain ⟨u, rfl, hu⟩ := h
  rw [pow_succ]
  intro hd
  exact hu ((mul_dvd_mul_iff_left (pow_ne_zero e (by exact_mod_cast hp.ne_zero))).mp hd)

theorem dvd_iff (hp : p.Prime) {e f : ℕ} {n : ℤ} (h : ExactPow p e n) :
    (p : ℤ) ^ f ∣ n ↔ f ≤ e := by
  constructor
  · intro hd
    by_contra hlt
    exact h.not_dvd_succ hp ((pow_dvd_pow _ (by omega)).trans hd)
  · intro hle; exact (pow_dvd_pow _ hle).trans h.dvd

theorem unique (hp : p.Prime) {e f : ℕ} {n : ℤ} (h1 : ExactPow p e n) (h2 : ExactPow p f n) :
    e = f :=
  le_antisymm ((h2.dvd_iff hp).mp h1.dvd) ((h1.dvd_iff hp).mp h2.dvd)

theorem mul (hp : p.Prime) {a b : ℕ} {x y : ℤ} (hx : ExactPow p a x) (hy : ExactPow p b y) :
    ExactPow p (a + b) (x * y) := by
  obtain ⟨u, rfl, hu⟩ := hx
  obtain ⟨w, rfl, hw⟩ := hy
  refine ⟨u * w, by ring, fun h => ?_⟩
  rcases (Nat.prime_iff_prime_int.mp hp).dvd_or_dvd h with h | h
  · exact hu h
  · exact hw h

theorem neg {e : ℕ} {n : ℤ} (h : ExactPow p e n) : ExactPow p e (-n) := by
  obtain ⟨u, rfl, hu⟩ := h
  exact ⟨-u, by ring, fun h => hu (by simpa using h.neg_right)⟩

/-- Adding a multiple of `p^{e+1}` does not change an exact power `p^e`. -/
theorem add_of_dvd {e : ℕ} {a b : ℤ} (ha : ExactPow p e a) (hb : (p : ℤ) ^ (e + 1) ∣ b) :
    ExactPow p e (a + b) := by
  obtain ⟨u, rfl, hu⟩ := ha
  obtain ⟨w, rfl⟩ := hb
  refine ⟨u + p * w, by ring, fun h => hu ?_⟩
  have : (p : ℤ) ∣ p * w := dvd_mul_right _ _
  exact (dvd_add_left this).mp h

/-- Every nonzero integer has an exact power of `p`. -/
theorem exists_of_ne_zero (hp : p.Prime) {n : ℤ} (hn : n ≠ 0) : ∃ e, ExactPow p e n := by
  obtain ⟨e, n', hnd, hn'⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.mpr hn) p hp.one_lt.ne'
  refine ⟨e, n.sign * n', ?_, fun hd => hnd ?_⟩
  · conv_lhs => rw [← Int.sign_mul_natAbs n, hn']
    push_cast; ring
  · have := Int.natCast_dvd.mp hd
    rwa [Int.natAbs_mul, Int.natAbs_sign_of_ne_zero hn, one_mul, Int.natAbs_natCast] at this

/-- A square has an even exact power, half of which is the root's. -/
theorem of_sq (hp : p.Prime) {c : ℕ} {k : ℤ} (h : ExactPow p c (k ^ 2)) (hk : k ≠ 0) :
    ∃ j, c = 2 * j ∧ ExactPow p j k := by
  obtain ⟨j, hj⟩ := exists_of_ne_zero hp hk
  refine ⟨j, ?_, hj⟩
  have := hj.mul hp hj
  rw [← sq] at this
  have := h.unique hp this
  omega

end ExactPow

/-- `p ∣ u²` implies `p ∣ u`, for prime `p`. -/
theorem dvd_of_dvd_sq' {p : ℕ} (hp : p.Prime) {u : ℤ} (h : (p : ℤ) ∣ u ^ 2) : (p : ℤ) ∣ u :=
  (Nat.prime_iff_prime_int.mp hp).dvd_of_dvd_pow h

theorem not_dvd_mul' {p : ℕ} (hp : p.Prime) {a b : ℤ} (ha : ¬ (p : ℤ) ∣ a) (hb : ¬ (p : ℤ) ∣ b) :
    ¬ (p : ℤ) ∣ a * b := fun h =>
  ((Nat.prime_iff_prime_int.mp hp).dvd_or_dvd h).elim ha hb

section twovar

variable {p : ℕ} (hp : p.Prime) {A u v w U S' m' κ ε u₀ v₀ : ℤ} {e₁ e₂ : ℕ}
include hp

/-- The shared setup: `m' = u v w` with `u = p^{e₁} u₀`, `v = p^{e₂} v₀`, and the exact
power of `m' S'` is `e₁ + e₂`. -/
theorem twovar_mS (hm : m' = u * v * w) (hw : ¬ (p : ℤ) ∣ w) (hS : ¬ (p : ℤ) ∣ S')
    (hu : u = (p : ℤ) ^ e₁ * u₀) (hv : v = (p : ℤ) ^ e₂ * v₀) (hu₀ : ¬ (p : ℤ) ∣ u₀)
    (hv₀ : ¬ (p : ℤ) ∣ v₀) :
    ExactPow p (e₁ + e₂) m' ∧ ExactPow p (e₁ + e₂) (m' * S') := by
  have hm' : ExactPow p (e₁ + e₂) m' := by
    rw [hm, hu, hv]
    have := ((ExactPow.mk (e := e₁) hu₀).mul hp (ExactPow.mk (e := e₂) hv₀)).mul hp
      (ExactPow.of_not_dvd hw)
    simpa using this
  exact ⟨hm', by simpa using hm'.mul hp (ExactPow.of_not_dvd hS)⟩

/-- From `A² (m' - κ) = m' S'`, the exact powers of `m' - κ` and `m' S'` give that of `A²`. -/
theorem exactPow_A_sq (hA0 : A ≠ 0) (hA : A ^ 2 * (m' - κ) = m' * S') {a b : ℕ}
    (hmk : ExactPow p a (m' - κ)) (hmS : ExactPow p (a + b) (m' * S')) :
    ExactPow p b (A ^ 2) := by
  obtain ⟨j, hj⟩ := ExactPow.exists_of_ne_zero hp (pow_ne_zero 2 hA0)
  have := hj.mul hp hmk
  rw [hA] at this
  have := hmS.unique hp this
  obtain rfl : j = b := by omega
  exact hj

/-- `lem:twovar` (i): if `e₁ < e₂` then `v_p(A²) = e₂`. -/
theorem twovar_lt (hm : m' = u * v * w)
    (hR : κ ^ 2 = (u ^ 2 + ε * v ^ 2) * U) (hU : ¬ (p : ℤ) ∣ U) (hw : ¬ (p : ℤ) ∣ w)
    (hS : ¬ (p : ℤ) ∣ S') (hu : u = (p : ℤ) ^ e₁ * u₀) (hv : v = (p : ℤ) ^ e₂ * v₀)
    (hu₀ : ¬ (p : ℤ) ∣ u₀) (hv₀ : ¬ (p : ℤ) ∣ v₀) (hκ : κ ≠ 0) (hA0 : A ≠ 0)
    (hA : A ^ 2 * (m' - κ) = m' * S') (he : e₁ < e₂) : ExactPow p e₂ (A ^ 2) := by
  obtain ⟨hm', hmS⟩ := twovar_mS hp hm hw hS hu hv hu₀ hv₀
  -- `u² + ε v² = p^{2e₁} (u₀² + ε p^{2(e₂ - e₁)} v₀²)`, the bracket prime to `p`
  have hF : ExactPow p (2 * e₁) (u ^ 2 + ε * v ^ 2) := by
    refine ⟨u₀ ^ 2 + ε * (p : ℤ) ^ (2 * (e₂ - e₁)) * v₀ ^ 2, ?_, fun h => hu₀ ?_⟩
    · rw [hu, hv]
      have : (p : ℤ) ^ (2 * e₂) = (p : ℤ) ^ (2 * e₁) * (p : ℤ) ^ (2 * (e₂ - e₁)) := by
        rw [← pow_add]; congr 1; omega
      rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm e₁ 2, mul_comm e₂ 2, this]; ring
    · have h2 : (p : ℤ) ∣ ε * (p : ℤ) ^ (2 * (e₂ - e₁)) * v₀ ^ 2 :=
        ((dvd_pow_self _ (by omega)).mul_left ε).mul_right _
      exact dvd_of_dvd_sq' hp ((dvd_add_left h2).mp h)
  have hk2 : ExactPow p (2 * e₁) (κ ^ 2) := by
    rw [hR]; simpa using hF.mul hp (ExactPow.of_not_dvd hU)
  obtain ⟨j, hj, hκe⟩ := hk2.of_sq hp hκ
  have hje : e₁ = j := by omega
  subst hje
  have hmk : ExactPow p e₁ (m' - κ) := by
    rw [sub_eq_neg_add]
    exact hκe.neg.add_of_dvd ((pow_dvd_pow _ (by omega)).trans hm'.dvd)
  exact exactPow_A_sq hp hA0 hA hmk hmS

/-- `lem:twovar` (ii), `δ = 0`: if `e₁ = e₂ = e ≥ 1` and `p ∤ u₀² + ε v₀²` then
`v_p(A²) = e`. -/
theorem twovar_eq_good (hm : m' = u * v * w)
    (hR : κ ^ 2 = (u ^ 2 + ε * v ^ 2) * U) (hU : ¬ (p : ℤ) ∣ U) (hw : ¬ (p : ℤ) ∣ w)
    (hS : ¬ (p : ℤ) ∣ S') (hu : u = (p : ℤ) ^ e₁ * u₀) (hv : v = (p : ℤ) ^ e₁ * v₀)
    (hu₀ : ¬ (p : ℤ) ∣ u₀) (hv₀ : ¬ (p : ℤ) ∣ v₀) (hκ : κ ≠ 0) (hA0 : A ≠ 0)
    (hA : A ^ 2 * (m' - κ) = m' * S') (he : 1 ≤ e₁) (hN : ¬ (p : ℤ) ∣ u₀ ^ 2 + ε * v₀ ^ 2) :
    ExactPow p e₁ (A ^ 2) := by
  obtain ⟨hm', hmS⟩ := twovar_mS hp hm hw hS hu hv hu₀ hv₀
  have hF : ExactPow p (2 * e₁) (u ^ 2 + ε * v ^ 2) :=
    ⟨u₀ ^ 2 + ε * v₀ ^ 2, by rw [hu, hv, pow_mul]; ring, hN⟩
  have hk2 : ExactPow p (2 * e₁) (κ ^ 2) := by
    rw [hR]; simpa using hF.mul hp (ExactPow.of_not_dvd hU)
  obtain ⟨j, hj, hκe⟩ := hk2.of_sq hp hκ
  have hje : e₁ = j := by omega
  subst hje
  have hmk : ExactPow p e₁ (m' - κ) := by
    rw [sub_eq_neg_add]
    exact hκe.neg.add_of_dvd ((pow_dvd_pow _ (by omega)).trans hm'.dvd)
  exact exactPow_A_sq hp hA0 hA hmk hmS

/-- `lem:twovar` (ii), `δ > 0`: if `e₁ = e₂ = e ≥ 1` and `p ∣ u₀² + ε v₀²` then
`pᵉ ∤ A²`. -/
theorem twovar_eq_bad (hm : m' = u * v * w)
    (hR : κ ^ 2 = (u ^ 2 + ε * v ^ 2) * U) (hw : ¬ (p : ℤ) ∣ w)
    (hS : ¬ (p : ℤ) ∣ S') (hu : u = (p : ℤ) ^ e₁ * u₀) (hv : v = (p : ℤ) ^ e₁ * v₀)
    (hu₀ : ¬ (p : ℤ) ∣ u₀) (hv₀ : ¬ (p : ℤ) ∣ v₀) (hκ : κ ≠ 0)
    (hA : A ^ 2 * (m' - κ) = m' * S') (he : 1 ≤ e₁) (hN : (p : ℤ) ∣ u₀ ^ 2 + ε * v₀ ^ 2) :
    ¬ (p : ℤ) ^ e₁ ∣ A ^ 2 := by
  obtain ⟨hm', hmS⟩ := twovar_mS hp hm hw hS hu hv hu₀ hv₀
  -- `p^{2e+1} ∣ κ²`, so `p^{e+1} ∣ κ`
  have hF : (p : ℤ) ^ (2 * e₁ + 1) ∣ κ ^ 2 := by
    rw [hR, pow_succ]
    obtain ⟨N, hN⟩ := hN
    exact ⟨N * U, by rw [hu, hv, pow_mul]; linear_combination (p : ℤ) ^ (e₁ * 2) * U * hN⟩
  obtain ⟨j, hj⟩ := ExactPow.exists_of_ne_zero hp hκ
  have hj2 : ExactPow p (j + j) (κ ^ 2) := by rw [sq]; exact hj.mul hp hj
  have hjle : 2 * e₁ + 1 ≤ j + j := (hj2.dvd_iff hp).mp hF
  have hk : (p : ℤ) ^ (e₁ + 1) ∣ κ := (hj.dvd_iff hp).mpr (by omega)
  have hmk : (p : ℤ) ^ (e₁ + 1) ∣ m' - κ :=
    dvd_sub ((pow_dvd_pow _ (by omega)).trans hm'.dvd) hk
  intro hAd
  have : (p : ℤ) ^ (e₁ + e₁ + 1) ∣ m' * S' := by
    rw [← hA, add_assoc, pow_add]; exact mul_dvd_mul hAd hmk
  exact hmS.not_dvd_succ hp this

end twovar

end PerfectCuboid
