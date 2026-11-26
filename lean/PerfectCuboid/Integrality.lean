import PerfectCuboid.Kernels

/-!
# Section 6: `prop:integrality` and `cor:sf`

With `h = gcd(m, κ)`, `m = h m₁`, `κ = h k₁` and `d = m₁ - k₁`:
* `integrality`: `prop:integrality`; `gcd(d, m₁) = 1`, and `A² = mS/(m - κ)` is an integer
  (i.e. `(m - κ) ∣ mS`) iff `d ∣ S`. Stated for any factorization `m = g m₁`, `κ = g k₁`
  with `m₁, k₁` coprime; `integrality_gcd` is the paper's `g = gcd(m, κ)`.
* `A_sq_eq_mul`: then `A² = m₁ e` with `S = d e`.
* `isSquare_mul_iff`: `cor:sf`; with `m₁ = s² δ`, `δ` squarefree (the squarefree kernel of
  `m₁`), `m₁ e` is a square iff `e = δ w²`, i.e. iff `e` has the same squarefree kernel.
  (Mathlib has no squarefree-kernel function, so the kernel of `m₁` is given by such a
  factorization, which always exists: `exists_sq_mul_squarefree`.)
* `sf_lt`: the necessary condition `sf(m₁) < 2x²` of `cor:sf`.
-/

namespace PerfectCuboid

/-- `prop:integrality`. -/
theorem integrality {m κ S g m₁ k₁ : ℤ} (hg : g ≠ 0) (hm : m = g * m₁) (hk : κ = g * k₁)
    (hc : IsCoprime m₁ k₁) :
    IsCoprime (m₁ - k₁) m₁ ∧ ((m - κ) ∣ m * S ↔ (m₁ - k₁) ∣ S) := by
  have hc' : IsCoprime (m₁ - k₁) m₁ := by
    obtain ⟨u, v, huv⟩ := hc
    exact ⟨-v, u + v, by linear_combination huv⟩
  refine ⟨hc', ?_⟩
  rw [hm, hk, show g * m₁ - g * k₁ = g * (m₁ - k₁) by ring,
    show g * m₁ * S = g * (m₁ * S) by ring, mul_dvd_mul_iff_left hg]
  exact ⟨fun h => hc'.dvd_of_dvd_mul_left h, fun h => h.mul_left _⟩

/-- `prop:integrality` with `h = gcd(m, κ)`, `m₁ = m/h`, `k₁ = κ/h`. -/
theorem integrality_gcd {m κ S : ℤ} (hm : m ≠ 0) :
    IsCoprime (m / Int.gcd m κ - κ / Int.gcd m κ) (m / Int.gcd m κ) ∧
      ((m - κ) ∣ m * S ↔ (m / Int.gcd m κ - κ / Int.gcd m κ) ∣ S) := by
  have hpos : 0 < Int.gcd m κ := Int.gcd_pos_of_ne_zero_left κ hm
  exact integrality (g := Int.gcd m κ) (by exact_mod_cast hpos.ne')
    (Int.mul_ediv_cancel' (Int.gcd_dvd_left m κ)).symm (Int.mul_ediv_cancel' (Int.gcd_dvd_right m κ)).symm
    (Int.isCoprime_iff_gcd_eq_one.mpr (Int.gcd_div_gcd_div_gcd hpos))

/-- `prop:integrality`: in the integral case `A² = m₁ e` with `e = S/d`. -/
theorem A_sq_eq_mul {A m κ S g m₁ k₁ e : ℤ} (hg : g ≠ 0) (hd : m₁ - k₁ ≠ 0)
    (hm : m = g * m₁) (hk : κ = g * k₁) (he : S = (m₁ - k₁) * e)
    (hA : A ^ 2 * (m - κ) = m * S) : A ^ 2 = m₁ * e := by
  apply mul_left_cancel₀ (mul_ne_zero hg hd)
  rw [hm, hk, he] at hA
  linear_combination hA

/-- If `a² b = c²` with `a ≠ 0` then `b` is a square (over `ℤ`). -/
theorem exists_sq_of_sq_mul_eq_sq_int {a b c : ℤ} (ha : a ≠ 0) (h : a ^ 2 * b = c ^ 2) :
    ∃ t, b = t ^ 2 := by
  obtain ⟨t, rfl⟩ : a ∣ c := (Int.pow_dvd_pow_iff two_ne_zero).mp ⟨b, h.symm⟩
  exact ⟨t, mul_left_cancel₀ (pow_ne_zero 2 ha) (by rw [h, mul_pow])⟩

/-- `cor:sf`: with `m₁ = s² δ`, `δ` squarefree, `m₁ e` is a square iff `e = δ w²`. -/
theorem isSquare_mul_iff {m₁ e s δ : ℤ} (hs : s ≠ 0) (hm : m₁ = s ^ 2 * δ) (hδ : Squarefree δ) :
    IsSquare (m₁ * e) ↔ ∃ w, e = δ * w ^ 2 := by
  have hδ0 : δ ≠ 0 := by rintro rfl; exact not_squarefree_zero hδ
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨t, ht⟩ := exists_sq_of_sq_mul_eq_sq_int (b := δ * e) hs (c := c)
      (by rw [← sq] at hc; rw [← hc, hm]; ring)
    obtain ⟨w, rfl⟩ : δ ∣ t := (hδ.dvd_pow_iff_dvd two_ne_zero).mp ⟨e, ht.symm⟩
    exact ⟨w, mul_left_cancel₀ hδ0 (by rw [ht]; ring)⟩
  · rintro ⟨w, rfl⟩
    exact ⟨s * δ * w, by rw [hm]; ring⟩

/-- `cor:sf`: the necessary condition `sf(m₁) < 2x²`. Here `e = S/d ≥ 1` with `d ≥ 1`
(from `Q > 0`), and `δ` is the squarefree kernel of `m₁`. -/
theorem sf_lt {x y z m₁ e s δ D : ℤ} (hz : 0 < z) (hyx : y < x) (hzy : z < y)
    (hD : 0 < D) (hS : S x y z = D * e) (he : 0 < e) (hs : s ≠ 0) (hm : m₁ = s ^ 2 * δ)
    (hδ : Squarefree δ) (hsq : IsSquare (m₁ * e)) : δ < 2 * x ^ 2 := by
  obtain ⟨w, hw⟩ := (isSquare_mul_iff hs hm hδ).mp hsq
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw; omega
  have h1 : δ ≤ e := by
    rw [hw]; have : 1 ≤ w ^ 2 := by have := pow_pos (abs_pos.mpr hw0) 2; rw [sq_abs] at this; omega
    nlinarith
  have h2 : e ≤ S x y z := by rw [hS]; nlinarith
  have h3 : S x y z < 2 * x ^ 2 := by
    unfold S
    have := pow_lt_pow_left₀ hyx (hz.trans hzy).le two_ne_zero
    have := pow_pos hz 2
    linarith
  linarith

end PerfectCuboid
