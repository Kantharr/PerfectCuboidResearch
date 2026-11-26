import PerfectCuboid.Basic

/-!
# The master equation and the surviving branch (Sections 2.3 and 3)

For integers `x, y, z` put `m = xyz`, `S = x² + y² - z²`, `Q = x²z² + y²z² - x²y²` and
`R = (x² + y²)(x² - z²)(y² - z²)`.

* `master`: `thm:master`, `Q A⁴ - 2 m² A² + m² S = 0`.
* `identity`: `prop:identity`, `m² - R = S Q`.
* `Q_mod_eight`, `Q_ne_zero`: `prop:u0`; for odd `x, y, z`, `Q ≡ 1 (mod 8)`, so `Q ≠ 0`.
* `sq_eq_mul_R`, `exists_kappa`: `prop:radicand`; `(Q A² - m²)² = m² R`, so `R = κ²` for the
  integer `κ = (Q A² - m²)/m`, which is `±√R`.
* `simplified`: `cor:simplified`, `A² (m - κ) = m S`.
* `kappa_pos`: `thm:minus`; `κ > 0`, i.e. the branch `κ = -√R` (which would give
  `A² < x²`, so `B < 0`) never occurs. Hence `A² = m S/(m - √R)`.
* `Q_pos`: `prop:positivity`; `0 < Q`, i.e. `x² (y² - z²) < y² z²`, and `κ < m`.
* `Cuboid.necessary`: the whole chain for a cuboid in normal form.

`κ` is defined from `A`, so the branch is decided by the cuboid rather than chosen.
-/

namespace PerfectCuboid

/-- `m = xyz`. -/
def m (x y z : ℤ) : ℤ := x * y * z
/-- `S = x² + y² - z²`. -/
def S (x y z : ℤ) : ℤ := x ^ 2 + y ^ 2 - z ^ 2
/-- `Q = x²z² + y²z² - x²y²`. -/
def Q (x y z : ℤ) : ℤ := x ^ 2 * z ^ 2 + y ^ 2 * z ^ 2 - x ^ 2 * y ^ 2
/-- `R = (x² + y²)(x² - z²)(y² - z²)`, the radicand. -/
def R (x y z : ℤ) : ℤ := (x ^ 2 + y ^ 2) * (x ^ 2 - z ^ 2) * (y ^ 2 - z ^ 2)

/-- `prop:identity`: `m² - R = S Q`. -/
theorem identity (x y z : ℤ) : m x y z ^ 2 - R x y z = S x y z * Q x y z := by
  unfold m R S Q; ring

/-- `thm:master`. -/
theorem master {A B C D x y z : ℤ} (hB : A ^ 2 - x ^ 2 = 2 * B * x)
    (hC : A ^ 2 - y ^ 2 = 2 * C * y) (hD : A ^ 2 + z ^ 2 = 2 * D * z)
    (hcub : A ^ 2 + B ^ 2 + C ^ 2 = D ^ 2) :
    Q x y z * A ^ 4 - 2 * m x y z ^ 2 * A ^ 2 + m x y z ^ 2 * S x y z = 0 := by
  unfold Q m S
  linear_combination (4 * x ^ 2 * y ^ 2 * z ^ 2) * hcub
    + (y ^ 2 * z ^ 2) * (A ^ 2 - x ^ 2 + 2 * B * x) * hB
    + (x ^ 2 * z ^ 2) * (A ^ 2 - y ^ 2 + 2 * C * y) * hC
    - (x ^ 2 * y ^ 2) * (A ^ 2 + z ^ 2 + 2 * D * z) * hD

/-- An odd integer read modulo `8` is `2u + 1`. -/
theorem odd_cast_zmod8 {x : ℤ} (hx : Odd x) : ∃ u : ZMod 8, (x : ZMod 8) = 2 * u + 1 := by
  obtain ⟨a, rfl⟩ := hx
  exact ⟨a, by push_cast; ring⟩

/-- `prop:u0`, in the sharper form `Q ≡ 1 (mod 8)` for odd `x, y, z`. -/
theorem Q_mod_eight {x y z : ℤ} (hx : Odd x) (hy : Odd y) (hz : Odd z) :
    (Q x y z : ZMod 8) = 1 := by
  obtain ⟨u, hu⟩ := odd_cast_zmod8 hx
  obtain ⟨v, hv⟩ := odd_cast_zmod8 hy
  obtain ⟨w, hw⟩ := odd_cast_zmod8 hz
  unfold Q
  push_cast
  rw [hu, hv, hw]
  clear hu hv hw
  revert u v w
  decide

/-- `prop:u0`: `Q ≠ 0`. -/
theorem Q_ne_zero {x y z : ℤ} (hx : Odd x) (hy : Odd y) (hz : Odd z) : Q x y z ≠ 0 := by
  intro h
  have := Q_mod_eight hx hy hz
  rw [h, Int.cast_zero] at this
  exact absurd this (by decide)

/-- `prop:radicand`, first form: completing the square in the master equation. -/
theorem sq_eq_mul_R {A x y z : ℤ}
    (h : Q x y z * A ^ 4 - 2 * m x y z ^ 2 * A ^ 2 + m x y z ^ 2 * S x y z = 0) :
    (Q x y z * A ^ 2 - m x y z ^ 2) ^ 2 = m x y z ^ 2 * R x y z := by
  linear_combination Q x y z * h + m x y z ^ 2 * identity x y z

/-- `prop:radicand`: `R` is the square of `κ = (Q A² - m²)/m`, an integer. -/
theorem exists_kappa {A x y z : ℤ} (hm : m x y z ≠ 0)
    (h : Q x y z * A ^ 4 - 2 * m x y z ^ 2 * A ^ 2 + m x y z ^ 2 * S x y z = 0) :
    ∃ κ : ℤ, m x y z * κ = Q x y z * A ^ 2 - m x y z ^ 2 ∧ κ ^ 2 = R x y z := by
  have hsq := sq_eq_mul_R h
  obtain ⟨κ, hκ⟩ : m x y z ∣ Q x y z * A ^ 2 - m x y z ^ 2 :=
    (Int.pow_dvd_pow_iff two_ne_zero).mp ⟨R x y z, by rw [hsq]⟩
  refine ⟨κ, hκ.symm, ?_⟩
  rw [hκ, mul_pow] at hsq
  exact mul_left_cancel₀ (pow_ne_zero 2 hm) hsq

/-- `cor:simplified`: `A² (m - κ) = m S`. -/
theorem simplified {A x y z κ : ℤ} (hQ : Q x y z ≠ 0)
    (hκ : m x y z * κ = Q x y z * A ^ 2 - m x y z ^ 2) (hκ2 : κ ^ 2 = R x y z) :
    A ^ 2 * (m x y z - κ) = m x y z * S x y z := by
  apply mul_left_cancel₀ hQ
  linear_combination (-(m x y z - κ)) * hκ + m x y z * identity x y z - m x y z * hκ2

/-- `thm:minus`: the cuboid lies on the branch `κ = +√R`. If `κ ≤ 0` then `A² < x²`,
contradicting `B > 0`. -/
theorem kappa_pos {A x y z κ : ℤ} (hx : 0 < x) (hz : 0 < z) (hzy : z < y) (hyx : y < x)
    (hκ2 : κ ^ 2 = R x y z) (hA : A ^ 2 * (m x y z - κ) = m x y z * S x y z)
    (hAx : x ^ 2 < A ^ 2) : 0 < κ := by
  by_contra hle
  replace hle := not_lt.mp hle
  have hy : 0 < y := hz.trans hzy
  have hm : 0 < m x y z := by unfold m; positivity
  set K := -κ with hK
  have hK0 : 0 ≤ K := by omega
  have hmK : 0 < m x y z + K := by omega
  -- `x² (m + K) < A² (m + K) = m S`, so `x² K < m (y² - z²)`
  have h1 : x ^ 2 * (m x y z + K) < m x y z * S x y z := by
    rw [← hA, show m x y z - κ = m x y z + K by omega]
    exact mul_lt_mul_of_pos_right hAx hmK
  have h2 : x ^ 2 * K < m x y z * (y ^ 2 - z ^ 2) := by unfold S at h1; linarith
  have h3 : (x ^ 2 * K) ^ 2 < (m x y z * (y ^ 2 - z ^ 2)) ^ 2 :=
    pow_lt_pow_left₀ h2 (by positivity) two_ne_zero
  have hK2 : K ^ 2 = R x y z := by rw [hK, neg_sq]; exact hκ2
  -- but `x²(x² + y²)(x² - z²) > y² z² (y² - z²)` factor by factor
  have p1 : y ^ 2 < x ^ 2 := pow_lt_pow_left₀ hyx hy.le two_ne_zero
  have p2 : z ^ 2 < x ^ 2 + y ^ 2 := by
    have := pow_lt_pow_left₀ hzy hz.le two_ne_zero; nlinarith
  have hyz : 0 < y ^ 2 - z ^ 2 := by
    have := pow_lt_pow_left₀ hzy hz.le two_ne_zero; linarith
  have p3 : y ^ 2 - z ^ 2 < x ^ 2 - z ^ 2 := by linarith
  have key : y ^ 2 * z ^ 2 * (y ^ 2 - z ^ 2) < x ^ 2 * (x ^ 2 + y ^ 2) * (x ^ 2 - z ^ 2) :=
    mul_lt_mul'' (mul_lt_mul'' p1 p2 (by positivity) (by positivity)) p3
      (by positivity) hyz.le
  have hpos : 0 < x ^ 2 * (y ^ 2 - z ^ 2) := by positivity
  have := mul_lt_mul_of_pos_left key hpos
  have e1 : (x ^ 2 * K) ^ 2 =
      x ^ 2 * (y ^ 2 - z ^ 2) * (x ^ 2 * (x ^ 2 + y ^ 2) * (x ^ 2 - z ^ 2)) := by
    rw [mul_pow, hK2]; unfold R; ring
  have e2 : (m x y z * (y ^ 2 - z ^ 2)) ^ 2 =
      x ^ 2 * (y ^ 2 - z ^ 2) * (y ^ 2 * z ^ 2 * (y ^ 2 - z ^ 2)) := by unfold m; ring
  linarith

/-- `prop:positivity`: on the surviving branch `0 < κ < m` and `Q > 0`. -/
theorem Q_pos {A x y z κ : ℤ} (hx : 0 < x) (hz : 0 < z) (hzy : z < y)
    (hκ : 0 < κ) (hκ2 : κ ^ 2 = R x y z) (hA0 : A ≠ 0)
    (hA : A ^ 2 * (m x y z - κ) = m x y z * S x y z) :
    κ < m x y z ∧ 0 < Q x y z := by
  have hy : 0 < y := hz.trans hzy
  have hm : 0 < m x y z := by unfold m; positivity
  have hS : 0 < S x y z := by
    unfold S; have := pow_lt_pow_left₀ hzy hz.le two_ne_zero; nlinarith
  have hA2 : 0 < A ^ 2 := by positivity
  have hmk : 0 < m x y z - κ := by
    have : 0 < A ^ 2 * (m x y z - κ) := by rw [hA]; positivity
    exact pos_of_mul_pos_right this hA2.le
  refine ⟨by linarith, ?_⟩
  have hSQ : S x y z * Q x y z = (m x y z - κ) * (m x y z + κ) := by
    rw [← identity, ← hκ2]; ring
  have : 0 < S x y z * Q x y z := by rw [hSQ]; exact mul_pos hmk (by linarith)
  exact pos_of_mul_pos_right this hS.le

/-- `prop:positivity`, as an inequality in `x, y, z`. -/
theorem Q_pos_iff (x y z : ℤ) : 0 < Q x y z ↔ x ^ 2 * (y ^ 2 - z ^ 2) < y ^ 2 * z ^ 2 := by
  unfold Q; constructor <;> intro h <;> linarith

namespace Cuboid

variable (c : Cuboid)

/-- `thm:master` for a cuboid. -/
theorem master_eq : Q c.x c.y c.z * (c.A : ℤ) ^ 4 - 2 * m c.x c.y c.z ^ 2 * (c.A : ℤ) ^ 2 +
    m c.x c.y c.z ^ 2 * S c.x c.y c.z = 0 :=
  master c.param_B c.param_C c.param_D c.hD_int

/-- `A² > x²`, from `B > 0`. -/
theorem x_sq_lt_A_sq : c.x ^ 2 < (c.A : ℤ) ^ 2 := by
  have := c.param_B
  have hB : (0 : ℤ) < c.B := by exact_mod_cast c.hB
  have := mul_pos (mul_pos two_pos hB) c.x_pos
  linarith

/-- The necessary conditions of Sections 2 and 3, for a cuboid in normal form (`A` the odd
edge, `B < C`): `x > y > z > 0` all odd, `Q > 0`, and `R = κ²` with `0 < κ < m` and
`A² (m - κ) = m S`. -/
theorem necessary (hA : Odd c.A) (hBC : c.B < c.C) :
    Odd c.x ∧ Odd c.y ∧ Odd c.z ∧ c.y < c.x ∧ c.z < c.y ∧ 0 < c.z ∧
    0 < Q c.x c.y c.z ∧
    ∃ κ : ℤ, κ ^ 2 = R c.x c.y c.z ∧ 0 < κ ∧ κ < m c.x c.y c.z ∧
      (c.A : ℤ) ^ 2 * (m c.x c.y c.z - κ) = m c.x c.y c.z * S c.x c.y c.z := by
  obtain ⟨ox, oy, oz⟩ := c.odd_xyz hA
  obtain ⟨hyx, hzy, hz⟩ := c.order hBC
  have hm : m c.x c.y c.z ≠ 0 := by unfold m; have := c.x_pos; have := c.y_pos; positivity
  obtain ⟨κ, hκ, hκ2⟩ := exists_kappa hm c.master_eq
  have hsimp := simplified (Q_ne_zero ox oy oz) hκ hκ2
  have hpos := kappa_pos c.x_pos hz hzy hyx hκ2 hsimp c.x_sq_lt_A_sq
  obtain ⟨hlt, hQ⟩ := Q_pos c.x_pos hz hzy hpos hκ2 (by exact_mod_cast c.hA.ne') hsimp
  exact ⟨ox, oy, oz, hyx, hzy, hz, hQ, κ, hκ2, hpos, hlt, hsimp⟩

end Cuboid

end PerfectCuboid
