import PerfectCuboid.Integrality
import PerfectCuboid.Case1Param

/-!
# The paper's numerical examples

* `no_cuboid_of`: a triple with `R = K²` (`K > 0`) whose `A² = mS/(m - K)` is a natural
  number that is not a square comes from no cuboid (the branch is forced: `κ = K`).
* `no_cuboid_423_399_329`, `no_cuboid_1287_507_473`: the two triples of Table 1 that
  survive to the line `A² ∈ ℤ`; with the integrality data `m₁ = 56259`, `e = 11`,
  `A² = 618849` and `m₁ = 719433`, `e = 113`, `A² = 81295929` (`table1_data`).
* `generic_example`: `rem:generic`, the triple `(723, 559, 507)`: `R` is a square, `Q > 0`,
  `A² = 6212027809/4929` with `v₃(A²) = -1` (so `(m - κ) ∤ mS`), and `3` is a bad prime of
  `thm:converse-full` (`3 ∥ 723`, `3 ∥ 507`, `3 ∤ 559`, `9 ∣ 241² - 169² = 29520`).
All numerical facts are checked by `norm_num` (kernel arithmetic, no `native_decide`).
-/

namespace PerfectCuboid

/-- A triple whose forced `A²` is a non-square natural number comes from no cuboid. -/
theorem no_cuboid_of {x y z K : ℤ} {A2 : ℕ} (hx : Odd x) (hy : Odd y) (hz : Odd z)
    (hz0 : 0 < z) (hzy : z < y) (hyx : y < x) (hK : 0 < K) (hK2 : K ^ 2 = R x y z)
    (hmK : m x y z - K ≠ 0) (hA2 : (A2 : ℤ) * (m x y z - K) = m x y z * S x y z)
    (hns : ¬ IsSquare A2) : ¬ ∃ c : Cuboid, c.x = x ∧ c.y = y ∧ c.z = z := by
  rintro ⟨c, rfl, rfl, rfl⟩
  have hm : m c.x c.y c.z ≠ 0 := by unfold m; have := c.x_pos; have := c.y_pos; positivity
  obtain ⟨κ, hκ, hκ2⟩ := exists_kappa hm c.master_eq
  have hsimp := simplified (Q_ne_zero hx hy hz) hκ hκ2
  have hpos := kappa_pos c.x_pos hz0 hzy hyx hκ2 hsimp c.x_sq_lt_A_sq
  have hκK : κ = K := by
    have h0 : (κ - K) * (κ + K) = 0 := by linear_combination hκ2 - hK2
    rcases mul_eq_zero.mp h0 with h | h
    · linarith
    · linarith
  subst hκK
  have hA : ((c.A ^ 2 : ℕ) : ℤ) = (A2 : ℤ) := by
    push_cast
    exact mul_right_cancel₀ hmK (hsimp.trans hA2.symm)
  exact hns ⟨c.A, by rw [← sq]; exact_mod_cast hA.symm⟩

/-- Table 1: `(423, 399, 329)` comes from no cuboid (`A² = 618849` is not a square). -/
theorem no_cuboid_423_399_329 : ¬ ∃ c : Cuboid, c.x = 423 ∧ c.y = 399 ∧ c.z = 329 :=
  no_cuboid_of (K := 34900320) (A2 := 618849) ⟨211, by norm_num⟩ ⟨199, by norm_num⟩
    ⟨164, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [R]) (by norm_num [m]) (by norm_num [m, S]) (by norm_num)

/-- Table 1: `(1287, 507, 473)` comes from no cuboid (`A² = 81295929` is not a square). -/
theorem no_cuboid_1287_507_473 : ¬ ∃ c : Cuboid, c.x = 1287 ∧ c.y = 507 ∧ c.z = 473 :=
  no_cuboid_of (K := 302221920) (A2 := 81295929) ⟨643, by norm_num⟩ ⟨253, by norm_num⟩
    ⟨236, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [R]) (by norm_num [m]) (by norm_num [m, S]) (by norm_num)

/-- Table 1: the integrality data of the two survivors (`prop:integrality`): `h = gcd(m, κ)`,
`m₁ = m/h`, `d = m₁ - κ/h`, `S = d e`, `A² = m₁ e`, and `Q > 0`. -/
theorem table1_data :
    (Int.gcd (m 423 399 329) 34900320 = 987 ∧ m 423 399 329 = 987 * 56259 ∧
      (34900320 : ℤ) = 987 * 35360 ∧ S 423 399 329 = (56259 - 35360) * 11 ∧
      (618849 : ℤ) = 56259 * 11 ∧ 0 < Q 423 399 329) ∧
    (Int.gcd (m 1287 507 473) 302221920 = 429 ∧ m 1287 507 473 = 429 * 719433 ∧
      (302221920 : ℤ) = 429 * 704480 ∧ S 1287 507 473 = (719433 - 704480) * 113 ∧
      (81295929 : ℤ) = 719433 * 113 ∧ 0 < Q 1287 507 473) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;>
    first | (norm_num [m]; rfl) | norm_num [m, S, Q]

/-- `rem:generic`: the triple `(723, 559, 507)`. -/
theorem generic_example :
    (110906640 : ℤ) ^ 2 = R 723 559 507 ∧ 0 < Q 723 559 507 ∧
    ((6212027809 : ℚ) / 4929) * ((m 723 559 507 - 110906640 : ℤ) : ℚ) =
      ((m 723 559 507 * S 723 559 507 : ℤ) : ℚ) ∧
    ¬ (m 723 559 507 - 110906640) ∣ m 723 559 507 * S 723 559 507 ∧
    ¬ (3 : ℤ) ∣ 6212027809 ∧ (4929 : ℤ) = 3 * 1643 ∧ ¬ (3 : ℤ) ∣ 1643 ∧
    BadPrime 723 559 507 3 := by
  refine ⟨by norm_num [R], by norm_num [Q], by norm_num [m, S], by norm_num [m, S],
    by norm_num, by norm_num, by norm_num, Nat.prime_three, 1, Or.inr (Or.inl ⟨⟨le_rfl, 241, 169,
      by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩, by norm_num⟩)⟩

end PerfectCuboid
