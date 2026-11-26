import PerfectCuboid.Master

/-!
# The converse (Section 3.1): `prop:converse` and `lem:onevar`

Throughout, `x > y > z > 0` are odd, `R = κ²` with `κ > 0`, and `A > 0` satisfies the
surviving-branch equation `A² (m - κ) = m S`.

* `A_sq_mul_Q`: `A² Q = m (m + κ)` (multiply the branch equation by `m + κ` and use
  `(m - κ)(m + κ) = S Q`). This identity drives everything below.
* `master_of_branch`: conversely the branch equation gives `thm:master`.
* `converse`: `prop:converse`. With `B, C, D` defined by `prop:param`, `(A, B, C)` is a
  perfect cuboid iff `x, y, z ∣ A²`. Neither `gcd(x, y, z) = 1` nor `Q > 0` is needed, and
  `A` is odd simply because `A² (m - κ) = m S` is odd (the paper uses `v₂(R) ≥ 7`).
* `dvd_A_sq_of_coprime_x`, `_y`, `_z`: `lem:onevar` in a stronger form. Since
  `Q ≡ y²z² (mod x)`, any divisor of `x` coprime to `yz` divides `A² Q = m (m + κ)` and is
  coprime to `Q`, so it divides `A²`; likewise for `y` (`Q ≡ x²z²`) and `z` (`Q ≡ -x²y²`).
  `onevar` is the paper's statement: `p^e ∣ A²` when `p^e ∣ x` and `p ∤ yz`.
-/

namespace PerfectCuboid

/-- `A² Q = m (m + κ)`. -/
theorem A_sq_mul_Q {A x y z κ : ℤ} (hS : S x y z ≠ 0) (hκ2 : κ ^ 2 = R x y z)
    (hA : A ^ 2 * (m x y z - κ) = m x y z * S x y z) :
    A ^ 2 * Q x y z = m x y z * (m x y z + κ) := by
  apply mul_left_cancel₀ hS
  linear_combination (m x y z + κ) * hA - A ^ 2 * identity x y z + A ^ 2 * hκ2

/-- The branch equation implies `thm:master`. -/
theorem master_of_branch {A x y z κ : ℤ} (hS : S x y z ≠ 0) (hQ : Q x y z ≠ 0)
    (hκ2 : κ ^ 2 = R x y z) (hA : A ^ 2 * (m x y z - κ) = m x y z * S x y z) :
    Q x y z * A ^ 4 - 2 * m x y z ^ 2 * A ^ 2 + m x y z ^ 2 * S x y z = 0 := by
  have h := A_sq_mul_Q hS hκ2 hA
  apply mul_left_cancel₀ hQ
  linear_combination (A ^ 2 * Q x y z + m x y z * (m x y z + κ) - 2 * m x y z ^ 2) * h
    - m x y z ^ 2 * identity x y z + m x y z ^ 2 * hκ2

/-- Basic positivity on the branch: `m, S > 0`, `m - κ > 0`, and `A² > x²`. -/
theorem branch_facts {A x y z κ : ℤ} (hz : 0 < z) (hzy : z < y) (hyx : y < x) (hκ : 0 < κ)
    (hA0 : A ≠ 0) (hA : A ^ 2 * (m x y z - κ) = m x y z * S x y z) :
    0 < m x y z ∧ 0 < S x y z ∧ 0 < m x y z - κ ∧ x ^ 2 < A ^ 2 := by
  have hy : 0 < y := hz.trans hzy
  have hx : 0 < x := hy.trans hyx
  have hm : 0 < m x y z := by unfold m; positivity
  have hzy2 : z ^ 2 < y ^ 2 := pow_lt_pow_left₀ hzy hz.le two_ne_zero
  have hS : 0 < S x y z := by unfold S; nlinarith
  have hA2 : 0 < A ^ 2 := by positivity
  have hmk : 0 < m x y z - κ := by
    have : 0 < A ^ 2 * (m x y z - κ) := by rw [hA]; positivity
    exact pos_of_mul_pos_right this hA2.le
  refine ⟨hm, hS, hmk, ?_⟩
  -- `(A² - x²)(m - κ) = m (y² - z²) + x² κ > 0`
  have h : (A ^ 2 - x ^ 2) * (m x y z - κ) = m x y z * (y ^ 2 - z ^ 2) + x ^ 2 * κ := by
    unfold S at hA; linear_combination hA
  have : 0 < (A ^ 2 - x ^ 2) * (m x y z - κ) := by
    rw [h]; have : 0 < y ^ 2 - z ^ 2 := by linarith
    positivity
  have := pos_of_mul_pos_left this hmk.le
  linarith

/-- For odd `u`, `2u ∣ n` iff `2 ∣ n` and `u ∣ n`. -/
theorem two_mul_dvd_of_odd {u n : ℤ} (hu : Odd u) (h2 : 2 ∣ n) (hn : u ∣ n) : 2 * u ∣ n := by
  have hc : IsCoprime (2 : ℤ) u := by
    rw [Prime.coprime_iff_not_dvd Int.prime_two]
    exact fun h => (Int.not_even_iff_odd.mpr hu) (even_iff_two_dvd.mpr h)
  exact hc.mul_dvd h2 hn

/-- `prop:converse`. -/
theorem converse {x y z κ A : ℤ} (hx : Odd x) (hy : Odd y) (hz : Odd z) (hz0 : 0 < z)
    (hzy : z < y) (hyx : y < x) (hκ : 0 < κ) (hκ2 : κ ^ 2 = R x y z) (hA0 : 0 < A)
    (hA : A ^ 2 * (m x y z - κ) = m x y z * S x y z) :
    (∃ c : Cuboid, (c.A : ℤ) = A ∧ c.x = x ∧ c.y = y ∧ c.z = z) ↔
      (x ∣ A ^ 2 ∧ y ∣ A ^ 2 ∧ z ∣ A ^ 2) := by
  constructor
  · rintro ⟨c, rfl, rfl, rfl, rfl⟩
    refine ⟨⟨c.x + 2 * c.B, ?_⟩, ⟨c.y + 2 * c.C, ?_⟩, ⟨2 * c.D - c.z, ?_⟩⟩
    · linear_combination c.param_B
    · linear_combination c.param_C
    · linear_combination c.param_D
  rintro ⟨dx, dy, dz⟩
  obtain ⟨hm, hS, hmk, hAx⟩ := branch_facts hz0 hzy hyx hκ hA0.ne' hA
  have hy0 : 0 < y := hz0.trans hzy
  have hx0 : 0 < x := hy0.trans hyx
  -- `A` is odd: `A² (m - κ) = m S` is odd
  have hmS : Odd (m x y z * S x y z) := by
    unfold m S
    exact ((hx.mul hy).mul hz).mul ((hx.pow.add_odd hy.pow).sub_odd hz.pow)
  have hAodd : Odd (A ^ 2) := by rw [← hA] at hmS; exact (Int.odd_mul.mp hmS).1
  have hy2 : y ^ 2 < A ^ 2 := lt_trans (pow_lt_pow_left₀ hyx hy0.le two_ne_zero) hAx
  have hz2 : z ^ 2 < A ^ 2 := lt_trans (pow_lt_pow_left₀ hzy hz0.le two_ne_zero) hy2
  -- `B`, `C`, `D` from `prop:param`
  have ev : ∀ {u : ℤ}, Odd u → 2 ∣ A ^ 2 - u ^ 2 ∧ 2 ∣ A ^ 2 + u ^ 2 := fun hu =>
    ⟨even_iff_two_dvd.mp (hAodd.sub_odd hu.pow), even_iff_two_dvd.mp (hAodd.add_odd hu.pow)⟩
  obtain ⟨B, hB⟩ := two_mul_dvd_of_odd hx (ev hx).1 (dvd_sub dx (dvd_pow_self x two_ne_zero))
  obtain ⟨C, hC⟩ := two_mul_dvd_of_odd hy (ev hy).1 (dvd_sub dy (dvd_pow_self y two_ne_zero))
  obtain ⟨D, hD⟩ := two_mul_dvd_of_odd hz (ev hz).2 (dvd_add dz (dvd_pow_self z two_ne_zero))
  have hB0 : 0 < B := by nlinarith
  have hC0 : 0 < C := by nlinarith
  have hD0 : 0 < D := by nlinarith
  have hG0 : 0 < D - z := by nlinarith
  -- the cuboid equation, from `thm:master`
  have hQ : Q x y z ≠ 0 := Q_ne_zero hx hy hz
  have hmaster := master_of_branch hS.ne' hQ hκ2 hA
  have h4 : (4 * m x y z ^ 2) * (A ^ 2 + B ^ 2 + C ^ 2 - D ^ 2) = 0 := by
    unfold Q m S at hmaster; unfold m
    linear_combination hmaster
      - (y ^ 2 * z ^ 2) * (A ^ 2 - x ^ 2 + 2 * B * x) * (hB.trans (by ring) : A ^ 2 - x ^ 2 = 2 * B * x)
      - (x ^ 2 * z ^ 2) * (A ^ 2 - y ^ 2 + 2 * C * y) * (hC.trans (by ring) : A ^ 2 - y ^ 2 = 2 * C * y)
      + (x ^ 2 * y ^ 2) * (A ^ 2 + z ^ 2 + 2 * D * z) * (hD.trans (by ring) : A ^ 2 + z ^ 2 = 2 * D * z)
  have hcub : A ^ 2 + B ^ 2 + C ^ 2 = D ^ 2 := by
    have := (mul_eq_zero.mp h4).resolve_left (mul_ne_zero four_ne_zero (pow_ne_zero 2 hm.ne'))
    linarith
  -- lift everything to `ℕ` and build the cuboid
  lift A to ℕ using hA0.le
  lift B to ℕ using hB0.le
  lift C to ℕ using hC0.le
  lift D to ℕ using hD0.le
  lift x to ℕ using hx0.le
  lift y to ℕ using hy0.le
  lift z to ℕ using hz0.le
  obtain ⟨G, hG⟩ : ∃ G : ℕ, (G : ℤ) = (D : ℤ) - z := ⟨((D : ℤ) - z).toNat, Int.toNat_of_nonneg hG0.le⟩
  have hzD : (z : ℤ) ≤ D := by linarith
  refine ⟨⟨A, B, C, D, B + x, C + y, G, by exact_mod_cast hA0, by exact_mod_cast hB0,
    by exact_mod_cast hC0, ?_, ?_, ?_, ?_⟩, rfl, ?_, ?_, ?_⟩
  · have : (A : ℤ) ^ 2 + B ^ 2 = ((B : ℤ) + x) ^ 2 := by linear_combination hB
    exact_mod_cast this
  · have : (A : ℤ) ^ 2 + C ^ 2 = ((C : ℤ) + y) ^ 2 := by linear_combination hC
    exact_mod_cast this
  · have : (B : ℤ) ^ 2 + C ^ 2 = (G : ℤ) ^ 2 := by rw [hG]; linear_combination hcub - hD
    exact_mod_cast this
  · exact_mod_cast hcub
  · simp [Cuboid.x]
  · simp [Cuboid.y]
  · simp only [Cuboid.z]; rw [hG]; ring

/-- `x ∣ m (m + κ)` gives `d ∣ A² Q` for every `d ∣ x`. -/
theorem dvd_A_sq_mul_Q {A x y z κ d : ℤ} (hS : S x y z ≠ 0) (hκ2 : κ ^ 2 = R x y z)
    (hA : A ^ 2 * (m x y z - κ) = m x y z * S x y z) (hd : d ∣ m x y z) :
    d ∣ A ^ 2 * Q x y z := by
  rw [A_sq_mul_Q hS hκ2 hA]; exact hd.mul_right _

/-- If `Q = w² + u t` and `d ∣ u` is coprime to `w`, then `d` is coprime to `Q`. -/
theorem isCoprime_of_eq {d u w t q : ℤ} (hd : d ∣ u) (hc : IsCoprime d w)
    (hq : q = w ^ 2 + u * t) : IsCoprime d q := by
  obtain ⟨r, rfl⟩ := hd
  rw [hq, mul_assoc]
  exact hc.pow_right.add_mul_left_right _

/-- `lem:onevar`, strong form for `x`: a divisor of `x` coprime to `yz` divides `A²`. -/
theorem dvd_A_sq_of_coprime_x {A x y z κ d : ℤ} (hS : S x y z ≠ 0) (hκ2 : κ ^ 2 = R x y z)
    (hA : A ^ 2 * (m x y z - κ) = m x y z * S x y z) (hd : d ∣ x) (hc : IsCoprime d (y * z)) :
    d ∣ A ^ 2 := by
  have h1 := dvd_A_sq_mul_Q (d := d) hS hκ2 hA (by unfold m; exact (hd.mul_right y).mul_right z)
  have hQ : IsCoprime d (Q x y z) :=
    isCoprime_of_eq hd hc (t := x * z ^ 2 - x * y ^ 2) (by unfold Q; ring)
  exact hQ.dvd_of_dvd_mul_right h1

/-- `lem:onevar`, strong form for `y`. -/
theorem dvd_A_sq_of_coprime_y {A x y z κ d : ℤ} (hS : S x y z ≠ 0) (hκ2 : κ ^ 2 = R x y z)
    (hA : A ^ 2 * (m x y z - κ) = m x y z * S x y z) (hd : d ∣ y) (hc : IsCoprime d (x * z)) :
    d ∣ A ^ 2 := by
  have h1 := dvd_A_sq_mul_Q (d := d) hS hκ2 hA (by
    unfold m; exact (hd.mul_left x).mul_right z)
  have hQ : IsCoprime d (Q x y z) :=
    isCoprime_of_eq hd hc (t := y * z ^ 2 - x ^ 2 * y) (by unfold Q; ring)
  exact hQ.dvd_of_dvd_mul_right h1

/-- `lem:onevar`, strong form for `z`. -/
theorem dvd_A_sq_of_coprime_z {A x y z κ d : ℤ} (hS : S x y z ≠ 0) (hκ2 : κ ^ 2 = R x y z)
    (hA : A ^ 2 * (m x y z - κ) = m x y z * S x y z) (hd : d ∣ z) (hc : IsCoprime d (x * y)) :
    d ∣ A ^ 2 := by
  have h1 := dvd_A_sq_mul_Q (d := d) hS hκ2 hA (by unfold m; exact hd.mul_left _)
  have hQ : IsCoprime d (-Q x y z) :=
    isCoprime_of_eq hd hc (t := -(x ^ 2 * z) - y ^ 2 * z) (by unfold Q; ring)
  have hQ' : IsCoprime d (Q x y z) := by simpa using hQ.neg_right
  exact hQ'.dvd_of_dvd_mul_right h1

/-- A prime power is coprime to a product of two integers the prime does not divide. -/
theorem isCoprime_prime_pow {p : ℕ} (hp : p.Prime) {a b : ℤ} (e : ℕ) (ha : ¬ (p : ℤ) ∣ a)
    (hb : ¬ (p : ℤ) ∣ b) : IsCoprime ((p : ℤ) ^ e) (a * b) := by
  have hp' := Nat.prime_iff_prime_int.mp hp
  refine IsCoprime.pow_left ((Prime.coprime_iff_not_dvd hp').mpr fun h => ?_)
  rcases hp'.dvd_or_dvd h with h | h
  · exact ha h
  · exact hb h

/-- `lem:onevar`: if a prime `p` divides `x` but not `y` or `z`, and `p^e ∣ x`, then
`p^e ∣ A²`. (The same holds with the roles of `x, y, z` permuted, by `_y` and `_z`.) -/
theorem onevar {A x y z κ : ℤ} {p e : ℕ} (hp : p.Prime) (hS : S x y z ≠ 0)
    (hκ2 : κ ^ 2 = R x y z) (hA : A ^ 2 * (m x y z - κ) = m x y z * S x y z)
    (hx : (p : ℤ) ^ e ∣ x) (hy : ¬ (p : ℤ) ∣ y) (hz : ¬ (p : ℤ) ∣ z) : (p : ℤ) ^ e ∣ A ^ 2 :=
  dvd_A_sq_of_coprime_x hS hκ2 hA hx (isCoprime_prime_pow hp e hy hz)

end PerfectCuboid
