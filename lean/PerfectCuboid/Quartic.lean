import PerfectCuboid.Case1
import PerfectCuboid.Kernels

/-!
# An elementary proof of `thm:quartic` (`QuarticHyp`)

The paper proves `thm:quartic` through the rank of the elliptic curve `V² = U³ - 7U - 6`.
Here it is proved by Fermat's infinite descent, with no elliptic curves.

**Step 1** (`quartic_ordered`): a solution of `3a²b² - a⁴ - b⁴ = c²` with `a > b > 0`
coprime gives a solution of `u⁴ + 3u²v² + v⁴ = w²` with `uv ≠ 0`. Both `a, b` are odd
(otherwise `c² ≡ 3 (mod 4)`), so `(c, a² - b², ab)` is a primitive Pythagorean triple with
`a² - b² = 2L`; writing `L = uv`, `c = ±(u² - v²)` gives
`u⁴ + 3u²v² + v⁴ = c² + 5L² = (L + b²)²`.

**Step 2** (`no_C1`): `x⁴ + 3x²y² + y⁴ = z²` has no solution in coprime positive `x, y`.
Not both are odd (otherwise `z² ≡ 5 (mod 8)`); say `y = 2y'`. Then
`(x² + y², xy, z)` is a primitive triple: `x² + y² = M² - N²`, `xy' = MN`. Splitting
`x = αβ`, `y' = γδ`, `M = αγ`, `N = βδ` turns `M² = N² + x² + y²` into
`α²(γ² - β²) = δ²(β² + 4γ²)`, so `β² + 4γ² = tα²`, `γ² - β² = tδ²` with `t ∣ 5`.
`t = 1` is impossible modulo `8`. For `t = 5`, `α² = β² + (2δ)²`, so `β = m² - n²`, `δ = mn`,
and `γ² = β² + 5δ² = m⁴ + 3m²n² + n⁴`: a solution with `mn = δ < xy`.

`pyth_param` is copied from the magic-squares project (`MagicSquares/FourSquares.lean`).
-/

namespace PerfectCuboid

/-- For odd `D` prime to `L > 0`, a solution of `D² + (2L)² = S²` has the form
`L = mn`, `D = m² - n²` with `gcd(m, n) = 1` and `m, n` of opposite parity. -/
theorem pyth_param {D L S : ℕ} (hD : D % 2 = 1) (hcop : Nat.Coprime D L) (hL : 0 < L)
    (h : D ^ 2 + (2 * L) ^ 2 = S ^ 2) :
    ∃ m n : ℕ, m * n = L ∧ (D : ℤ) = (m : ℤ) ^ 2 - (n : ℤ) ^ 2 ∧ Nat.Coprime m n ∧
      (m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) := by
  have hcop2 : Nat.Coprime D (2 * L) :=
    Nat.Coprime.mul_right ((Nat.coprime_comm.mp
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)))) hcop
  have hS : 0 < S := by
    rcases Nat.eq_zero_or_pos S with h0 | h0
    · subst h0; simp at h; omega
    · exact h0
  have hpt : PythagoreanTriple (D : ℤ) (2 * L) S := by
    unfold PythagoreanTriple
    have : ((D ^ 2 + (2 * L) ^ 2 : ℕ) : ℤ) = ((S ^ 2 : ℕ) : ℤ) := by rw [h]
    push_cast at this
    linear_combination this
  obtain ⟨m, n, hDm, hLm, -, hgcd, hpar, hm0⟩ :=
    PythagoreanTriple.coprime_classification' hpt
      (by have h1 : Int.gcd (D : ℤ) ((2 * L : ℕ) : ℤ) = 1 := by
            rw [Int.gcd_natCast_natCast]; exact hcop2
          simpa using h1)
      (by omega) (by exact_mod_cast hS)
  have hmn : m * n = L := by linarith
  have hLz : (0 : ℤ) < L := by exact_mod_cast hL
  have hmpos : 0 < m := by
    rcases lt_or_eq_of_le hm0 with h | h
    · exact h
    · rw [← h] at hmn; simp at hmn; omega
  have hnpos : 0 < n := by
    by_contra hn
    have := mul_nonpos_of_nonneg_of_nonpos hm0 (not_lt.mp hn)
    linarith
  have em : (m.natAbs : ℤ) = m := Int.natAbs_of_nonneg hm0
  have en : (n.natAbs : ℤ) = n := Int.natAbs_of_nonneg hnpos.le
  refine ⟨m.natAbs, n.natAbs, ?_, ?_, hgcd, ?_⟩
  · have : ((m.natAbs * n.natAbs : ℕ) : ℤ) = L := by rw [Nat.cast_mul, em, en, hmn]
    exact_mod_cast this
  · rw [em, en]; exact hDm
  · omega

/-- A prime dividing two coprime numbers is impossible. -/
theorem not_prime_dvd_both {p a b : ℕ} (hp : p.Prime) (hc : Nat.Coprime a b) (ha : p ∣ a)
    (hb : p ∣ b) : False :=
  (Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp, ha, hb⟩) hc

/-! ## Step 2: `x⁴ + 3x²y² + y⁴ = z²` -/

/-- A nontrivial solution of `x⁴ + 3x²y² + y⁴ = z²`. -/
def C1Sol (x y : ℕ) : Prop :=
  0 < x ∧ 0 < y ∧ Nat.Coprime x y ∧ ∃ z, x ^ 4 + 3 * x ^ 2 * y ^ 2 + y ^ 4 = z ^ 2

theorem C1Sol.symm {x y : ℕ} (h : C1Sol x y) : C1Sol y x := by
  obtain ⟨hx, hy, hc, z, hz⟩ := h
  exact ⟨hy, hx, hc.symm, z, by rw [← hz]; ring⟩

/-- Not both odd: `x⁴ + 3x²y² + y⁴ ≡ 5 (mod 8)` for odd `x, y`. -/
theorem C1_not_both_odd {x y z : ℕ} (hx : x % 2 = 1) (hy : y % 2 = 1) :
    x ^ 4 + 3 * x ^ 2 * y ^ 2 + y ^ 4 ≠ z ^ 2 := by
  obtain ⟨a, rfl⟩ : ∃ a, x = 2 * a + 1 := ⟨x / 2, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, y = 2 * b + 1 := ⟨y / 2, by omega⟩
  intro h
  have h8 := congrArg (Nat.cast : ℕ → ZMod 8) h
  push_cast at h8
  revert h8
  generalize (a : ZMod 8) = u
  generalize (b : ZMod 8) = v
  generalize (z : ZMod 8) = w
  revert u v w
  decide

/-- The case `t = 1` of the descent is impossible: with `α, β` odd, `β² + 4γ² = α²` forces
`γ` even, and then `γ² - β² = δ²` is `≡ -1 (mod 4)`. -/
theorem t_one_impossible {a b g d : ℤ} (ha : Odd a) (hb : Odd b)
    (h1 : b ^ 2 + 4 * g ^ 2 = a ^ 2) (h2 : g ^ 2 - b ^ 2 = d ^ 2) : False := by
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  have e1 := congrArg (Int.cast : ℤ → ZMod 8) h1
  have e2 := congrArg (Int.cast : ℤ → ZMod 8) h2
  push_cast at e1 e2
  revert e1 e2
  generalize (a' : ZMod 8) = u
  generalize (b' : ZMod 8) = v
  generalize (g : ZMod 8) = w
  generalize (d : ZMod 8) = s
  revert u v w s
  decide +kernel

/-- The descent step: a solution with `y` even gives one with smaller `xy`. -/
theorem C1_descent {x y : ℕ} (h : C1Sol x y) (hy2 : y % 2 = 0) :
    ∃ m n, C1Sol m n ∧ m * n < x * y := by
  obtain ⟨hx0, hy0, hcop, z, hz⟩ := h
  obtain ⟨y', rfl⟩ : ∃ y', y = 2 * y' := ⟨y / 2, by omega⟩
  have hy'0 : 0 < y' := by omega
  have hx2 : x % 2 = 1 := by
    by_contra hx
    exact Kernels.two_not_dvd_both hcop ⟨x / 2, by omega⟩ ⟨y', rfl⟩
  -- the primitive triple `(x² + y², xy, z)`
  have hDodd : (x ^ 2 + (2 * y') ^ 2) % 2 = 1 := by
    obtain ⟨a, rfl⟩ : ∃ a, x = 2 * a + 1 := ⟨x / 2, by omega⟩
    ring_nf; omega
  have hpyth : (x ^ 2 + (2 * y') ^ 2) ^ 2 + (2 * (x * y')) ^ 2 = z ^ 2 := by rw [← hz]; ring
  have hcopDL : Nat.Coprime (x ^ 2 + (2 * y') ^ 2) (x * y') := by
    apply Nat.coprime_of_dvd
    intro p hp hD hL
    rcases (Nat.Prime.dvd_mul hp).mp hL with h | h
    · have : p ∣ (2 * y') ^ 2 := (Nat.dvd_add_right (dvd_pow h two_ne_zero)).mp hD
      exact not_prime_dvd_both hp hcop h (hp.dvd_of_dvd_pow this)
    · have h2 : p ∣ 2 * y' := h.mul_left 2
      have : p ∣ x ^ 2 := (Nat.dvd_add_left (dvd_pow h2 two_ne_zero)).mp hD
      exact not_prime_dvd_both hp hcop (hp.dvd_of_dvd_pow this) h2
  obtain ⟨M, N, hMN, hDMN, hcopMN, -⟩ := pyth_param hDodd hcopDL (Nat.mul_pos hx0 hy'0) hpyth
  -- split `x y' = M N`
  obtain ⟨α, β, ⟨γ, rfl⟩, ⟨δ, rfl⟩, rfl⟩ := Nat.dvd_mul.mp (⟨y', hMN⟩ : x ∣ M * N)
  have hpos : 0 < α * β := hx0
  have hα : 0 < α := Nat.pos_of_ne_zero (by rintro rfl; simp at hpos)
  have hβ : 0 < β := Nat.pos_of_ne_zero (by rintro rfl; simp at hpos)
  have hy' : y' = γ * δ := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [← hMN]; ring
  subst hy'
  have hγ : 0 < γ := Nat.pos_of_ne_zero (by rintro rfl; simp at hy'0)
  have hδ : 0 < δ := Nat.pos_of_ne_zero (by rintro rfl; simp at hy'0)
  -- coprimality of the four factors
  have cαδ : Nat.Coprime α δ :=
    Nat.Coprime.coprime_dvd_left (dvd_mul_right α β)
      (Nat.Coprime.coprime_dvd_right ⟨2 * γ, by ring⟩ hcop)
  have cβγ : Nat.Coprime β γ :=
    Nat.Coprime.coprime_dvd_left (dvd_mul_left β α)
      (Nat.Coprime.coprime_dvd_right ⟨2 * δ, by ring⟩ hcop)
  have cβδ : Nat.Coprime β δ :=
    Nat.Coprime.coprime_dvd_left (dvd_mul_left β α)
      (Nat.Coprime.coprime_dvd_right ⟨2 * γ, by ring⟩ hcop)
  -- `α²(γ² - β²) = δ²(β² + 4γ²)`
  have key : (α : ℤ) ^ 2 * ((γ : ℤ) ^ 2 - (β : ℤ) ^ 2) =
      (δ : ℤ) ^ 2 * ((β : ℤ) ^ 2 + 4 * (γ : ℤ) ^ 2) := by
    push_cast at hDMN; linear_combination -hDMN
  have hcαδ : IsCoprime ((α : ℤ) ^ 2) ((δ : ℤ) ^ 2) :=
    (Nat.isCoprime_iff_coprime.mpr cαδ).pow
  obtain ⟨t, ht1⟩ : (α : ℤ) ^ 2 ∣ (β : ℤ) ^ 2 + 4 * (γ : ℤ) ^ 2 :=
    hcαδ.dvd_of_dvd_mul_left ⟨_, key.symm⟩
  have hα2 : (α : ℤ) ^ 2 ≠ 0 := by positivity
  have ht2 : (γ : ℤ) ^ 2 - (β : ℤ) ^ 2 = (δ : ℤ) ^ 2 * t := by
    apply mul_left_cancel₀ hα2
    rw [key, ht1]; ring
  -- `t ∣ 5`, `t > 0`
  have ht5 : t ∣ 5 := by
    obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.mpr cβγ).pow (m := 2) (n := 2)
    exact ⟨u * ((α : ℤ) ^ 2 - 4 * (δ : ℤ) ^ 2) + v * ((α : ℤ) ^ 2 + (δ : ℤ) ^ 2), by
      linear_combination (u + v) * ht1 + (v - 4 * u) * ht2 - 5 * huv⟩
  have htpos : 0 < t := by
    have : 0 < (α : ℤ) ^ 2 * t := by rw [← ht1]; positivity
    exact pos_of_mul_pos_right this (by positivity)
  have ht15 : t = 1 ∨ t = 5 := by
    have := (Nat.dvd_prime Nat.prime_five).mp (Int.natAbs_dvd_natAbs.mpr ht5)
    omega
  rcases ht15 with rfl | rfl
  · exfalso
    have hodd : Odd (α * β) := Nat.odd_iff.mpr hx2
    exact t_one_impossible (g := γ) (d := δ) (Nat.odd_mul.mp hodd).1.natCast
      (Nat.odd_mul.mp hodd).2.natCast
      (by linear_combination ht1) (by linear_combination ht2)
  · -- `α² = β² + (2δ)²`
    have hβodd : β % 2 = 1 := Nat.odd_iff.mp (Nat.odd_mul.mp (Nat.odd_iff.mpr hx2)).2
    have hα' : β ^ 2 + (2 * δ) ^ 2 = α ^ 2 := by
      have : (β : ℤ) ^ 2 + (2 * (δ : ℤ)) ^ 2 = (α : ℤ) ^ 2 := by
        apply mul_left_cancel₀ (show (5 : ℤ) ≠ 0 by norm_num)
        linear_combination ht1 - 4 * ht2
      exact_mod_cast this
    obtain ⟨m, n, hmn, hβmn, hcopmn, -⟩ := pyth_param hβodd cβδ hδ hα'
    have hm : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hmn; omega)
    have hn : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; simp at hmn; omega)
    refine ⟨m, n, ⟨hm, hn, hcopmn, γ, ?_⟩, ?_⟩
    · have : (m : ℤ) ^ 4 + 3 * (m : ℤ) ^ 2 * (n : ℤ) ^ 2 + (n : ℤ) ^ 4 = (γ : ℤ) ^ 2 := by
        have hδmn : (δ : ℤ) = m * n := by exact_mod_cast hmn.symm
        linear_combination -ht2 - ((β : ℤ) + ((m : ℤ) ^ 2 - (n : ℤ) ^ 2)) * hβmn
          - 5 * ((δ : ℤ) + m * n) * hδmn
      exact_mod_cast this
    · rw [hmn]
      have : 1 ≤ α * β * (2 * γ) := Nat.one_le_iff_ne_zero.mpr (by positivity)
      calc δ = 1 * δ := (one_mul δ).symm
        _ < 2 * (α * β * γ) * δ := by
          apply Nat.mul_lt_mul_of_pos_right _ hδ
          have : 1 ≤ α * β * γ := Nat.one_le_iff_ne_zero.mpr (by positivity)
          omega
        _ = α * β * (2 * (γ * δ)) := by ring

/-- Step 2: `x⁴ + 3x²y² + y⁴ = z²` has no solution in coprime positive integers. -/
theorem no_C1 : ∀ n x y, x * y = n → ¬ C1Sol x y := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x y hn hs
    obtain ⟨m, k, h1, h2⟩ : ∃ m k, C1Sol m k ∧ m * k < x * y := by
      rcases Nat.mod_two_eq_zero_or_one y with hy | hy
      · exact C1_descent hs hy
      · rcases Nat.mod_two_eq_zero_or_one x with hx | hx
        · obtain ⟨m, k, h1, h2⟩ := C1_descent hs.symm hx
          exact ⟨m, k, h1, by rw [mul_comm x]; exact h2⟩
        · exfalso
          obtain ⟨-, -, -, z, hz⟩ := hs
          exact C1_not_both_odd hx hy hz
    exact ih (m * k) (hn ▸ h2) m k rfl h1

/-! ## Step 1: from the quartic to `x⁴ + 3x²y² + y⁴ = z²` -/

/-- One even, one odd is impossible: `3a²b² - a⁴ - b⁴ ≡ 3 (mod 4)`. -/
theorem quartic_mod4 {a b c : ℤ} (ha : Even a) (hb : Odd b)
    (h : 3 * a ^ 2 * b ^ 2 - a ^ 4 - b ^ 4 = c ^ 2) : False := by
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  have e := congrArg (Int.cast : ℤ → ZMod 4) h
  push_cast at e
  revert e
  generalize (a' : ZMod 4) = u
  generalize (b' : ZMod 4) = v
  generalize (c : ZMod 4) = w
  revert u v w
  decide

/-- Step 1, for coprime `a > b`. -/
theorem quartic_ordered {a b : ℕ} {c : ℤ} (hab : b < a) (hc : Nat.Coprime a b)
    (h : 3 * (a : ℤ) ^ 2 * (b : ℤ) ^ 2 - (a : ℤ) ^ 4 - (b : ℤ) ^ 4 = c ^ 2) : False := by
  -- both odd
  have ha2 : a % 2 = 1 := by
    by_contra ha
    rcases Nat.mod_two_eq_zero_or_one b with hb2 | hb2
    · exact Kernels.two_not_dvd_both hc ⟨a / 2, by omega⟩ ⟨b / 2, by omega⟩
    · exact quartic_mod4 (a := a) (b := b) (c := c) ⟨(a / 2 : ℕ), by push_cast; omega⟩
        (Nat.odd_iff.mpr hb2).natCast h
  have hb2 : b % 2 = 1 := by
    by_contra hb'
    exact quartic_mod4 (a := b) (b := a) (c := c) ⟨(b / 2 : ℕ), by push_cast; omega⟩
      (Nat.odd_iff.mpr ha2).natCast (by linear_combination h)
  -- `a² - b² = 2L`
  obtain ⟨L, hL⟩ : ∃ L, a ^ 2 = b ^ 2 + 2 * L := by
    have ha2' : a ^ 2 % 2 = 1 := by rw [Nat.pow_mod, ha2]
    have hb2' : b ^ 2 % 2 = 1 := by rw [Nat.pow_mod, hb2]
    have hle := Nat.pow_le_pow_left hab.le 2
    exact ⟨(a ^ 2 - b ^ 2) / 2, by omega⟩
  have hLpos : 0 < L := by
    have := Nat.pow_lt_pow_left hab (two_ne_zero); omega
  have hL' : (a : ℤ) ^ 2 = (b : ℤ) ^ 2 + 2 * (L : ℤ) := by exact_mod_cast hL
  -- `c² + (2L)² = (ab)²`
  have hcL : c ^ 2 + (2 * (L : ℤ)) ^ 2 = ((a : ℤ) * b) ^ 2 := by
    linear_combination -h - (2 * (L : ℤ) + (a : ℤ) ^ 2 - (b : ℤ) ^ 2) * hL'
  set D := c.natAbs
  have hDc : (D : ℤ) ^ 2 = c ^ 2 := Int.natAbs_sq c
  have hpyth : D ^ 2 + (2 * L) ^ 2 = (a * b) ^ 2 := by
    have : (D : ℤ) ^ 2 + (2 * (L : ℤ)) ^ 2 = ((a : ℤ) * b) ^ 2 := by rw [hDc]; exact hcL
    exact_mod_cast this
  have hDodd : D % 2 = 1 := by
    by_contra hD
    have hab_odd : Odd ((a * b) ^ 2) :=
      (Nat.odd_mul.mpr ⟨Nat.odd_iff.mpr ha2, Nat.odd_iff.mpr hb2⟩).pow
    have hDe : Even D := Nat.even_iff.mpr (by omega)
    have : Even (D ^ 2 + (2 * L) ^ 2) :=
      (Nat.even_pow.mpr ⟨hDe, two_ne_zero⟩).add (Nat.even_pow.mpr ⟨even_two_mul L, two_ne_zero⟩)
    rw [hpyth] at this
    exact (Nat.not_even_iff_odd.mpr hab_odd) this
  have hcopDL : Nat.Coprime D L := by
    apply Nat.coprime_of_dvd
    intro p hp hpD hpL
    -- `p ∣ (ab)²`, so `p ∣ a` or `p ∣ b`, and `p ∣ 2L = a² - b²`
    have hab2 : p ∣ (a * b) ^ 2 := hpyth ▸ dvd_add (dvd_pow hpD two_ne_zero)
      (dvd_pow (hpL.mul_left 2) two_ne_zero)
    have h2L : p ∣ 2 * L := hpL.mul_left 2
    rcases (Nat.Prime.dvd_mul hp).mp (hp.dvd_of_dvd_pow hab2) with h | h
    · have : p ∣ b ^ 2 := (Nat.dvd_add_left h2L).mp (hL ▸ dvd_pow h two_ne_zero)
      exact not_prime_dvd_both hp hc h (hp.dvd_of_dvd_pow this)
    · have : p ∣ a ^ 2 := hL ▸ dvd_add (dvd_pow h two_ne_zero) h2L
      exact not_prime_dvd_both hp hc (hp.dvd_of_dvd_pow this) h
  obtain ⟨m, n, hmn, hDmn, hcopmn, -⟩ := pyth_param hDodd hcopDL hLpos hpyth
  have hm : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hmn; omega)
  have hn : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; simp at hmn; omega)
  -- `m⁴ + 3m²n² + n⁴ = c² + 5L² = (L + b²)²`
  refine no_C1 _ m n rfl ⟨hm, hn, hcopmn, L + b ^ 2, ?_⟩
  have hLmn : (L : ℤ) = m * n := by exact_mod_cast hmn.symm
  have : (m : ℤ) ^ 4 + 3 * (m : ℤ) ^ 2 * (n : ℤ) ^ 2 + (n : ℤ) ^ 4 = ((L : ℤ) + (b : ℤ) ^ 2) ^ 2 := by
    linear_combination (-((D : ℤ) + ((m : ℤ) ^ 2 - (n : ℤ) ^ 2))) * hDmn
      - 5 * ((L : ℤ) + m * n) * hLmn + hDc - h
      + (2 * (b : ℤ) ^ 2 - (a : ℤ) ^ 2 - 2 * (L : ℤ)) * hL'
  exact_mod_cast this

/-- `thm:quartic`, proved: `QuarticHyp` holds. -/
theorem quarticHyp : QuarticHyp := by
  intro p q c h
  by_contra hpq
  set P := p.natAbs
  set Q := q.natAbs
  have eP : (P : ℤ) ^ 2 = p ^ 2 := Int.natAbs_sq p
  have eQ : (Q : ℤ) ^ 2 = q ^ 2 := Int.natAbs_sq q
  have hP4 : (P : ℤ) ^ 4 = p ^ 4 := by
    rw [show (P : ℤ) ^ 4 = ((P : ℤ) ^ 2) ^ 2 by ring, eP]; ring
  have hQ4 : (Q : ℤ) ^ 4 = q ^ 4 := by
    rw [show (Q : ℤ) ^ 4 = ((Q : ℤ) ^ 2) ^ 2 by ring, eQ]; ring
  have h' : 3 * (P : ℤ) ^ 2 * (Q : ℤ) ^ 2 - (P : ℤ) ^ 4 - (Q : ℤ) ^ 4 = c ^ 2 := by
    rw [hP4, hQ4, eP, eQ]; exact h
  have hPQ : P ≠ Q := fun hPQ => hpq (by rw [← eP, ← eQ, hPQ])
  -- neither is zero
  have hP0 : P ≠ 0 := by
    intro h0; rw [h0] at h'
    have : (Q : ℤ) ^ 4 + c ^ 2 = 0 := by linear_combination -h'
    have hQ : (Q : ℤ) ^ 4 = 0 := by nlinarith [sq_nonneg c, pow_nonneg (Nat.cast_nonneg Q : (0:ℤ) ≤ Q) 4]
    exact hPQ (by rw [h0]; exact_mod_cast (pow_eq_zero_iff (by norm_num)).mp hQ |>.symm)
  have hQ0 : Q ≠ 0 := by
    intro h0; rw [h0] at h'
    have : (P : ℤ) ^ 4 + c ^ 2 = 0 := by linear_combination -h'
    have hP : (P : ℤ) ^ 4 = 0 := by nlinarith [sq_nonneg c, pow_nonneg (Nat.cast_nonneg P : (0:ℤ) ≤ P) 4]
    exact hPQ (by rw [h0]; exact_mod_cast (pow_eq_zero_iff (by norm_num)).mp hP)
  -- divide by the gcd
  obtain ⟨P', Q', hco, hP', hQ'⟩ := Nat.exists_coprime P Q
  set g := Nat.gcd P Q
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hP0)
  have hg4 : ((g : ℤ) ^ 2) ^ 2 ∣ c ^ 2 :=
    ⟨3 * (P' : ℤ) ^ 2 * (Q' : ℤ) ^ 2 - (P' : ℤ) ^ 4 - (Q' : ℤ) ^ 4, by
      rw [← h', hP', hQ']; push_cast; ring⟩
  obtain ⟨c', hc'⟩ := (Int.pow_dvd_pow_iff two_ne_zero).mp hg4
  have h'' : 3 * (P' : ℤ) ^ 2 * (Q' : ℤ) ^ 2 - (P' : ℤ) ^ 4 - (Q' : ℤ) ^ 4 = c' ^ 2 := by
    have hg0 : ((g : ℤ) ^ 2) ^ 2 ≠ 0 := by positivity
    apply mul_left_cancel₀ hg0
    have eP' : (P : ℤ) = P' * g := by exact_mod_cast hP'
    have eQ' : (Q : ℤ) = Q' * g := by exact_mod_cast hQ'
    have := h'
    rw [eP', eQ', hc'] at this
    linear_combination this
  have hP'0 : 0 < P' := Nat.pos_of_ne_zero (by rintro rfl; simp at hP'; exact hP0 hP')
  have hQ'0 : 0 < Q' := Nat.pos_of_ne_zero (by rintro rfl; simp at hQ'; exact hQ0 hQ')
  have hne : P' ≠ Q' := fun h => hPQ (by rw [hP', hQ', h])
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact quartic_ordered (c := c') hlt hco.symm (by linear_combination h'')
  · exact quartic_ordered hlt hco h''

/-- `thm:case1`, now unconditional: no perfect cuboid in normal form has `y² = xz`. -/
theorem Cuboid.not_case1' (c : Cuboid) (hA : Odd c.A) (hBC : c.B < c.C) :
    c.y ^ 2 ≠ c.x * c.z :=
  c.not_case1 quarticHyp hA hBC

/-- A perfect cuboid exists iff one exists in normal form with `y² ≠ xz`. -/
theorem exists_iff_case2' :
    FormalConjecturesStatement ↔
      ∃ c : Cuboid, c.IsPrimitive ∧ Odd c.A ∧ c.B < c.C ∧ c.y ^ 2 ≠ c.x * c.z :=
  exists_iff_case2 quarticHyp

end PerfectCuboid
