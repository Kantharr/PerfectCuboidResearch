import PerfectCuboid.ConverseFull

/-!
# Section 4: necessary conditions on the radicand

Here `x > y > z > 0` are natural numbers and the three factors of `R` are
`F₁ = x² + y²`, `F₂ = x² - z²`, `F₃ = y² - z²` (`R_eq_cast` relates their product to `R`).

* `kernel_decomp`: if a product of three positive integers is a square, they are
  `αβu₁²`, `αγu₂²`, `βγu₃²` with `α, β, γ` squarefree and pairwise coprime. Proof:
  `F₁ = s₁² d₁`, `F₂ = s₂² d₂` with `d₁, d₂` squarefree; `α = gcd(d₁, d₂)`, `β = d₁/α`,
  `γ = d₂/α`; then `βγF₃` is a square and `βγ` is squarefree, so `βγ ∣ √(βγF₃)`.
* `Kernels`: a decomposition `eq:kernels` for `(x, y, z)`; `exists_kernels` and
  `Kernels.sq_eq` are `thm:kernels` (both directions).
* `Kernels.coprime_xyz`, `dvd_y_sq_add_z_sq` etc., `mod_four`, `two_adic`:
  `thm:kernels` (i)-(iv). Part (iii) is stated for odd primes dividing `α` or `β`.
* `not_isSquare_F₁`, `not_all_squares`: `cor:altitude`.
* `Kernels.char_gamma`, `char_alpha`, `char_beta`: `prop:characters`, as
  `χ(αβ) = χ(2)` etc. for the quadratic character `χ` of `ZMod p` (`legendreSym p a` is by
  definition `χ(a)`). In each case the congruences collapse to `αβu₁² ≡ 2z²`,
  `βγu₃² ≡ 2y²` or `αγu₂² ≡ 2x² (mod p)`, so the paper's use of `p ≡ 1 (mod 4)` (to make
  `-1` a square) is not needed.
-/

namespace PerfectCuboid

open Nat

/-- If `a² b = c²` with `a ≠ 0` then `b` is a square. -/
theorem exists_sq_of_sq_mul_eq_sq {a b c : ℕ} (ha : a ≠ 0) (h : a ^ 2 * b = c ^ 2) :
    ∃ t, b = t ^ 2 := by
  obtain ⟨t, rfl⟩ : a ∣ c := (Nat.pow_dvd_pow_iff two_ne_zero).mp ⟨b, h.symm⟩
  refine ⟨t, Nat.eq_of_mul_eq_mul_left (pow_pos (Nat.pos_of_ne_zero ha) 2) ?_⟩
  rw [h, mul_pow]

/-- Kernel decomposition of three positive integers whose product is a square. -/
theorem kernel_decomp {F₁ F₂ F₃ : ℕ} (h₁ : 0 < F₁) (h₂ : 0 < F₂)
    (hsq : IsSquare (F₁ * F₂ * F₃)) :
    ∃ α β γ u₁ u₂ u₃ : ℕ, Squarefree α ∧ Squarefree β ∧ Squarefree γ ∧
      α.Coprime β ∧ α.Coprime γ ∧ β.Coprime γ ∧
      F₁ = α * β * u₁ ^ 2 ∧ F₂ = α * γ * u₂ ^ 2 ∧ F₃ = β * γ * u₃ ^ 2 := by
  obtain ⟨s₁, d₁, hF₁, hd₁⟩ := exists_sq_mul_squarefree F₁
  obtain ⟨s₂, d₂, hF₂, hd₂⟩ := exists_sq_mul_squarefree F₂
  have hd₁0 : d₁ ≠ 0 := by rintro rfl; simp at hF₁; omega
  have hd₂0 : d₂ ≠ 0 := by rintro rfl; simp at hF₂; omega
  have hs₁ : s₁ ≠ 0 := by rintro rfl; simp at hF₁; omega
  have hs₂ : s₂ ≠ 0 := by rintro rfl; simp at hF₂; omega
  set α := Nat.gcd d₁ d₂ with hα
  have hα0 : 0 < α := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hd₁0)
  set β := d₁ / α
  set γ := d₂ / α
  have e₁ : d₁ = α * β := (Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)).symm
  have e₂ : d₂ = α * γ := (Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)).symm
  have hβγ : β.Coprime γ := Nat.coprime_div_gcd_div_gcd hα0
  rw [e₁] at hd₁
  rw [e₂] at hd₂
  obtain ⟨hαβ, hsα, hsβ⟩ := Nat.squarefree_mul_iff.mp hd₁
  obtain ⟨hαγ, -, hsγ⟩ := Nat.squarefree_mul_iff.mp hd₂
  have hsq' : Squarefree (β * γ) := Nat.squarefree_mul_iff.mpr ⟨hβγ, hsβ, hsγ⟩
  -- `βγ F₃` is a square
  obtain ⟨c, hc⟩ := hsq
  obtain ⟨t, ht⟩ : ∃ t, β * γ * F₃ = t ^ 2 := by
    refine exists_sq_of_sq_mul_eq_sq (a := s₁ * s₂ * α) (c := c)
      (mul_ne_zero (mul_ne_zero hs₁ hs₂) hα0.ne') ?_
    rw [← sq] at hc; rw [← hc, ← hF₁, ← hF₂, e₁, e₂]; ring
  obtain ⟨w, rfl⟩ : β * γ ∣ t := (hsq'.dvd_pow_iff_dvd two_ne_zero).mp ⟨F₃, ht.symm⟩
  have hβγ0 : β * γ ≠ 0 :=
    mul_ne_zero (fun h => hd₁0 (by rw [e₁, h, mul_zero])) (fun h => hd₂0 (by rw [e₂, h, mul_zero]))
  refine ⟨α, β, γ, s₁, s₂, w, hsα, hsβ, hsγ, hαβ, hαγ, hβγ, ?_, ?_, ?_⟩
  · rw [← hF₁, e₁]; ring
  · rw [← hF₂, e₂]; ring
  · apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hβγ0)
    rw [ht]; ring

/-- A decomposition `eq:kernels` of the three factors of `R`. -/
structure Kernels (x y z : ℕ) where
  α : ℕ
  β : ℕ
  γ : ℕ
  u₁ : ℕ
  u₂ : ℕ
  u₃ : ℕ
  sf_α : Squarefree α
  sf_β : Squarefree β
  sf_γ : Squarefree γ
  cop_αβ : α.Coprime β
  cop_αγ : α.Coprime γ
  cop_βγ : β.Coprime γ
  h₁ : x ^ 2 + y ^ 2 = α * β * u₁ ^ 2
  h₂ : x ^ 2 - z ^ 2 = α * γ * u₂ ^ 2
  h₃ : y ^ 2 - z ^ 2 = β * γ * u₃ ^ 2

/-- `R` as a product of natural numbers. -/
theorem R_eq_cast {x y z : ℕ} (hzy : z < y) (hyx : y < x) :
    R (x : ℤ) y z = (((x ^ 2 + y ^ 2) * (x ^ 2 - z ^ 2) * (y ^ 2 - z ^ 2) : ℕ) : ℤ) := by
  have h1 : z ^ 2 ≤ x ^ 2 := Nat.pow_le_pow_left (hzy.trans hyx).le 2
  have h2 : z ^ 2 ≤ y ^ 2 := Nat.pow_le_pow_left hzy.le 2
  unfold R; push_cast [Nat.cast_sub h1, Nat.cast_sub h2]; ring

/-- `thm:kernels`: if `R` is a square, a kernel decomposition exists. -/
theorem exists_kernels {x y z : ℕ} (hz : 0 < z) (hzy : z < y) (hyx : y < x)
    (hR : IsSquare ((x ^ 2 + y ^ 2) * (x ^ 2 - z ^ 2) * (y ^ 2 - z ^ 2))) :
    Nonempty (Kernels x y z) := by
  have p1 : 0 < x ^ 2 + y ^ 2 := Nat.add_pos_left (pow_pos (by omega) 2) _
  have p2 : 0 < x ^ 2 - z ^ 2 := Nat.sub_pos_of_lt (Nat.pow_lt_pow_left (hzy.trans hyx) two_ne_zero)
  obtain ⟨α, β, γ, u₁, u₂, u₃, a, b, c, d, e, f, g, h, i⟩ := kernel_decomp p1 p2 hR
  exact ⟨⟨α, β, γ, u₁, u₂, u₃, a, b, c, d, e, f, g, h, i⟩⟩

namespace Kernels

variable {x y z : ℕ} (k : Kernels x y z)

/-- `thm:kernels`: `√R = αβγ u₁u₂u₃`, and conversely any such decomposition makes `R` a
square. -/
theorem sq_eq : (x ^ 2 + y ^ 2) * (x ^ 2 - z ^ 2) * (y ^ 2 - z ^ 2) =
    (k.α * k.β * k.γ * k.u₁ * k.u₂ * k.u₃) ^ 2 := by
  rw [k.h₁, k.h₂, k.h₃]; ring

/-- `thm:kernels` (ii). -/
theorem dvd_y_sq_add_z_sq (hzx : z < x) : k.α ∣ y ^ 2 + z ^ 2 := by
  have e : y ^ 2 + z ^ 2 = (x ^ 2 + y ^ 2) - (x ^ 2 - z ^ 2) := by
    have := Nat.pow_le_pow_left hzx.le 2; omega
  rw [e, k.h₁, k.h₂]
  exact Nat.dvd_sub ((dvd_mul_right _ _).mul_right _) ((dvd_mul_right _ _).mul_right _)

theorem dvd_x_sq_add_z_sq (hzy : z < y) : k.β ∣ x ^ 2 + z ^ 2 := by
  have e : x ^ 2 + z ^ 2 = (x ^ 2 + y ^ 2) - (y ^ 2 - z ^ 2) := by
    have := Nat.pow_le_pow_left hzy.le 2; omega
  rw [e, k.h₁, k.h₃]
  exact Nat.dvd_sub ((dvd_mul_left _ _).mul_right _) ((dvd_mul_right _ _).mul_right _)

theorem dvd_x_sq_sub_y_sq (hzy : z < y) (hyx : y < x) : k.γ ∣ x ^ 2 - y ^ 2 := by
  have e : x ^ 2 - y ^ 2 = (x ^ 2 - z ^ 2) - (y ^ 2 - z ^ 2) := by
    have := Nat.pow_le_pow_left hzy.le 2; have := Nat.pow_le_pow_left hyx.le 2; omega
  rw [e, k.h₂, k.h₃]
  exact Nat.dvd_sub ((dvd_mul_left _ _).mul_right _) ((dvd_mul_left _ _).mul_right _)

end Kernels

/-! ## Linking the divisibility of `x, y, z` by a prime through the factors -/

theorem dvd_iff_of_dvd_add_sq {p a b : ℕ} (hp : p.Prime) (h : p ∣ a ^ 2 + b ^ 2) :
    p ∣ a ↔ p ∣ b := by
  constructor
  · intro ha
    exact hp.dvd_of_dvd_pow ((Nat.dvd_add_right (dvd_pow ha two_ne_zero)).mp h)
  · intro hb
    exact hp.dvd_of_dvd_pow ((Nat.dvd_add_left (dvd_pow hb two_ne_zero)).mp h)

theorem dvd_iff_of_dvd_sub_sq {p a b : ℕ} (hp : p.Prime) (hle : b ≤ a)
    (h : p ∣ a ^ 2 - b ^ 2) : p ∣ a ↔ p ∣ b := by
  have e : a ^ 2 = (a ^ 2 - b ^ 2) + b ^ 2 := by
    have := Nat.pow_le_pow_left hle 2; omega
  constructor
  · intro ha
    have : p ∣ (a ^ 2 - b ^ 2) + b ^ 2 := by rw [← e]; exact dvd_pow ha two_ne_zero
    exact hp.dvd_of_dvd_pow ((Nat.dvd_add_right h).mp this)
  · intro hb
    have : p ∣ a ^ 2 := by rw [e]; exact dvd_add h (dvd_pow hb two_ne_zero)
    exact hp.dvd_of_dvd_pow this

namespace Kernels

variable {x y z : ℕ} (k : Kernels x y z)

/-- If `p` divides `α`, `β` or `γ` then `p` divides one of `x, y, z` iff it divides all
three. -/
theorem link {p : ℕ} (hp : p.Prime) (hzy : z < y) (hyx : y < x)
    (h : p ∣ k.α ∨ p ∣ k.β ∨ p ∣ k.γ) :
    (p ∣ x ↔ p ∣ y) ∧ (p ∣ x ↔ p ∣ z) := by
  have hzx := hzy.trans hyx
  have d1 : ∀ {d}, d ∣ k.α ∨ d ∣ k.β → d ∣ x ^ 2 + y ^ 2 := fun h => by
    rw [k.h₁]; rcases h with h | h
    · exact (h.mul_right _).mul_right _
    · exact (h.mul_left _).mul_right _
  have d2 : ∀ {d}, d ∣ k.α ∨ d ∣ k.γ → d ∣ x ^ 2 - z ^ 2 := fun h => by
    rw [k.h₂]; rcases h with h | h
    · exact (h.mul_right _).mul_right _
    · exact (h.mul_left _).mul_right _
  have d3 : ∀ {d}, d ∣ k.β ∨ d ∣ k.γ → d ∣ y ^ 2 - z ^ 2 := fun h => by
    rw [k.h₃]; rcases h with h | h
    · exact (h.mul_right _).mul_right _
    · exact (h.mul_left _).mul_right _
  rcases h with h | h | h
  · exact ⟨dvd_iff_of_dvd_add_sq hp (d1 (Or.inl h)),
      dvd_iff_of_dvd_sub_sq hp hzx.le (d2 (Or.inl h))⟩
  · have hxy := dvd_iff_of_dvd_add_sq hp (d1 (Or.inr h))
    exact ⟨hxy, hxy.trans (dvd_iff_of_dvd_sub_sq hp hzy.le (d3 (Or.inl h)))⟩
  · have hxz := dvd_iff_of_dvd_sub_sq hp hzx.le (d2 (Or.inr h))
    exact ⟨hxz.trans (dvd_iff_of_dvd_sub_sq hp hzy.le (d3 (Or.inr h))).symm, hxz⟩

/-- `thm:kernels` (i): `gcd(αβγ, xyz) = 1` when no prime divides all of `x, y, z`. -/
theorem coprime_xyz (hzy : z < y) (hyx : y < x)
    (hcop : ∀ p : ℕ, p.Prime → ¬ (p ∣ x ∧ p ∣ y ∧ p ∣ z)) :
    (k.α * k.β * k.γ).Coprime (x * y * z) := by
  apply Nat.coprime_of_dvd
  intro p hp hd hxyz
  have hd' : p ∣ k.α ∨ p ∣ k.β ∨ p ∣ k.γ := by
    rcases (Nat.Prime.dvd_mul hp).mp hd with h | h
    · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  obtain ⟨hxy, hxz⟩ := k.link hp hzy hyx hd'
  apply hcop p hp
  rcases (Nat.Prime.dvd_mul hp).mp hxyz with h | h
  · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · exact ⟨h, hxy.mp h, hxz.mp h⟩
    · exact ⟨hxy.mpr h, h, hxz.mp (hxy.mpr h)⟩
  · exact ⟨hxz.mpr h, hxy.mp (hxz.mpr h), h⟩

/-- `thm:kernels` (iii): every odd prime dividing `αβ` is `≡ 1 (mod 4)`. -/
theorem mod_four (hzy : z < y) (hyx : y < x)
    (hcop : ∀ p : ℕ, p.Prime → ¬ (p ∣ x ∧ p ∣ y ∧ p ∣ z)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : p ∣ k.α * k.β) : p % 4 = 1 := by
  have hab : p ∣ k.α ∨ p ∣ k.β := (Nat.Prime.dvd_mul hp).mp h
  obtain ⟨hxy, hxz⟩ := k.link hp hzy hyx (hab.elim Or.inl (Or.inr ∘ Or.inl))
  have hx : ¬ p ∣ x := fun hx => hcop p hp ⟨hx, hxy.mp hx, hxz.mp hx⟩
  have hF : p ∣ x ^ 2 + y ^ 2 := by
    rw [k.h₁]; rcases hab with h | h
    · exact (h.mul_right _).mul_right _
    · exact (h.mul_left _).mul_right _
  have := Fact.mk hp
  have hF' : ((x : ZMod p)) ^ 2 + (y : ZMod p) ^ 2 = 0 := by
    have := (ZMod.natCast_eq_zero_iff (x ^ 2 + y ^ 2) p).mpr hF
    push_cast at this; exact this
  have hx0 : (x : ZMod p) ≠ 0 := fun h0 => hx ((ZMod.natCast_eq_zero_iff x p).mp h0)
  have h3 : p % 4 ≠ 3 :=
    ZMod.mod_four_ne_three_of_sq_eq_neg_sq' (x := (y : ZMod p)) hx0 (by linear_combination hF')
  have : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
  omega

omit k in
theorem two_not_dvd_both {a b : ℕ} (hc : a.Coprime b) (ha : 2 ∣ a) (hb : 2 ∣ b) : False := by
  have := Nat.dvd_gcd ha hb
  rw [hc.gcd_eq_one] at this
  omega

/-- `thm:kernels` (iv): for odd `x, y`, `γ` is odd and exactly one of `α, β` is even. -/
theorem two_adic (hx : Odd x) (hy : Odd y) :
    Odd k.γ ∧ ((Even k.α ∧ Odd k.β) ∨ (Odd k.α ∧ Even k.β)) := by
  -- `x² + y² ≡ 2 (mod 4)`
  have h4 : (x ^ 2 + y ^ 2) % 4 = 2 := by
    obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy; ring_nf; omega
  have heven : Even (k.α * k.β) := by
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    rcases Nat.even_or_odd k.u₁ with ⟨u, hu⟩ | hu
    · have : 4 ∣ x ^ 2 + y ^ 2 := by rw [k.h₁, hu]; exact ⟨k.α * k.β * u ^ 2, by ring⟩
      omega
    · have : Odd (x ^ 2 + y ^ 2) := by rw [k.h₁]; exact hodd.mul hu.pow
      obtain ⟨c, hc⟩ := this; omega
  have hnot : ¬ (Even k.α ∧ Even k.β) := by
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact two_not_dvd_both k.cop_αβ ⟨a, by omega⟩ ⟨b, by omega⟩
  refine ⟨?_, ?_⟩
  · by_contra hγ
    rw [Nat.not_odd_iff_even] at hγ
    rcases Nat.even_mul.mp heven with ha | hb
    · obtain ⟨a, ha⟩ := ha; obtain ⟨c, hc⟩ := hγ
      exact two_not_dvd_both k.cop_αγ ⟨a, by omega⟩ ⟨c, by omega⟩
    · obtain ⟨b, hb⟩ := hb; obtain ⟨c, hc⟩ := hγ
      exact two_not_dvd_both k.cop_βγ ⟨b, by omega⟩ ⟨c, by omega⟩
  · rcases Nat.even_mul.mp heven with ha | hb
    · exact Or.inl ⟨ha, Nat.not_even_iff_odd.mp fun hb => hnot ⟨ha, hb⟩⟩
    · exact Or.inr ⟨Nat.not_even_iff_odd.mp fun ha => hnot ⟨ha, hb⟩, hb⟩

end Kernels

/-- `cor:altitude`: for odd `x, y`, `x² + y²` is not a square, so the three factors of `R`
are never all squares. -/
theorem not_isSquare_F₁ {x y : ℕ} (hx : Odd x) (hy : Odd y) : ¬ IsSquare (x ^ 2 + y ^ 2) := by
  rintro ⟨c, hc⟩
  exact odd_sq_add_odd_sq_ne_sq hx hy (by rw [hc, sq])

theorem not_all_squares {x y z : ℕ} (hx : Odd x) (hy : Odd y) :
    ¬ (IsSquare (x ^ 2 + y ^ 2) ∧ IsSquare (x ^ 2 - z ^ 2) ∧ IsSquare (y ^ 2 - z ^ 2)) :=
  fun h => not_isSquare_F₁ hx hy h.1

/-- Every cuboid in normal form has a kernel decomposition for its triple (`thm:kernels`
applied to `Cuboid.necessary`). -/
theorem Cuboid.exists_kernels (c : Cuboid) (hA : Odd c.A) (hBC : c.B < c.C) :
    Nonempty (Kernels c.x.toNat c.y.toNat c.z.toNat) := by
  obtain ⟨-, -, -, hyx, hzy, hz, -, κ, hκ2, hκ, -, -⟩ := c.necessary hA hBC
  have hx := c.x_pos
  have hy := c.y_pos
  have eX : ((c.x.toNat : ℕ) : ℤ) = c.x := Int.toNat_of_nonneg hx.le
  have eY : ((c.y.toNat : ℕ) : ℤ) = c.y := Int.toNat_of_nonneg hy.le
  have eZ : ((c.z.toNat : ℕ) : ℤ) = c.z := Int.toNat_of_nonneg hz.le
  have hzy' : c.z.toNat < c.y.toNat := by omega
  have hyx' : c.y.toNat < c.x.toNat := by omega
  apply PerfectCuboid.exists_kernels (by omega) hzy' hyx'
  refine ⟨κ.toNat, ?_⟩
  have h := R_eq_cast hzy' hyx'
  rw [eX, eY, eZ, ← hκ2, ← Int.toNat_of_nonneg hκ.le] at h
  rw [← sq]
  exact_mod_cast h.symm

/-- `rem:altitude`: at `(x, y, z) = (33, 9, 7)` the factors are `1170`, `1040`, `32`, none a
square, with product `6240²`. -/
theorem altitude_example :
    (33 ^ 2 + 9 ^ 2 = 1170 ∧ 33 ^ 2 - 7 ^ 2 = 1040 ∧ 9 ^ 2 - 7 ^ 2 = 32) ∧
    ¬ IsSquare (1170 : ℕ) ∧ ¬ IsSquare (1040 : ℕ) ∧ ¬ IsSquare (32 : ℕ) ∧
    1170 * 1040 * 32 = (6240 : ℕ) ^ 2 := by
  norm_num

/-! ## `prop:characters` -/

section characters

variable {p : ℕ} [Fact p.Prime]

/-- If `a u² = 2 t²` in `ZMod p` with `u, t ≠ 0`, then `χ(a) = χ(2)`. -/
theorem char_eq_two {a u t : ZMod p} (hu : u ≠ 0) (ht : t ≠ 0) (h : a * u ^ 2 = 2 * t ^ 2) :
    quadraticChar (ZMod p) a = quadraticChar (ZMod p) 2 := by
  have ha : a = 2 * (t / u) ^ 2 := by
    field_simp; linear_combination h
  rw [ha, map_mul, quadraticChar_sq_one' (div_ne_zero ht hu), mul_one]

theorem two_ne_zero_zmod (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at this
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp this)

theorem natCast_ne_zero_of_not_dvd {n : ℕ} (h : ¬ p ∣ n) : (n : ZMod p) ≠ 0 :=
  fun h0 => h ((ZMod.natCast_eq_zero_iff n p).mp h0)

/-- Cast `d ∣ a² - b²` (with `b ≤ a`) to `a² = b²` in `ZMod p`. -/
theorem sq_eq_of_dvd_sub {a b : ℕ} (hle : b ≤ a) (h : p ∣ a ^ 2 - b ^ 2) :
    (a : ZMod p) ^ 2 = (b : ZMod p) ^ 2 := by
  have := (ZMod.natCast_eq_zero_iff _ p).mpr h
  rw [Nat.cast_sub (Nat.pow_le_pow_left hle 2)] at this
  push_cast at this
  linear_combination this

theorem sq_add_of_dvd {a b : ℕ} (h : p ∣ a ^ 2 + b ^ 2) :
    (a : ZMod p) ^ 2 + (b : ZMod p) ^ 2 = 0 := by
  have := (ZMod.natCast_eq_zero_iff _ p).mpr h
  push_cast at this; exact this

namespace Kernels

variable {x y z : ℕ} (k : Kernels x y z)

/-- The three kernel equations read in `ZMod p`. -/
theorem zmod_eqs (hzy : z < y) (hyx : y < x) :
    (x : ZMod p) ^ 2 + (y : ZMod p) ^ 2 = (k.α * k.β : ℕ) * (k.u₁ : ZMod p) ^ 2 ∧
    (x : ZMod p) ^ 2 - (z : ZMod p) ^ 2 = (k.α * k.γ : ℕ) * (k.u₂ : ZMod p) ^ 2 ∧
    (y : ZMod p) ^ 2 - (z : ZMod p) ^ 2 = (k.β * k.γ : ℕ) * (k.u₃ : ZMod p) ^ 2 := by
  have h1 := congrArg (Nat.cast : ℕ → ZMod p) k.h₁
  have h2 := congrArg (Nat.cast : ℕ → ZMod p) k.h₂
  have h3 := congrArg (Nat.cast : ℕ → ZMod p) k.h₃
  rw [Nat.cast_sub (Nat.pow_le_pow_left (hzy.trans hyx).le 2)] at h2
  rw [Nat.cast_sub (Nat.pow_le_pow_left hzy.le 2)] at h3
  push_cast at h1 h2 h3 ⊢
  exact ⟨h1, h2, h3⟩

/-- `prop:characters`, `p ∣ γ`: `χ(αβ) = χ(2)`. -/
theorem char_gamma (hzy : z < y) (hyx : y < x)
    (hcop : ∀ q : ℕ, q.Prime → ¬ (q ∣ x ∧ q ∣ y ∧ q ∣ z)) (hp2 : p ≠ 2) (h : p ∣ k.γ) :
    quadraticChar (ZMod p) (k.α * k.β : ℕ) = quadraticChar (ZMod p) 2 := by
  have hp : p.Prime := Fact.out
  obtain ⟨hxy, hxz⟩ := k.link hp hzy hyx (Or.inr (Or.inr h))
  have hz : ¬ p ∣ z := fun hz => hcop p hp ⟨hxz.mpr hz, hxy.mp (hxz.mpr hz), hz⟩
  obtain ⟨e1, e2, e3⟩ := k.zmod_eqs (p := p) hzy hyx
  have hγ0 : ((k.γ : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).mpr h
  have hxz2 : (x : ZMod p) ^ 2 = (z : ZMod p) ^ 2 := by
    push_cast at e2; rw [hγ0] at e2; linear_combination e2
  have hyz2 : (y : ZMod p) ^ 2 = (z : ZMod p) ^ 2 := by
    push_cast at e3; rw [hγ0] at e3; linear_combination e3
  have hz0 := natCast_ne_zero_of_not_dvd hz
  have key : ((k.α * k.β : ℕ) : ZMod p) * (k.u₁ : ZMod p) ^ 2 = 2 * (z : ZMod p) ^ 2 := by
    rw [← e1, hxz2, hyz2]; ring
  have hu : (k.u₁ : ZMod p) ≠ 0 := by
    intro hu; rw [hu] at key
    have : (2 : ZMod p) * (z : ZMod p) ^ 2 = 0 := by rw [← key]; ring
    rcases mul_eq_zero.mp this with h2 | h2
    · exact two_ne_zero_zmod hp2 h2
    · exact hz0 (pow_eq_zero_iff two_ne_zero |>.mp h2)
  exact char_eq_two hu hz0 key

/-- `prop:characters`, odd `p ∣ α`: `χ(βγ) = χ(2)`. -/
theorem char_alpha (hzy : z < y) (hyx : y < x)
    (hcop : ∀ q : ℕ, q.Prime → ¬ (q ∣ x ∧ q ∣ y ∧ q ∣ z)) (hp2 : p ≠ 2) (h : p ∣ k.α) :
    quadraticChar (ZMod p) (k.β * k.γ : ℕ) = quadraticChar (ZMod p) 2 := by
  have hp : p.Prime := Fact.out
  obtain ⟨hxy, hxz⟩ := k.link hp hzy hyx (Or.inl h)
  have hy : ¬ p ∣ y := fun hy => hcop p hp ⟨hxy.mpr hy, hy, hxz.mp (hxy.mpr hy)⟩
  obtain ⟨e1, e2, -⟩ := k.zmod_eqs (p := p) hzy hyx
  obtain ⟨-, -, e3⟩ := k.zmod_eqs (p := p) hzy hyx
  have hα0 : ((k.α : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).mpr h
  push_cast at e1 e2; rw [hα0] at e1 e2
  -- `x² = -y²` and `x² = z²`, so `y² - z² = 2y²`
  have key : ((k.β * k.γ : ℕ) : ZMod p) * (k.u₃ : ZMod p) ^ 2 = 2 * (y : ZMod p) ^ 2 := by
    rw [← e3]; linear_combination e2 - e1
  have hy0 := natCast_ne_zero_of_not_dvd hy
  have hu : (k.u₃ : ZMod p) ≠ 0 := by
    intro hu; rw [hu] at key
    have : (2 : ZMod p) * (y : ZMod p) ^ 2 = 0 := by rw [← key]; ring
    rcases mul_eq_zero.mp this with h2 | h2
    · exact two_ne_zero_zmod hp2 h2
    · exact hy0 (pow_eq_zero_iff two_ne_zero |>.mp h2)
  exact char_eq_two hu hy0 key

/-- `prop:characters`, odd `p ∣ β`: `χ(αγ) = χ(2)`. -/
theorem char_beta (hzy : z < y) (hyx : y < x)
    (hcop : ∀ q : ℕ, q.Prime → ¬ (q ∣ x ∧ q ∣ y ∧ q ∣ z)) (hp2 : p ≠ 2) (h : p ∣ k.β) :
    quadraticChar (ZMod p) (k.α * k.γ : ℕ) = quadraticChar (ZMod p) 2 := by
  have hp : p.Prime := Fact.out
  obtain ⟨hxy, hxz⟩ := k.link hp hzy hyx (Or.inr (Or.inl h))
  have hx : ¬ p ∣ x := fun hx => hcop p hp ⟨hx, hxy.mp hx, hxz.mp hx⟩
  obtain ⟨e1, e2, e3⟩ := k.zmod_eqs (p := p) hzy hyx
  have hβ0 : ((k.β : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).mpr h
  push_cast at e1 e3; rw [hβ0] at e1 e3
  -- `y² = -x²` and `y² = z²`, so `x² - z² = 2x²`
  have key : ((k.α * k.γ : ℕ) : ZMod p) * (k.u₂ : ZMod p) ^ 2 = 2 * (x : ZMod p) ^ 2 := by
    rw [← e2]; linear_combination e3 - e1
  have hx0 := natCast_ne_zero_of_not_dvd hx
  have hu : (k.u₂ : ZMod p) ≠ 0 := by
    intro hu; rw [hu] at key
    have : (2 : ZMod p) * (x : ZMod p) ^ 2 = 0 := by rw [← key]; ring
    rcases mul_eq_zero.mp this with h2 | h2
    · exact two_ne_zero_zmod hp2 h2
    · exact hx0 (pow_eq_zero_iff two_ne_zero |>.mp h2)
  exact char_eq_two hu hx0 key

end Kernels

end characters

end PerfectCuboid
