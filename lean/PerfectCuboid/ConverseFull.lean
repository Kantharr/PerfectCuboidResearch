import PerfectCuboid.Valuation

/-!
# `thm:converse-full`

`BadPair p e u v ε`: `p` divides `u` and `v` exactly to the same exponent `e ≥ 1` and
divides `N = u₀² + ε v₀²` (`u = pᵉ u₀`, `v = pᵉ v₀`). `BadPrime x y z p` says this happens
for one of the pairs of `lem:twovar`: `(x, y)` with `ε = 1` and `p ∤ z`, or `(x, z)`, `(y, z)`
with `ε = -1` and `p` not dividing the third variable.

* `pair_dvd`: away from the bad case, every power of `p` dividing `u` or `v` divides `A²`
  (`lem:twovar` (i) and (ii) with `δ = 0`, in both orientations `e₁ < e₂`, `e₁ > e₂`).
* `pair_xy`, `pair_xz`, `pair_yz`: the three instances.
* `dvd_of_prime_pow_dvd`: `d ∣ n` iff every prime power dividing `d` divides `n`.
* `converse_full`: `thm:converse-full`. For odd `x > y > z > 0` with no prime dividing all
  three, `R = κ²` with `κ > 0` and `A > 0` on the surviving branch, `(A, B, C)` is a perfect
  cuboid iff there is no bad prime.
-/

namespace PerfectCuboid

/-- The exceptional configuration of `lem:twovar` (ii) with `δ > 0`, for one pair. -/
def BadPair (p e : ℕ) (u v ε : ℤ) : Prop :=
  1 ≤ e ∧ ∃ u₀ v₀ : ℤ, u = (p : ℤ) ^ e * u₀ ∧ v = (p : ℤ) ^ e * v₀ ∧ ¬ (p : ℤ) ∣ u₀ ∧
    ¬ (p : ℤ) ∣ v₀ ∧ (p : ℤ) ∣ u₀ ^ 2 + ε * v₀ ^ 2

/-- A prime excluded by `thm:converse-full`. -/
def BadPrime (x y z : ℤ) (p : ℕ) : Prop :=
  p.Prime ∧ ∃ e, (BadPair p e x y 1 ∧ ¬ (p : ℤ) ∣ z) ∨ (BadPair p e x z (-1) ∧ ¬ (p : ℤ) ∣ y) ∨
    (BadPair p e y z (-1) ∧ ¬ (p : ℤ) ∣ x)

section

variable {p : ℕ} (hp : p.Prime)
include hp

theorem not_dvd_sq {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) : ¬ (p : ℤ) ∣ a ^ 2 :=
  fun h => ha (dvd_of_dvd_sq' hp h)

omit hp in
theorem dvd_sq_of_dvd {a : ℤ} (ha : (p : ℤ) ∣ a) : (p : ℤ) ∣ a ^ 2 := dvd_pow ha two_ne_zero

omit hp in
/-- `p ∣ a`, `p ∤ b` give `p ∤ a + b`. -/
theorem not_dvd_add_of {a b : ℤ} (ha : (p : ℤ) ∣ a) (hb : ¬ (p : ℤ) ∣ b) : ¬ (p : ℤ) ∣ a + b :=
  fun h => hb ((dvd_add_right ha).mp h)

/-- The generic pair: away from the bad case, every power of `p` dividing `u` or `v` divides
`A²`. -/
theorem pair_dvd {A u v w U S' m' κ ε : ℤ} (hε : ε = 1 ∨ ε = -1) (hm : m' = u * v * w)
    (hR : κ ^ 2 = (u ^ 2 + ε * v ^ 2) * U) (hU : ¬ (p : ℤ) ∣ U) (hw : ¬ (p : ℤ) ∣ w)
    (hS : ¬ (p : ℤ) ∣ S') (hκ : κ ≠ 0) (hA0 : A ≠ 0) (hA : A ^ 2 * (m' - κ) = m' * S')
    (hu : u ≠ 0) (hv : v ≠ 0) (hgood : ∀ e, ¬ BadPair p e u v ε) :
    (∀ f, (p : ℤ) ^ f ∣ u → (p : ℤ) ^ f ∣ A ^ 2) ∧ (∀ f, (p : ℤ) ^ f ∣ v → (p : ℤ) ^ f ∣ A ^ 2) := by
  obtain ⟨e₁, u₀, rfl, hu₀⟩ := ExactPow.exists_of_ne_zero hp hu
  obtain ⟨e₂, v₀, rfl, hv₀⟩ := ExactPow.exists_of_ne_zero hp hv
  have hu' : ExactPow p e₁ ((p : ℤ) ^ e₁ * u₀) := ExactPow.mk hu₀
  have hv' : ExactPow p e₂ ((p : ℤ) ^ e₂ * v₀) := ExactPow.mk hv₀
  -- it suffices to find `E ≥ max e₁ e₂` with `v_p(A²) = E`
  suffices ∃ E, e₁ ≤ E ∧ e₂ ≤ E ∧ ExactPow p E (A ^ 2) by
    obtain ⟨E, h1, h2, hE⟩ := this
    refine ⟨fun f hf => (hE.dvd_iff hp).mpr ?_, fun f hf => (hE.dvd_iff hp).mpr ?_⟩
    · exact ((hu'.dvd_iff hp).mp hf).trans h1
    · exact ((hv'.dvd_iff hp).mp hf).trans h2
  rcases lt_trichotomy e₁ e₂ with h | h | h
  · exact ⟨e₂, h.le, le_rfl, twovar_lt hp hm hR hU hw hS rfl rfl hu₀ hv₀ hκ hA0 hA h⟩
  · subst h
    rcases Nat.eq_zero_or_pos e₁ with h0 | h0
    · subst h0
      -- `p` divides neither: `v_p(A²) ≥ 0` is all that is asked
      obtain ⟨E, hE⟩ := ExactPow.exists_of_ne_zero hp (pow_ne_zero 2 hA0)
      exact ⟨E, Nat.zero_le _, Nat.zero_le _, hE⟩
    · have hN : ¬ (p : ℤ) ∣ u₀ ^ 2 + ε * v₀ ^ 2 :=
        fun hN => hgood e₁ ⟨h0, u₀, v₀, rfl, rfl, hu₀, hv₀, hN⟩
      exact ⟨e₁, le_rfl, le_rfl,
        twovar_eq_good hp hm hR hU hw hS rfl rfl hu₀ hv₀ hκ hA0 hA h0 hN⟩
  · -- swap the roles of `u` and `v`: `u² + ε v² = ε (v² + ε u²)`
    have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
    have hR' : κ ^ 2 = (((p : ℤ) ^ e₂ * v₀) ^ 2 + ε * ((p : ℤ) ^ e₁ * u₀) ^ 2) * (ε * U) := by
      rw [hR]; linear_combination (-((p : ℤ) ^ e₁ * u₀) ^ 2 * U) * hε2
    have hU' : ¬ (p : ℤ) ∣ ε * U := by
      rcases hε with rfl | rfl
      · simpa using hU
      · simpa using hU
    have hm' : m' = (p : ℤ) ^ e₂ * v₀ * ((p : ℤ) ^ e₁ * u₀) * w := by rw [hm]; ring
    exact ⟨e₁, le_rfl, h.le, twovar_lt hp hm' hR' hU' hw hS rfl rfl hv₀ hu₀ hκ hA0 hA h⟩

/-- The bad case: `pᵉ ∤ A²`. -/
theorem pair_bad {A u v w U S' m' κ ε : ℤ} {e : ℕ} (hm : m' = u * v * w)
    (hR : κ ^ 2 = (u ^ 2 + ε * v ^ 2) * U) (hw : ¬ (p : ℤ) ∣ w) (hS : ¬ (p : ℤ) ∣ S')
    (hκ : κ ≠ 0) (hA : A ^ 2 * (m' - κ) = m' * S') (hbad : BadPair p e u v ε) :
    ¬ (p : ℤ) ^ e ∣ A ^ 2 := by
  obtain ⟨he, u₀, v₀, hu, hv, hu₀, hv₀, hN⟩ := hbad
  exact twovar_eq_bad hp hm hR hw hS hu hv hu₀ hv₀ hκ hA he hN

/-! The three pairs of the paper. -/

variable {A x y z κ : ℤ}

theorem setup_xy (hpx : (p : ℤ) ∣ x) (hpy : (p : ℤ) ∣ y) (hpz : ¬ (p : ℤ) ∣ z) :
    m x y z = x * y * z ∧ R x y z = (x ^ 2 + 1 * y ^ 2) * ((x ^ 2 - z ^ 2) * (y ^ 2 - z ^ 2)) ∧
    ¬ (p : ℤ) ∣ (x ^ 2 - z ^ 2) * (y ^ 2 - z ^ 2) ∧ ¬ (p : ℤ) ∣ S x y z := by
  have hz2 : ¬ (p : ℤ) ∣ -z ^ 2 := by rw [dvd_neg]; exact not_dvd_sq hp hpz
  refine ⟨rfl, by unfold R; ring, not_dvd_mul' hp ?_ ?_, ?_⟩
  · rw [sub_eq_add_neg]; exact not_dvd_add_of (dvd_sq_of_dvd hpx) hz2
  · rw [sub_eq_add_neg]; exact not_dvd_add_of (dvd_sq_of_dvd hpy) hz2
  · unfold S; rw [sub_eq_add_neg]
    exact not_dvd_add_of (dvd_add (dvd_sq_of_dvd hpx) (dvd_sq_of_dvd hpy)) hz2

theorem setup_xz (hpx : (p : ℤ) ∣ x) (hpz : (p : ℤ) ∣ z) (hpy : ¬ (p : ℤ) ∣ y) :
    m x y z = x * z * y ∧ R x y z = (x ^ 2 + -1 * z ^ 2) * ((x ^ 2 + y ^ 2) * (y ^ 2 - z ^ 2)) ∧
    ¬ (p : ℤ) ∣ (x ^ 2 + y ^ 2) * (y ^ 2 - z ^ 2) ∧ ¬ (p : ℤ) ∣ S x y z := by
  have hy2 := not_dvd_sq hp hpy
  refine ⟨by unfold m; ring, by unfold R; ring, not_dvd_mul' hp ?_ ?_, ?_⟩
  · exact not_dvd_add_of (dvd_sq_of_dvd hpx) hy2
  · rw [show y ^ 2 - z ^ 2 = -z ^ 2 + y ^ 2 by ring]
    exact not_dvd_add_of ((dvd_sq_of_dvd hpz).neg_right) hy2
  · unfold S; rw [show x ^ 2 + y ^ 2 - z ^ 2 = (x ^ 2 - z ^ 2) + y ^ 2 by ring]
    exact not_dvd_add_of (dvd_sub (dvd_sq_of_dvd hpx) (dvd_sq_of_dvd hpz)) hy2

theorem setup_yz (hpy : (p : ℤ) ∣ y) (hpz : (p : ℤ) ∣ z) (hpx : ¬ (p : ℤ) ∣ x) :
    m x y z = y * z * x ∧ R x y z = (y ^ 2 + -1 * z ^ 2) * ((x ^ 2 + y ^ 2) * (x ^ 2 - z ^ 2)) ∧
    ¬ (p : ℤ) ∣ (x ^ 2 + y ^ 2) * (x ^ 2 - z ^ 2) ∧ ¬ (p : ℤ) ∣ S x y z := by
  have hx2 := not_dvd_sq hp hpx
  refine ⟨by unfold m; ring, by unfold R; ring, not_dvd_mul' hp ?_ ?_, ?_⟩
  · rw [add_comm]; exact not_dvd_add_of (dvd_sq_of_dvd hpy) hx2
  · rw [show x ^ 2 - z ^ 2 = -z ^ 2 + x ^ 2 by ring]
    exact not_dvd_add_of ((dvd_sq_of_dvd hpz).neg_right) hx2
  · unfold S; rw [show x ^ 2 + y ^ 2 - z ^ 2 = (y ^ 2 - z ^ 2) + x ^ 2 by ring]
    exact not_dvd_add_of (dvd_sub (dvd_sq_of_dvd hpy) (dvd_sq_of_dvd hpz)) hx2

end

/-- `d ∣ n` iff every prime power dividing `d` divides `n`. -/
theorem dvd_of_prime_pow_dvd {d n : ℤ} (hd : d ≠ 0) (hn : n ≠ 0)
    (h : ∀ p : ℕ, p.Prime → ∀ f : ℕ, (p : ℤ) ^ f ∣ d → (p : ℤ) ^ f ∣ n) : d ∣ n := by
  rw [← Int.natAbs_dvd_natAbs, ← Nat.factorization_prime_le_iff_dvd (Int.natAbs_ne_zero.mpr hd)
    (Int.natAbs_ne_zero.mpr hn)]
  intro p hp
  have h1 : ((p ^ d.natAbs.factorization p : ℕ) : ℤ) ∣ d :=
    Int.natCast_dvd.mpr (Nat.ordProj_dvd _ _)
  push_cast at h1
  have h2 := Int.natCast_dvd.mp (by push_cast; exact h p hp _ h1 :
    ((p ^ d.natAbs.factorization p : ℕ) : ℤ) ∣ n)
  exact (hp.pow_dvd_iff_le_factorization (Int.natAbs_ne_zero.mpr hn)).mp h2

/-- `thm:converse-full`. -/
theorem converse_full {x y z κ A : ℤ} (hx : Odd x) (hy : Odd y) (hz : Odd z) (hz0 : 0 < z)
    (hzy : z < y) (hyx : y < x) (hκ : 0 < κ) (hκ2 : κ ^ 2 = R x y z) (hA0 : 0 < A)
    (hA : A ^ 2 * (m x y z - κ) = m x y z * S x y z)
    (hcop : ∀ p : ℕ, p.Prime → ¬ ((p : ℤ) ∣ x ∧ (p : ℤ) ∣ y ∧ (p : ℤ) ∣ z)) :
    (∃ c : Cuboid, (c.A : ℤ) = A ∧ c.x = x ∧ c.y = y ∧ c.z = z) ↔
      ¬ ∃ p, BadPrime x y z p := by
  rw [converse hx hy hz hz0 hzy hyx hκ hκ2 hA0 hA]
  obtain ⟨hm, hS, -, -⟩ := branch_facts hz0 hzy hyx hκ hA0.ne' hA
  have hy0 : 0 < y := hz0.trans hzy
  have hx0 : 0 < x := hy0.trans hyx
  have hκ0 := hκ.ne'
  have hA0' := hA0.ne'
  constructor
  · rintro ⟨dx, dy, dz⟩ ⟨p, hp, e, h⟩
    rcases h with ⟨hb, hpz⟩ | ⟨hb, hpy⟩ | ⟨hb, hpx⟩
    · obtain ⟨he, u₀, v₀, hu, hv, -⟩ := id hb
      have hpx : (p : ℤ) ∣ x := hu ▸ (dvd_pow_self _ (by omega)).mul_right _
      have hpy : (p : ℤ) ∣ y := hv ▸ (dvd_pow_self _ (by omega)).mul_right _
      obtain ⟨h1, h2, -, h4⟩ := setup_xy hp hpx hpy hpz
      exact pair_bad hp h1 (hκ2.trans h2) hpz h4 hκ0 hA hb ((Dvd.intro u₀ hu.symm).trans dx)
    · obtain ⟨he, u₀, v₀, hu, hv, -⟩ := id hb
      have hpx : (p : ℤ) ∣ x := hu ▸ (dvd_pow_self _ (by omega)).mul_right _
      have hpz : (p : ℤ) ∣ z := hv ▸ (dvd_pow_self _ (by omega)).mul_right _
      obtain ⟨h1, h2, -, h4⟩ := setup_xz hp hpx hpz hpy
      exact pair_bad hp h1 (hκ2.trans h2) hpy h4 hκ0 hA hb ((Dvd.intro u₀ hu.symm).trans dx)
    · obtain ⟨he, u₀, v₀, hu, hv, -⟩ := id hb
      have hpy : (p : ℤ) ∣ y := hu ▸ (dvd_pow_self _ (by omega)).mul_right _
      have hpz : (p : ℤ) ∣ z := hv ▸ (dvd_pow_self _ (by omega)).mul_right _
      obtain ⟨h1, h2, -, h4⟩ := setup_yz hp hpy hpz hpx
      exact pair_bad hp h1 (hκ2.trans h2) hpx h4 hκ0 hA hb ((Dvd.intro u₀ hu.symm).trans dy)
  · intro hno
    have good : ∀ p : ℕ, p.Prime → ∀ e,
        ((¬ (p : ℤ) ∣ z → ¬ BadPair p e x y 1) ∧ (¬ (p : ℤ) ∣ y → ¬ BadPair p e x z (-1)) ∧
          (¬ (p : ℤ) ∣ x → ¬ BadPair p e y z (-1))) := fun p hp e =>
      ⟨fun h hb => hno ⟨p, hp, e, Or.inl ⟨hb, h⟩⟩,
       fun h hb => hno ⟨p, hp, e, Or.inr (Or.inl ⟨hb, h⟩)⟩,
       fun h hb => hno ⟨p, hp, e, Or.inr (Or.inr ⟨hb, h⟩)⟩⟩
    have hA2 : A ^ 2 ≠ 0 := pow_ne_zero 2 hA0'
    refine ⟨dvd_of_prime_pow_dvd hx0.ne' hA2 ?_, dvd_of_prime_pow_dvd hy0.ne' hA2 ?_,
      dvd_of_prime_pow_dvd hz0.ne' hA2 ?_⟩ <;> intro p hp f hf
    · by_cases hpx : (p : ℤ) ∣ x
      swap
      · rcases Nat.eq_zero_or_pos f with rfl | hf0
        · simp
        · exact absurd ((dvd_pow_self _ hf0.ne').trans hf) hpx
      by_cases hpy : (p : ℤ) ∣ y <;> by_cases hpz : (p : ℤ) ∣ z
      · exact absurd ⟨hpx, hpy, hpz⟩ (hcop p hp)
      · obtain ⟨h1, h2, h3, h4⟩ := setup_xy hp hpx hpy hpz
        exact (pair_dvd hp (Or.inl rfl) h1 (hκ2.trans h2) h3 hpz h4 hκ0 hA0' hA hx0.ne' hy0.ne'
          (fun e => (good p hp e).1 hpz)).1 f hf
      · obtain ⟨h1, h2, h3, h4⟩ := setup_xz hp hpx hpz hpy
        exact (pair_dvd hp (Or.inr rfl) h1 (hκ2.trans h2) h3 hpy h4 hκ0 hA0' hA hx0.ne' hz0.ne'
          (fun e => (good p hp e).2.1 hpy)).1 f hf
      · exact onevar hp hS.ne' hκ2 hA hf hpy hpz
    · by_cases hpy : (p : ℤ) ∣ y
      swap
      · rcases Nat.eq_zero_or_pos f with rfl | hf0
        · simp
        · exact absurd ((dvd_pow_self _ hf0.ne').trans hf) hpy
      by_cases hpx : (p : ℤ) ∣ x <;> by_cases hpz : (p : ℤ) ∣ z
      · exact absurd ⟨hpx, hpy, hpz⟩ (hcop p hp)
      · obtain ⟨h1, h2, h3, h4⟩ := setup_xy hp hpx hpy hpz
        exact (pair_dvd hp (Or.inl rfl) h1 (hκ2.trans h2) h3 hpz h4 hκ0 hA0' hA hx0.ne' hy0.ne'
          (fun e => (good p hp e).1 hpz)).2 f hf
      · obtain ⟨h1, h2, h3, h4⟩ := setup_yz hp hpy hpz hpx
        exact (pair_dvd hp (Or.inr rfl) h1 (hκ2.trans h2) h3 hpx h4 hκ0 hA0' hA hy0.ne' hz0.ne'
          (fun e => (good p hp e).2.2 hpx)).1 f hf
      · exact dvd_A_sq_of_coprime_y hS.ne' hκ2 hA hf (isCoprime_prime_pow hp f hpx hpz)
    · by_cases hpz : (p : ℤ) ∣ z
      swap
      · rcases Nat.eq_zero_or_pos f with rfl | hf0
        · simp
        · exact absurd ((dvd_pow_self _ hf0.ne').trans hf) hpz
      by_cases hpx : (p : ℤ) ∣ x <;> by_cases hpy : (p : ℤ) ∣ y
      · exact absurd ⟨hpx, hpy, hpz⟩ (hcop p hp)
      · obtain ⟨h1, h2, h3, h4⟩ := setup_xz hp hpx hpz hpy
        exact (pair_dvd hp (Or.inr rfl) h1 (hκ2.trans h2) h3 hpy h4 hκ0 hA0' hA hx0.ne' hz0.ne'
          (fun e => (good p hp e).2.1 hpy)).2 f hf
      · obtain ⟨h1, h2, h3, h4⟩ := setup_yz hp hpy hpz hpx
        exact (pair_dvd hp (Or.inr rfl) h1 (hκ2.trans h2) h3 hpx h4 hκ0 hA0' hA hy0.ne' hz0.ne'
          (fun e => (good p hp e).2.2 hpx)).2 f hf
      · exact dvd_A_sq_of_coprime_z hS.ne' hκ2 hA hf (isCoprime_prime_pow hp f hpx hpy)

end PerfectCuboid
