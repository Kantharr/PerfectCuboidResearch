import PerfectCuboid.Statement

/-!
# Section 2 of the paper: the parametrization

* `Cuboid.A_ne_B`, `Cuboid.A_ne_C`, `Cuboid.B_ne_C`, `Cuboid.not_two_odd`,
  `Cuboid.IsPrimitive.one_odd`: `lem:distinct`.
* `exists_normal`: every cuboid can be scaled down to a primitive one and relabelled so
  that `A` is the odd edge and `B < C` (`rem:labelling`, the choices the paper makes).
* `Cuboid.x`, `Cuboid.y`, `Cuboid.z` and `Cuboid.param_B`, `param_C`, `param_D`:
  `prop:param`, in the form `A² - x² = 2Bx`, `A² - y² = 2Cy`, `A² + z² = 2Dz`.
* `Cuboid.order`: `lem:order`, `x > y > z > 0` once `B < C`.
* `Cuboid.parity`: `thm:parity`. The proof here is shorter than the paper's: `A² = x² + 2Bx`
  gives `x ≡ A (mod 2)` directly, and likewise for `y` and `z`.
-/

namespace PerfectCuboid

/-- `2 E² = J²` has no solution with `E ≠ 0` (`2`-adic valuation). -/
theorem two_mul_sq_ne_sq {E J : ℕ} (hE : E ≠ 0) : 2 * E ^ 2 ≠ J ^ 2 := by
  intro h
  have hv := congrArg (fun n => n.factorization 2) h
  simp only [Nat.factorization_mul (by norm_num : (2 : ℕ) ≠ 0) (pow_ne_zero 2 hE),
    Nat.factorization_pow, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
    Nat.prime_two.factorization_self] at hv
  omega

/-- Two odd squares never sum to a square (the sum is `2 (mod 4)`). -/
theorem odd_sq_add_odd_sq_ne_sq {a b c : ℕ} (ha : Odd a) (hb : Odd b) :
    a ^ 2 + b ^ 2 ≠ c ^ 2 := by
  obtain ⟨a, rfl⟩ := ha
  obtain ⟨b, rfl⟩ := hb
  intro h
  have h4 := congrArg (Nat.cast : ℕ → ZMod 4) h
  push_cast at h4
  revert h4
  generalize (a : ZMod 4) = u
  generalize (b : ZMod 4) = v
  generalize (c : ZMod 4) = w
  revert u v w
  decide

namespace Cuboid

variable (c : Cuboid)

/-! ## `lem:distinct` -/

theorem A_ne_B : c.A ≠ c.B := fun h =>
  two_mul_sq_ne_sq (J := c.E) c.hA.ne' (by have := c.hE; rw [← h] at this; omega)

theorem A_ne_C : c.A ≠ c.C := fun h =>
  two_mul_sq_ne_sq (J := c.F) c.hA.ne' (by have := c.hF; rw [← h] at this; omega)

theorem B_ne_C : c.B ≠ c.C := fun h =>
  two_mul_sq_ne_sq (J := c.G) c.hB.ne' (by have := c.hG; rw [← h] at this; omega)

/-- At most one edge is odd. -/
theorem not_two_odd : ¬ (Odd c.A ∧ Odd c.B) ∧ ¬ (Odd c.A ∧ Odd c.C) ∧ ¬ (Odd c.B ∧ Odd c.C) :=
  ⟨fun h => odd_sq_add_odd_sq_ne_sq h.1 h.2 c.hE,
   fun h => odd_sq_add_odd_sq_ne_sq h.1 h.2 c.hF,
   fun h => odd_sq_add_odd_sq_ne_sq h.1 h.2 c.hG⟩

/-- A cuboid is primitive if its edges have no common factor. -/
def IsPrimitive : Prop := Nat.gcd c.A (Nat.gcd c.B c.C) = 1

/-- In a primitive cuboid some edge is odd (and then exactly one, by `not_two_odd`). -/
theorem IsPrimitive.one_odd {c : Cuboid} (h : c.IsPrimitive) : Odd c.A ∨ Odd c.B ∨ Odd c.C := by
  by_contra hne
  simp only [not_or, Nat.not_odd_iff_even] at hne
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨d, hd⟩⟩ := hne
  have h2 : 2 ∣ Nat.gcd c.A (Nat.gcd c.B c.C) :=
    Nat.dvd_gcd ⟨a, by omega⟩ (Nat.dvd_gcd ⟨b, by omega⟩ ⟨d, by omega⟩)
  rw [h] at h2
  omega

/-! ## Relabelling -/

/-- Interchange `A` and `B` (this interchanges `F` and `G`). -/
def swapAB : Cuboid where
  A := c.B
  B := c.A
  C := c.C
  D := c.D
  E := c.E
  F := c.G
  G := c.F
  hA := c.hB
  hB := c.hA
  hC := c.hC
  hE := by rw [add_comm]; exact c.hE
  hF := c.hG
  hG := c.hF
  hD := by rw [← c.hD]; ring

/-- Interchange `A` and `C` (this interchanges `E` and `G`). -/
def swapAC : Cuboid where
  A := c.C
  B := c.B
  C := c.A
  D := c.D
  E := c.G
  F := c.F
  G := c.E
  hA := c.hC
  hB := c.hB
  hC := c.hA
  hE := by rw [add_comm]; exact c.hG
  hF := by rw [add_comm]; exact c.hF
  hG := by rw [add_comm]; exact c.hE
  hD := by rw [← c.hD]; ring

/-- Interchange `B` and `C` (this interchanges `E` and `F`). -/
def swapBC : Cuboid where
  A := c.A
  B := c.C
  C := c.B
  D := c.D
  E := c.F
  F := c.E
  G := c.G
  hA := c.hA
  hB := c.hC
  hC := c.hB
  hE := c.hF
  hF := c.hE
  hG := by rw [add_comm]; exact c.hG
  hD := by rw [← c.hD]; ring

theorem IsPrimitive.swapAB {c : Cuboid} (h : c.IsPrimitive) : c.swapAB.IsPrimitive := by
  unfold IsPrimitive at *; simp only [Cuboid.swapAB]; rw [Nat.gcd_left_comm]; exact h

theorem IsPrimitive.swapAC {c : Cuboid} (h : c.IsPrimitive) : c.swapAC.IsPrimitive := by
  unfold IsPrimitive at *; simp only [Cuboid.swapAC]
  rw [Nat.gcd_comm c.B c.A, Nat.gcd_left_comm, Nat.gcd_comm c.C c.B]; exact h

theorem IsPrimitive.swapBC {c : Cuboid} (h : c.IsPrimitive) : c.swapBC.IsPrimitive := by
  unfold IsPrimitive at *; simp only [Cuboid.swapBC]; rw [Nat.gcd_comm c.C]; exact h

end Cuboid

/-- If `g² ∣ n²` then `g ∣ n`. -/
theorem dvd_of_sq_dvd_sq {g n : ℕ} (h : g ^ 2 ∣ n ^ 2) : g ∣ n :=
  (Nat.pow_dvd_pow_iff two_ne_zero).mp h

/-- Every cuboid gives a primitive one, by dividing all seven lengths by the gcd of the
edges. -/
theorem exists_primitive (c : Cuboid) : ∃ c' : Cuboid, c'.IsPrimitive := by
  set g := Nat.gcd c.A (Nat.gcd c.B c.C) with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ c.hA
  obtain ⟨a, ha⟩ : g ∣ c.A := Nat.gcd_dvd_left _ _
  obtain ⟨b, hb⟩ : g ∣ c.B := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)
  obtain ⟨d, hd⟩ : g ∣ c.C := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _)
  have sq : ∀ {u v w : ℕ}, u ^ 2 + v ^ 2 = w ^ 2 → g ∣ u → g ∣ v → g ∣ w := fun h hu hv =>
    dvd_of_sq_dvd_sq (h ▸ dvd_add (pow_dvd_pow_of_dvd hu 2) (pow_dvd_pow_of_dvd hv 2))
  obtain ⟨e, he⟩ := sq c.hE ⟨a, ha⟩ ⟨b, hb⟩
  obtain ⟨f, hf⟩ := sq c.hF ⟨a, ha⟩ ⟨d, hd⟩
  obtain ⟨k, hk⟩ := sq c.hG ⟨b, hb⟩ ⟨d, hd⟩
  have hDdvd : g ∣ c.D := dvd_of_sq_dvd_sq (c.hD ▸ dvd_add (dvd_add
    (pow_dvd_pow_of_dvd ⟨a, ha⟩ 2) (pow_dvd_pow_of_dvd ⟨b, hb⟩ 2)) (pow_dvd_pow_of_dvd ⟨d, hd⟩ 2))
  obtain ⟨D', hD'⟩ := hDdvd
  have hg2 : 0 < g ^ 2 := pow_pos hg0 2
  have cancel : ∀ {u v : ℕ}, g ^ 2 * u = g ^ 2 * v → u = v := fun h =>
    Nat.eq_of_mul_eq_mul_left hg2 h
  have pa : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; have := c.hA; omega)
  have pb : 0 < b := Nat.pos_of_ne_zero (by rintro rfl; have := c.hB; omega)
  have pd : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; have := c.hC; omega)
  refine ⟨⟨a, b, d, D', e, f, k, pa, pb, pd, cancel ?_, cancel ?_, cancel ?_, cancel ?_⟩, ?_⟩
  · have := c.hE; rw [ha, hb, he] at this; linear_combination this
  · have := c.hF; rw [ha, hd, hf] at this; linear_combination this
  · have := c.hG; rw [hb, hd, hk] at this; linear_combination this
  · have := c.hD; rw [ha, hb, hd, hD'] at this; linear_combination this
  · show Nat.gcd a (Nat.gcd b d) = 1
    have h1 : g = g * Nat.gcd a (Nat.gcd b d) := by
      conv_lhs => rw [hg, ha, hb, hd]
      rw [Nat.gcd_mul_left, Nat.gcd_mul_left]
    have := Nat.eq_of_mul_eq_mul_left hg0 (h1.symm.trans (mul_one g).symm)
    exact this

/-- The normal form used throughout the paper: a perfect cuboid exists iff there is a
primitive one whose odd edge is `A` and with `B < C`. -/
theorem exists_normal (c : Cuboid) : ∃ c' : Cuboid, c'.IsPrimitive ∧ Odd c'.A ∧ c'.B < c'.C := by
  obtain ⟨c₁, hp⟩ := exists_primitive c
  obtain ⟨c₂, hp₂, hodd⟩ : ∃ c₂ : Cuboid, c₂.IsPrimitive ∧ Odd c₂.A := by
    rcases hp.one_odd with h | h | h
    · exact ⟨c₁, hp, h⟩
    · exact ⟨c₁.swapAB, hp.swapAB, h⟩
    · exact ⟨c₁.swapAC, hp.swapAC, h⟩
  rcases lt_or_gt_of_ne c₂.B_ne_C with h | h
  · exact ⟨c₂, hp₂, hodd, h⟩
  · exact ⟨c₂.swapBC, hp₂.swapBC, hodd, h⟩

namespace Cuboid

variable (c : Cuboid)

/-! ## `prop:param` -/

/-- `x = E - B`. -/
def x : ℤ := c.E - c.B
/-- `y = F - C`. -/
def y : ℤ := c.F - c.C
/-- `z = D - G`. -/
def z : ℤ := c.D - c.G

theorem hE_int : (c.A : ℤ) ^ 2 + c.B ^ 2 = c.E ^ 2 := by exact_mod_cast c.hE
theorem hF_int : (c.A : ℤ) ^ 2 + c.C ^ 2 = c.F ^ 2 := by exact_mod_cast c.hF
theorem hG_int : (c.B : ℤ) ^ 2 + c.C ^ 2 = c.G ^ 2 := by exact_mod_cast c.hG
theorem hD_int : (c.A : ℤ) ^ 2 + c.B ^ 2 + c.C ^ 2 = c.D ^ 2 := by exact_mod_cast c.hD

/-- `B = (A² - x²)/(2x)`. -/
theorem param_B : (c.A : ℤ) ^ 2 - c.x ^ 2 = 2 * c.B * c.x := by
  unfold x; linear_combination c.hE_int

/-- `C = (A² - y²)/(2y)`. -/
theorem param_C : (c.A : ℤ) ^ 2 - c.y ^ 2 = 2 * c.C * c.y := by
  unfold y; linear_combination c.hF_int

/-- `D = (A² + z²)/(2z)`. -/
theorem param_D : (c.A : ℤ) ^ 2 + c.z ^ 2 = 2 * c.D * c.z := by
  unfold z; linear_combination c.hD_int - c.hG_int

/-- `a² < b²` with `a, b ≥ 0` gives `a < b`, over `ℤ`. -/
theorem lt_of_sq_lt_sq' {a b : ℤ} (hb : 0 ≤ b) (h : a ^ 2 < b ^ 2) : a < b :=
  lt_of_pow_lt_pow_left₀ 2 hb h

theorem A_pos_int : (0 : ℤ) < c.A := by exact_mod_cast c.hA

theorem B_lt_E : (c.B : ℤ) < c.E := by
  apply lt_of_sq_lt_sq' (by positivity)
  have := c.hE_int; have := c.A_pos_int; nlinarith

theorem C_lt_F : (c.C : ℤ) < c.F := by
  apply lt_of_sq_lt_sq' (by positivity)
  have := c.hF_int; have := c.A_pos_int; nlinarith

theorem G_lt_D : (c.G : ℤ) < c.D := by
  apply lt_of_sq_lt_sq' (by positivity)
  have := c.hD_int; have := c.hG_int; have := c.A_pos_int; nlinarith

theorem x_pos : 0 < c.x := by unfold x; linarith [c.B_lt_E]
theorem y_pos : 0 < c.y := by unfold y; linarith [c.C_lt_F]
theorem z_pos : 0 < c.z := by unfold z; linarith [c.G_lt_D]

/-! ## `lem:order` -/

/-- `lem:order`: with `B < C`, `x > y > z > 0`. -/
theorem order (h : c.B < c.C) : c.y < c.x ∧ c.z < c.y ∧ 0 < c.z := by
  have hBC : (c.B : ℤ) < c.C := by exact_mod_cast h
  have hA : (0 : ℤ) < c.A := by exact_mod_cast c.hA
  have hB : (0 : ℤ) < c.B := by exact_mod_cast c.hB
  -- `x (E + B) = A² = y (F + C) = z (D + G)`
  have h1 : c.x * (c.E + c.B) = (c.A : ℤ) ^ 2 := by unfold x; linear_combination -c.hE_int
  have h2 : c.y * (c.F + c.C) = (c.A : ℤ) ^ 2 := by unfold y; linear_combination -c.hF_int
  have h3 : c.z * (c.D + c.G) = (c.A : ℤ) ^ 2 := by
    unfold z; linear_combination -c.hD_int + c.hG_int
  -- `E < F`, `C < G`, `F < D`
  have hEF : (c.E : ℤ) < c.F := lt_of_sq_lt_sq' (by positivity) (by
    have := c.hE_int; have := c.hF_int; nlinarith)
  have hCG : (c.C : ℤ) < c.G := lt_of_sq_lt_sq' (by positivity) (by
    have := c.hG_int; nlinarith)
  have hFD : (c.F : ℤ) < c.D := lt_of_sq_lt_sq' (by positivity) (by
    have := c.hF_int; have := c.hD_int; nlinarith)
  have hx := c.x_pos
  have hy := c.y_pos
  have hz := c.z_pos
  refine ⟨?_, ?_, hz⟩
  · by_contra hle
    replace hle := not_lt.mp hle
    have : c.x * (c.E + c.B) < c.y * (c.F + c.C) :=
      calc c.x * (c.E + c.B) ≤ c.y * (c.E + c.B) :=
            mul_le_mul_of_nonneg_right hle (by positivity)
        _ < c.y * (c.F + c.C) := mul_lt_mul_of_pos_left (by linarith) hy
    linarith
  · by_contra hle
    replace hle := not_lt.mp hle
    have : c.y * (c.F + c.C) < c.z * (c.D + c.G) :=
      calc c.y * (c.F + c.C) ≤ c.z * (c.F + c.C) :=
            mul_le_mul_of_nonneg_right hle (by positivity)
        _ < c.z * (c.D + c.G) := mul_lt_mul_of_pos_left (by linarith) hz
    linarith

/-! ## `thm:parity` -/

/-- `thm:parity`: `x`, `y` and `z` each have the parity of `A`. In particular they all have
the same parity, and they are all odd if and only if `A` is odd. -/
theorem parity : (Even c.x ↔ Even (c.A : ℤ)) ∧ (Even c.y ↔ Even (c.A : ℤ)) ∧
    (Even c.z ↔ Even (c.A : ℤ)) := by
  have hB := c.param_B
  have hC := c.param_C
  have hD := c.param_D
  have ev2 : ∀ u v : ℤ, Even (2 * u * v) := fun u v => ⟨u * v, by ring⟩
  refine ⟨?_, ?_, ?_⟩
  · have := ev2 c.B c.x
    rw [← hB, Int.even_sub, Int.even_pow' two_ne_zero, Int.even_pow' two_ne_zero] at this
    exact this.symm
  · have := ev2 c.C c.y
    rw [← hC, Int.even_sub, Int.even_pow' two_ne_zero, Int.even_pow' two_ne_zero] at this
    exact this.symm
  · have := ev2 c.D c.z
    rw [← hD, Int.even_add, Int.even_pow' two_ne_zero, Int.even_pow' two_ne_zero] at this
    exact this.symm

/-- With `A` the odd edge, `x`, `y`, `z` are all odd. -/
theorem odd_xyz (h : Odd c.A) : Odd c.x ∧ Odd c.y ∧ Odd c.z := by
  have hA : ¬ Even (c.A : ℤ) := by
    rw [Int.not_even_iff_odd]; exact_mod_cast h
  obtain ⟨px, py, pz⟩ := c.parity
  simp only [← Int.not_even_iff_odd]
  exact ⟨fun h => hA (px.mp h), fun h => hA (py.mp h), fun h => hA (pz.mp h)⟩

end Cuboid

end PerfectCuboid
