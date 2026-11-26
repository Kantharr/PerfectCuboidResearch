import Mathlib

/-!
# The perfect cuboid problem: statement

`IsEulerBrick`, `IsPerfectCuboid` and `FormalConjecturesStatement` are the open problem
exactly as stated in google-deepmind/formal-conjectures, file
`FormalConjectures/Wikipedia/EulerBrick.lean` (Apache License 2.0, copied 2026-11-26
at commit d9f6ffa8dd7f): the definitions are copied verbatim, and the body of
`FormalConjecturesStatement` is the statement of theorem
`EulerBrick.perfect_euler_brick_existence`; only the name is ours.

We then give our own vocabulary in the paper's terms -- a `Cuboid` with edges `A, B, C`,
face diagonals `E, F, G` and space diagonal `D` -- and prove it says the same thing
(`formalConjectures_iff`), so every result in this project is checked against the
community wording.
-/

namespace PerfectCuboid

/--
An **Euler brick** is a rectangular cuboid where all edges and face diagonals have integer lengths.
-/
def IsEulerBrick (a b c : ℕ+) : Prop :=
  IsSquare (a^2 + b^2) ∧ IsSquare (a^2 + c^2) ∧ IsSquare (b^2 + c^2)

/--
A **perfect cuboid** is an Euler brick with an integer space diagonal.
-/
def IsPerfectCuboid (a b c : ℕ+) : Prop :=
  IsEulerBrick a b c ∧ IsSquare (a^2 + b^2 + c^2)

/-- The open problem, verbatim from formal-conjectures (see the module doc). -/
def FormalConjecturesStatement : Prop :=
    ∃ a b c : ℕ+, IsPerfectCuboid a b c

/-- A perfect cuboid in the paper's notation: positive edges `A, B, C`, face diagonals
`E² = A² + B²`, `F² = A² + C²`, `G² = B² + C²` and space diagonal `D² = A² + B² + C²`. -/
structure Cuboid where
  A : ℕ
  B : ℕ
  C : ℕ
  D : ℕ
  E : ℕ
  F : ℕ
  G : ℕ
  hA : 0 < A
  hB : 0 < B
  hC : 0 < C
  hE : A ^ 2 + B ^ 2 = E ^ 2
  hF : A ^ 2 + C ^ 2 = F ^ 2
  hG : B ^ 2 + C ^ 2 = G ^ 2
  hD : A ^ 2 + B ^ 2 + C ^ 2 = D ^ 2

/-- A square in `ℕ+` is a square of naturals after coercion, and conversely. -/
theorem pnat_isSquare_iff (n : ℕ+) : IsSquare n ↔ ∃ r : ℕ, 0 < r ∧ (n : ℕ) = r ^ 2 := by
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨r, r.pos, by rw [hr, PNat.mul_coe, sq]⟩
  · rintro ⟨r, hr0, hr⟩
    refine ⟨(⟨r, hr0⟩ : ℕ+), PNat.eq ?_⟩
    simp [hr, sq]
    rfl

theorem pos_of_eq_sq {n r : ℕ} (hn : 0 < n) (h : n = r ^ 2) : 0 < r :=
  Nat.pos_of_ne_zero (by rintro rfl; simp at h; omega)

/-- Our formulation agrees with the formal-conjectures statement. -/
theorem formalConjectures_iff : FormalConjecturesStatement ↔ Nonempty Cuboid := by
  constructor
  · rintro ⟨a, b, c, ⟨hE, hF, hG⟩, hD⟩
    rw [pnat_isSquare_iff] at hE hF hG hD
    obtain ⟨E, -, hE⟩ := hE
    obtain ⟨F, -, hF⟩ := hF
    obtain ⟨G, -, hG⟩ := hG
    obtain ⟨D, -, hD⟩ := hD
    simp only [PNat.add_coe, PNat.pow_coe] at hE hF hG hD
    exact ⟨⟨a, b, c, D, E, F, G, a.pos, b.pos, c.pos, hE, hF, hG, hD⟩⟩
  · rintro ⟨⟨A, B, C, D, E, F, G, hA, hB, hC, hE, hF, hG, hD⟩⟩
    refine ⟨⟨A, hA⟩, ⟨B, hB⟩, ⟨C, hC⟩, ⟨?_, ?_, ?_⟩, ?_⟩ <;> rw [pnat_isSquare_iff] <;>
      simp only [PNat.add_coe]
    · exact ⟨E, pos_of_eq_sq (by positivity) hE, hE⟩
    · exact ⟨F, pos_of_eq_sq (by positivity) hF, hF⟩
    · exact ⟨G, pos_of_eq_sq (by positivity) hG, hG⟩
    · exact ⟨D, pos_of_eq_sq (by positivity) hD, hD⟩

end PerfectCuboid
