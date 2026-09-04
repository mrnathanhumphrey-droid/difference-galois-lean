import Mathlib

/-- A difference ring: a commutative ring `R` equipped with a distinguished
ring automorphism `σ`. This is the fundamental object of difference algebra —
a linear difference equation lives over such a ring. -/
structure DifferenceRing (R : Type*) [CommRing R] where
  /-- The distinguished automorphism. -/
  σ : R ≃+* R

namespace DifferenceRing

variable {R : Type*} [CommRing R] (D : DifferenceRing R)

/-- Apply the difference automorphism to an element. -/
def act (x : R) : R := D.σ x

/-- The automorphism preserves addition. -/
theorem act_add (x y : R) : D.act (x + y) = D.act x + D.act y :=
  map_add D.σ x y

/-- The automorphism preserves multiplication. -/
theorem act_mul (x y : R) : D.act (x * y) = D.act x * D.act y :=
  map_mul D.σ x y

/-- The automorphism fixes one. -/
theorem act_one : D.act (1 : R) = 1 :=
  map_one D.σ

/-- The automorphism fixes zero. -/
theorem act_zero : D.act (0 : R) = 0 :=
  map_zero D.σ

/-- The constants of a difference ring: the elements fixed by `σ`.
The Picard–Vessiot theory is built on the hypothesis that a solution
extension has the *same* constants as the base — so this subring is
the object that entire condition concerns. -/
def constants : Subring R where
  carrier := {x | D.σ x = x}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [map_mul, ha, hb]
  one_mem' := by
    simp only [Set.mem_setOf_eq, map_one]
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [map_add, ha, hb]
  zero_mem' := by
    simp only [Set.mem_setOf_eq, map_zero]
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    rw [map_neg, ha]

/-- Membership in the constants: `x` is a constant iff `σ` fixes it. -/
theorem mem_constants {x : R} : x ∈ D.constants ↔ D.σ x = x := Iff.rfl

end DifferenceRing
