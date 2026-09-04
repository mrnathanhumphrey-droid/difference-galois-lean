import Mathlib
import DiffGalois.Basic
import DiffGalois.Module
set_option linter.style.whitespace false
set_option linter.style.longLine false

/-! # Picard–Vessiot theory — Floor 2

Following van der Put–Singer §1.3 (Prop 1.20), adapted from the differential
to the difference setting (σ replaces the derivation ∂; the maximal-difference-
ideal + simple-quotient skeleton is identical).

Brick 1 (this step): a **difference ideal** is an ideal `I` of a difference ring
`(R, σ)` with `σ(I) ⊆ I`; the quotient `R/I` is again a difference ring. This is
the paragraph before Def 1.15 — move one of the PV construction.
-/

namespace DifferenceRing

variable {R : Type*} [CommRing R] (D : DifferenceRing R)

/-- A **difference ideal** of `(R, σ)`: an ideal closed under the shift `σ`. -/
def IsDifferenceIdeal (I : Ideal R) : Prop :=
  ∀ x ∈ I, D.σ x ∈ I

/-- Probe: descend σ to the quotient as a ring hom, given σ(I) ⊆ I.
Testing the mathlib quotient-map API before building the full equiv. -/
noncomputable def quotσProbe (I : Ideal R) (h : D.IsDifferenceIdeal I) :
    (R ⧸ I) →+* (R ⧸ I) :=
  Ideal.quotientMap I (D.σ : R →+* R) (by
    intro x hx
    exact h x hx)

/-- σ descends to the quotient as a ring **equivalence**, given σ-stability in
both directions. Both are needed: σ(I) ⊆ I to descend σ, σ⁻¹(I) ⊆ I to descend
the inverse, and together they make the descended map invertible. -/
noncomputable def quotσ (I : Ideal R)
    (h : D.IsDifferenceIdeal I) (h' : ∀ x ∈ I, D.σ.symm x ∈ I) :
    (R ⧸ I) ≃+* (R ⧸ I) :=
  RingEquiv.ofRingHom
    (Ideal.quotientMap I (D.σ : R →+* R) (fun x hx => h x hx))
    (Ideal.quotientMap I (D.σ.symm : R →+* R) (fun x hx => h' x hx))
    (by
      ext x
      simp [Ideal.quotientMap_mk])
    (by
      ext x
      simp [Ideal.quotientMap_mk])

/-- The **quotient difference ring** `R ⧸ I` for a difference ideal `I`
(σ-stable both ways). This is the paragraph before vdP–Singer Def 1.15:
`R/I` is again a difference ring over `k`. -/
noncomputable def quotientDifferenceRing (I : Ideal R)
    (h : D.IsDifferenceIdeal I) (h' : ∀ x ∈ I, D.σ.symm x ∈ I) :
    DifferenceRing (R ⧸ I) where
  σ := quotσ D I h h'

/-- A difference ring is **σ-simple** if its only difference ideals are `⊥` and `⊤`.
(vdP–Singer: "a simple differential ring is one whose only differential ideals
are (0) and R".) This is condition 1 of the Picard–Vessiot ring. -/
def IsSigmaSimple : Prop :=
  ∀ I : Ideal R, D.IsDifferenceIdeal I → I = ⊥ ∨ I = ⊤

open Ideal in
/-- **A maximal difference ideal exists** (vdP–Singer Prop 1.20: "let I be a
maximal differential ideal"). The heart of Picard–Vessiot existence. -/
theorem exists_maximal_differenceIdeal (hnt : (⊤ : Ideal R) ≠ ⊥) :
    ∃ I : Ideal R, D.IsDifferenceIdeal I ∧ I ≠ ⊤ ∧
      ∀ J : Ideal R, D.IsDifferenceIdeal J → I < J → J = ⊤ := by
  -- the poset: proper difference ideals
  set S : Set (Ideal R) := {I | D.IsDifferenceIdeal I ∧ I ≠ ⊤} with hS
  -- ⊥ is a proper difference ideal, so S is inhabited at ⊥
  have hbot : (⊥ : Ideal R) ∈ S := by
    refine ⟨?_, ?_⟩
    · intro x hx
      rw [Ideal.mem_bot] at hx ⊢
      rw [hx, map_zero]
    · exact hnt.symm
  have hchain : ∀ c ⊆ S, IsChain (· ≤ ·) c → ∀ y ∈ c,
      ∃ ub ∈ S, ∀ z ∈ c, z ≤ ub := by
    intro c hcS hc y hyc
    refine ⟨sSup c, ⟨?_, ?_⟩, ?_⟩
    · -- (a) sSup c is a difference ideal
      intro x hx
      rw [Submodule.mem_sSup_of_directed ⟨y, hyc⟩ (hc.directedOn)] at hx ⊢
      obtain ⟨I, hIc, hxI⟩ := hx
      exact ⟨I, hIc, (hcS hIc).1 x hxI⟩
    · -- (b) sSup c ≠ ⊤  (properness — the crux)
      rw [Ne, Ideal.eq_top_iff_one]
      intro h1
      rw [Submodule.mem_sSup_of_directed ⟨y, hyc⟩ hc.directedOn] at h1
      obtain ⟨I, hIc, h1I⟩ := h1
      exact (hcS hIc).2 (Ideal.eq_top_iff_one I |>.mpr h1I)
    · -- (c) upper bound
      intro z hzc
      exact le_sSup hzc
  obtain ⟨m, _, hm_max⟩ := zorn_le_nonempty₀ S hchain ⊥ hbot
  refine ⟨m, hm_max.1.1, hm_max.1.2, ?_⟩
  intro J hJ hmJ
  by_contra hJtop
  exact absurd (hm_max.2 ⟨hJ, hJtop⟩ hmJ.le) hmJ.2

/-- **Def 1.15.** A difference-ring structure `E` on the `R`-algebra `S` is a
**Picard–Vessiot ring** for the equation `σ(Y) = A·Y` over the base difference ring `D`:
* `compat` — `E`'s shift extends `D`'s along `algebraMap R S`;
* `simple` — `E` is σ-simple;
* `fundamental` — a fundamental matrix `F ∈ GLₙ(S)` with `σ(F) = A·F`, whose entries
  together with `1/det F` generate `S` over `R`. -/
structure IsPicardVessiot {S : Type*} [CommRing S] [Algebra R S] {n : ℕ}
    (E : DifferenceRing S) (A : Matrix (Fin n) (Fin n) R) : Prop where
  compat : ∀ x : R, E.σ (algebraMap R S x) = algebraMap R S (D.σ x)
  simple : E.IsSigmaSimple
  fundamental : ∃ F : Matrix (Fin n) (Fin n) S, IsUnit F.det ∧
    F.map ⇑E.σ = A.map (algebraMap R S) * F ∧
    Algebra.adjoin R ({s | ∃ i j, F i j = s} ∪ {Ring.inverse F.det}) = ⊤

#check @DifferenceRing.IsPicardVessiot

end DifferenceRing
