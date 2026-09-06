import Mathlib
import DiffGalois.Basic
import DiffGalois.Module
import DiffGalois.PicardVessiot
set_option linter.style.whitespace false
set_option linter.style.longLine false
set_option linter.style.missingEnd false

/-! # The difference-Galois group — Floor 6

For a difference-ring extension `S / R` (an `R`-algebra `S` carrying a compatible shift
`E.σ` extending `D.σ`), the **difference-Galois group** `Gal` is the group of
`R`-algebra automorphisms of `S` that commute with the shift. As a subgroup of the
automorphism group `S ≃ₐ[R] S` (mathlib's `AlgEquiv.aut`), it inherits its group structure
for free. Instantiated at `S = R₀` (the Picard–Vessiot ring), this is the Galois group of a
difference equation — the object the whole tower reconstructs.
-/

namespace DifferenceRing

variable {R : Type*} [CommRing R] (D : DifferenceRing R)
  {S : Type*} [CommRing S] [Algebra R S] (E : DifferenceRing S)

/-- The difference-Galois group of a difference-ring extension `S / R`: the `R`-algebra
automorphisms of `S` commuting with the shift `E.σ`, as a subgroup of `S ≃ₐ[R] S`.
Composition and inverse preserve σ-commutation, so this is a genuine subgroup. -/
def galoisGroup : Subgroup (S ≃ₐ[R] S) where
  carrier := {φ | ∀ x, φ (E.σ x) = E.σ (φ x)}
  mul_mem' := by
    intro φ ψ hφ hψ x
    simp only [AlgEquiv.mul_apply]
    rw [hψ x, hφ (ψ x)]
  one_mem' := by
    intro x
    simp only [AlgEquiv.one_apply]
  inv_mem' := by
    intro φ hφ x
    rw [AlgEquiv.aut_inv]
    apply φ.injective
    rw [AlgEquiv.apply_symm_apply, hφ (φ.symm x), AlgEquiv.apply_symm_apply]

/-- **Chevalley atom: in a σ-simple difference ring, every nonzero constant is a unit.**
The principal ideal `(c)` of a constant `c` is σ-stable (because `σ(r·c) = σr·c`), so
σ-simplicity forces it to be `⊥` or `⊤`; `c ≠ 0` rules out `⊥`, leaving `⊤`, i.e. `c` is a
unit. This is the seed of "no new constants". -/
theorem isUnit_of_isSigmaSimple_of_constant {R : Type*} [CommRing R] (D : DifferenceRing R)
    (hsimple : D.IsSigmaSimple) {c : R} (hc : D.σ c = c) (hc0 : c ≠ 0) : IsUnit c := by
  have hdiff : D.IsDifferenceIdeal (Ideal.span {c}) := by
    intro x hx
    rw [Ideal.mem_span_singleton'] at hx ⊢
    obtain ⟨a, rfl⟩ := hx
    exact ⟨D.σ a, by rw [map_mul, hc]⟩
  rcases hsimple _ hdiff with hbot | htop
  · exact absurd (Ideal.span_singleton_eq_bot.mp hbot) hc0
  · exact Ideal.span_singleton_eq_top.mp htop

/-- **Chevalley atom B: the inverse of a constant is a constant.** Over a difference
*field*, if `σ c = c` then `σ (c⁻¹) = (σ c)⁻¹ = c⁻¹`. So the constants are closed under
inverses — the piece that makes `constants` a subfield, and the second input to Chevalley. -/
theorem inv_constant {R : Type*} [Field R] (D : DifferenceRing R) {c : R} (hc : D.σ c = c) :
    D.σ (c⁻¹) = c⁻¹ := by
  rw [map_inv₀, hc]

/-- **The constants form a field.** Over a difference *field* with σ-simple structure,
every nonzero constant is a unit (Chevalley atom A) whose inverse is again a constant
(atom B); hence the constants subring is itself a field. This is the structural input to
"no new constants". -/
@[reducible] noncomputable def constantsField {R : Type*} [Field R] (D : DifferenceRing R) :
    Field ↥(D.constants) :=
  Field.ofIsUnitOrEqZero (fun c => by
    rcases eq_or_ne c 0 with hc0 | hc0
    · exact Or.inr hc0
    · refine Or.inl ?_
      -- c ≠ 0 in the subring; ↑c ≠ 0 in R
      have hcR : (↑c : R) ≠ 0 := by
        simpa using (Subtype.coe_ne_coe.mpr hc0)
      -- the inverse (↑c)⁻¹ is a constant, so it lives in the subring
      have hinv_mem : (↑c : R)⁻¹ ∈ D.constants := by
        rw [mem_constants]
        exact inv_constant D c.2
      -- package the subring inverse
      refine ⟨⟨c, ⟨(↑c : R)⁻¹, hinv_mem⟩, ?_, ?_⟩, rfl⟩
      · apply Subtype.ext
        simp only [Subring.coe_mul, Subring.coe_one]
        exact mul_inv_cancel₀ hcR
      · apply Subtype.ext
        simp only [Subring.coe_mul, Subring.coe_one]
        exact inv_mul_cancel₀ hcR)

/-- **The constants of a σ-simple difference ring form a field.** A nonzero constant `c`
is a unit (Chevalley atom A), and `σ` — being a ring *equivalence* — fixes its inverse
(`σ` maps units to units and `σ c = c`), so `c⁻¹` is again a constant. Hence the constants
subring is a field. This is the version that applies to a Picard–Vessiot ring `R₀` (σ-simple,
but not itself a field) — step 1 toward "no new constants". -/
@[reducible] noncomputable def constantsFieldOfSigmaSimple {R : Type*} [CommRing R]
   [Nontrivial R] (D : DifferenceRing R) (hsimple : D.IsSigmaSimple) : Field ↥(D.constants) :=
  Field.ofIsUnitOrEqZero (fun c => by
    rcases eq_or_ne c 0 with hc0 | hc0
    · exact Or.inr hc0
    · refine Or.inl ?_
      have hcR : (↑c : R) ≠ 0 := fun h => hc0 (Subtype.ext h)
      -- seed A: the nonzero constant ↑c is a unit in R
      obtain ⟨u, hu⟩ := isUnit_of_isSigmaSimple_of_constant D hsimple c.2 hcR
      -- σ fixes the inverse: σ(↑c⁻¹) = (↑c)⁻¹ since σ is a ring equiv fixing ↑c
      have hinv_const : D.σ (↑u⁻¹ : R) = (↑u⁻¹ : R) := by
        have h1 : D.σ (↑u : R) = (↑u : R) := by rw [hu]; exact c.2
        have h2 : D.σ (↑u : R) * D.σ (↑u⁻¹ : R) = 1 := by
          rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
        rw [h1] at h2
        calc D.σ (↑u⁻¹ : R) = (↑u : R) * D.σ (↑u⁻¹ : R) * (↑u⁻¹ : R) := by
              rw [mul_comm (↑u : R), mul_assoc, ← Units.val_mul, mul_inv_cancel,
                  Units.val_one, mul_one]
          _ = (↑u⁻¹ : R) := by rw [h2, one_mul]
      have hinv_mem : (↑u⁻¹ : R) ∈ D.constants := by rw [mem_constants]; exact hinv_const
      refine ⟨⟨c, ⟨(↑u⁻¹ : R), hinv_mem⟩, ?_, ?_⟩, rfl⟩
      · apply Subtype.ext
        simp only [Subring.coe_mul, Subring.coe_one]
        rw [← hu, ← Units.val_mul, mul_inv_cancel, Units.val_one]
      · apply Subtype.ext
        simp only [Subring.coe_mul, Subring.coe_one]
        rw [← hu, ← Units.val_mul, inv_mul_cancel, Units.val_one])

open scoped Classical in
/-- **"No new constants" (Chevalley, vdP–Singer Lemma 1.8).** For a σ-simple, finitely
generated difference-`R`-algebra extension `E / D` with compatible shift and *algebraically
closed* base constants, every constant of `E` is the image of a base constant:
`E^σ = image of D^σ`. This is what makes the difference-Galois group algebraic.

Scaffolded: the ⊇ inclusion (base constants are `E`-constants, from `compat`) is proven; the
⊆ inclusion splits into **(2) algebraicity of `E^σ` over `k`** (the analytic core — `sorry`)
and **(3) alg-closed collapse** (clean). -/
theorem constants_eq_image_of_isAlgClosed
    {R : Type*} [Field R] (D : DifferenceRing R)
    {S : Type*} [CommRing S] [IsDomain S] [Algebra R S] (E : DifferenceRing S)
    (hcompat : ∀ x : R, E.σ (algebraMap R S x) = algebraMap R S (D.σ x))
    (hsimple : E.IsSigmaSimple)
    (hfg : Algebra.FiniteType R S)
    [hkR : Algebra.FiniteType ↥(D.constants) R]
    [inst_ac : @IsAlgClosed ↥(D.constants) (constantsField D)] :
    E.constants = (D.constants).map (algebraMap R S) := by
  apply le_antisymm
  · intro c hc
    letI := constantsField D
    have hIntegral : IsIntegral ↥(D.constants) c := by
      rw [← isAlgebraic_iff_isIntegral]
      by_contra htr
      have htr' : Transcendental ↥(D.constants) c := htr
      -- σ fixes the image of any base constant c₀ in S
      have hfix : ∀ c₀ : ↥(D.constants),
          E.σ (algebraMap ↥(D.constants) S c₀) = algebraMap ↥(D.constants) S c₀ := by
        intro c₀
        rw [IsScalarTower.algebraMap_apply ↥(D.constants) R S c₀]
        rw [hcompat (algebraMap ↥(D.constants) R c₀)]
        congr 1
        exact c₀.2
      -- for every base constant c₀, (c − algebraMap c₀) is invertible in S
      have hinv : ∀ c₀ : ↥(D.constants), IsUnit (c - algebraMap ↥(D.constants) S c₀) := by
        intro c₀
        have hdiff' : E.IsDifferenceIdeal (Ideal.span {c - algebraMap ↥(D.constants) S c₀}) := by
          intro x hx
          rw [Ideal.mem_span_singleton'] at hx ⊢
          obtain ⟨a, rfl⟩ := hx
          refine ⟨E.σ a, ?_⟩
          have hcc : E.σ c = c := hc
          rw [map_mul, map_sub, hcc, hfix c₀]
        rcases hsimple _ hdiff' with hbot | htop
        · -- ⊥ impossible: c − algebraMap c₀ ≠ 0 since c ∉ k
          exfalso
          have hzero : c - algebraMap ↥(D.constants) S c₀ = 0 :=
            Ideal.span_singleton_eq_bot.mp hbot
          have : c = algebraMap ↥(D.constants) S c₀ := by
            rw [← sub_eq_zero]; exact hzero
          exact htr (this ▸ isAlgebraic_algebraMap c₀)
        · exact Ideal.span_singleton_eq_top.mp htop
      -- k[c] = adjoin k {c} is a finite-type k-subalgebra of S (foundation for the Rosenlicht close)
      haveI : Algebra.FiniteType ↥(D.constants) (Algebra.adjoin ↥(D.constants) ({c} : Set S)) :=
        Algebra.FiniteType.adjoin_of_finite (Set.finite_singleton c)
      -- specialization via a maximal quotient S/m; alg-closedness will collapse it to k
      obtain ⟨m, hm⟩ := Ideal.exists_maximal S
      letI : Field (S ⧸ m) := Ideal.Quotient.field m
      haveI : Algebra.FiniteType ↥(D.constants) S := Algebra.FiniteType.trans hkR hfg
      haveI : Algebra.FiniteType ↥(D.constants) (S ⧸ m) :=
        Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ↥(D.constants) m)
          (Ideal.Quotient.mkₐ_surjective ↥(D.constants) m)
      haveI : Module.Finite ↥(D.constants) (S ⧸ m) :=
        finite_of_finite_type_of_isJacobsonRing ↥(D.constants) (S ⧸ m)
      haveI : Algebra.IsIntegral ↥(D.constants) (S ⧸ m) :=
        Algebra.IsIntegral.of_finite ↥(D.constants) (S ⧸ m)
      have hbij : Function.Bijective (algebraMap ↥(D.constants) (S ⧸ m)) :=
        IsAlgClosed.algebraMap_bijective_of_isIntegral
      -- c̄ = mk m c lives in S/m ≅ k, so pull back to c₀ ∈ k
      obtain ⟨c₀, hc₀⟩ := hbij.surjective (Ideal.Quotient.mk m c)
      have hmem : c - algebraMap ↥(D.constants) S c₀ ∈ m := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero, ← hc₀,
            ← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
      have htop : m = ⊤ := Ideal.eq_top_of_isUnit_mem m hmem (hinv c₀)
      exact Ideal.IsMaximal.ne_top hm htop
    obtain ⟨d, hd⟩ : ∃ d : ↥(D.constants), algebraMap ↥(D.constants) S d = c := by
      have hdeg : (minpoly ↥(D.constants) c).degree ≠ 0 :=
        (minpoly.degree_pos hIntegral).ne'
      obtain ⟨d, hd⟩ := IsAlgClosed.exists_root (k := ↥(D.constants))
        (minpoly ↥(D.constants) c) hdeg
      exact ⟨d, minpoly.root hIntegral hd⟩
    exact ⟨(d : R), d.2, by
      rw [← hd, IsScalarTower.algebraMap_apply ↥(D.constants) R S d]
      rfl⟩
  · rintro _ ⟨c₀, hc₀, rfl⟩
    have hc₀' : D.σ c₀ = c₀ := hc₀
    rw [mem_constants, hcompat c₀, hc₀']
end DifferenceRing
