import Mathlib
import DiffGalois.Basic
import DiffGalois.Module
import DiffGalois.Tensor
set_option linter.style.whitespace false
set_option linter.style.longLine false

/-! # Duals of difference modules — toward the rigid structure

The dual of a difference module `(M, Φ_M)` is `M* = Module.Dual R M = M →ₗ[R] R`
with the **contragredient** shift

  Φ_{M*}(φ)  =  σ ∘ φ ∘ Φ_M⁻¹.

The composition is well-typed: `φ ∘ Φ_M⁻¹` is σ⁻¹-semilinear, and post-composing
with `σ` returns an honest R-linear functional, so `Φ_{M*}(φ) ∈ M*`. As a map
`M* → M*` it is σ-semilinear, making `M*` a difference module with the same σ.

Together with the tensor product and unit object (in Tensor.lean), the dual
upgrades the monoidal structure on difference modules to a rigid one — the
Tannakian prerequisite. Built the honest way (Option A: the genuine
contragredient), which is what the Picard–Vessiot / Tannakian references prove.
-/

open scoped TensorProduct

namespace DifferenceModule

variable {R : Type*} [CommRing R] {D : DifferenceRing R}
variable {M : Type*} [AddCommGroup M] [Module R M]

/-- The inverse shift `Φ_M⁻¹`, as a semilinear equivalence.
`F.Φ` is a bijective σ-semilinear map, hence a semilinear equiv; its `.symm`
is the inverse and is what the contragredient composes with. -/
noncomputable def ΦInv (F : DifferenceModule D M) :=
  letI : RingHomInvPair (D.σ : R →+* R) (D.σ.symm : R →+* R) :=
    RingHomInvPair.of_ringEquiv D.σ
  letI : RingHomInvPair (D.σ.symm : R →+* R) (D.σ : R →+* R) :=
    RingHomInvPair.of_ringEquiv_symm D.σ
  (LinearEquiv.ofBijective F.Φ F.bijective).symm

/-- The contragredient action on a single functional: `φ ↦ σ ∘ φ ∘ Φ_M⁻¹`.
Bare function form — testing that the semilinear composition elaborates before
wrapping it in the linear-map / bijectivity structure. -/
noncomputable def contraProbe2 (F : DifferenceModule D M) (φ : Module.Dual R M) :=
  letI : RingHomInvPair (D.σ : R →+* R) (D.σ.symm : R →+* R) :=
    RingHomInvPair.of_ringEquiv D.σ
  letI : RingHomInvPair (D.σ.symm : R →+* R) (D.σ : R →+* R) :=
    RingHomInvPair.of_ringEquiv_symm D.σ
  (unitΦ (D := D)).comp (φ.comp (ΦInv F).toLinearMap)

/-- The contragredient as a σ-semilinear map on the dual: `Φ_{M*}(φ) = σ ∘ φ ∘ Φ_M⁻¹`.
This is the shift making `M* = Dual R M` a difference module. -/
noncomputable def contraMap (F : DifferenceModule D M) :
    Module.Dual R M →ₛₗ[(D.σ : R →+* R)] Module.Dual R M :=
  letI : RingHomInvPair (D.σ : R →+* R) (D.σ.symm : R →+* R) :=
    RingHomInvPair.of_ringEquiv D.σ
  letI : RingHomInvPair (D.σ.symm : R →+* R) (D.σ : R →+* R) :=
    RingHomInvPair.of_ringEquiv_symm D.σ
  { toFun := fun φ => (unitΦ (D := D)).comp (φ.comp (ΦInv F).toLinearMap)
    map_add' := by
      intro φ ψ
      ext m
      simp
    map_smul' := by
      intro a φ
      ext m
      change unitΦ (a * φ (F.ΦInv m)) = D.σ a * unitΦ (φ (F.ΦInv m))
      simp only [unitΦ, LinearMap.coe_mk, AddHom.coe_mk]
      exact map_mul D.σ a (φ (F.ΦInv m)) }

/-- σ⁻¹ as a σ⁻¹-semilinear map on R (the analog of unitΦ for the inverse). -/
def unitΦinv : R →ₛₗ[(D.σ.symm : R →+* R)] R where
  toFun := D.σ.symm
  map_add' := map_add D.σ.symm
  map_smul' := fun a r => by
    simp only [smul_eq_mul, RingHom.coe_coe]
    exact map_mul D.σ.symm a r

/-- The contragredient shift is bijective: its inverse is the contragredient built
from `Φ_M` (rather than `Φ_M⁻¹`). -/
theorem contraMap_bijective (F : DifferenceModule D M) :
    Function.Bijective (contraMap F) := by
  letI : RingHomInvPair (D.σ : R →+* R) (D.σ.symm : R →+* R) :=
    RingHomInvPair.of_ringEquiv D.σ
  letI : RingHomInvPair (D.σ.symm : R →+* R) (D.σ : R →+* R) :=
    RingHomInvPair.of_ringEquiv_symm D.σ
  rw [Function.bijective_iff_has_inverse]
  refine ⟨fun ψ => (unitΦinv (D := D)).comp (ψ.comp F.Φ), ?_, ?_⟩
  · intro φ
    ext m
    change D.σ.symm (D.σ (φ (F.ΦInv (F.Φ m)))) = φ m
    rw [RingEquiv.symm_apply_apply]
    congr 1
    exact (LinearEquiv.ofBijective F.Φ F.bijective).symm_apply_apply m
  · intro ψ
    ext m
    change D.σ (D.σ.symm (ψ (F.Φ (F.ΦInv m)))) = ψ m
    rw [RingEquiv.apply_symm_apply]
    congr 1
    exact (LinearEquiv.ofBijective F.Φ F.bijective).apply_symm_apply m

/-- The dual difference module `M* = (Dual R M, Φ_{M*})` with the contragredient shift.
Together with `tensor` and `unit`, this gives the rigid structure. -/
noncomputable def dual (F : DifferenceModule D M) :
    DifferenceModule D (Module.Dual R M) where
  Φ := contraMap F
  bijective := contraMap_bijective F

#check @DifferenceModule.dual

-- (dual construction goes here, one vertebra at a time)

end DifferenceModule
