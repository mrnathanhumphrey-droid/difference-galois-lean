import Mathlib
import DiffGalois.Basic
import DiffGalois.Module
set_option linter.style.whitespace false
set_option linter.style.longLine false

/-! # Tensor products of difference modules

Making `DifferenceModule` a tensor category — the Floor-2 / Tannakian prerequisite.
The tensor product `M ⊗ N` carries `Φ_{M⊗N} = TensorProduct.map Φ_M Φ_N` (σ-semilinear,
since mathlib's `TensorProduct.map` accepts semilinear maps), with bijectivity from
`TensorProduct.map_bijective`. -/

open scoped TensorProduct

namespace DifferenceModule

variable {R : Type*} [CommRing R] {D : DifferenceRing R}
variable {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- The tensor of the two Φ-maps, as a standalone semilinear map. -/
noncomputable def tensorΦ (F : DifferenceModule D M) (G : DifferenceModule D N) :
    M ⊗[R] N →ₛₗ[(D.σ : R →+* R)] M ⊗[R] N :=
  TensorProduct.map F.Φ G.Φ


theorem tensorΦ_bijective (F : DifferenceModule D M) (G : DifferenceModule D N) :
    Function.Bijective (tensorΦ F G) := by
  obtain ⟨fL, hfL, hfR⟩ := Function.bijective_iff_has_inverse.mp F.bijective
  obtain ⟨gL, hgL, hgR⟩ := Function.bijective_iff_has_inverse.mp G.bijective
  refine ⟨?_, ?_⟩
  · -- injective via left inverse built from the semilinear equivs
    haveI : RingHomInvPair (D.σ : R →+* R) (D.σ.symm : R →+* R) :=
      RingHomInvPair.of_ringEquiv D.σ
    haveI : RingHomInvPair (D.σ.symm : R →+* R) (D.σ : R →+* R) :=
      RingHomInvPair.of_ringEquiv_symm D.σ
    let eF : M ≃ₛₗ[(D.σ : R →+* R)] M := LinearEquiv.ofBijective F.Φ F.bijective
    let eG : N ≃ₛₗ[(D.σ : R →+* R)] N := LinearEquiv.ofBijective G.Φ G.bijective
    have hleft : Function.LeftInverse
        (TensorProduct.map (eF.symm : M →ₛₗ[(D.σ.symm : R →+* R)] M)
                           (eG.symm : N →ₛₗ[(D.σ.symm : R →+* R)] N))
        (tensorΦ F G) := by
      intro x
      induction x with
      | zero => simp
      | tmul m n =>
        rw [tensorΦ, TensorProduct.map_tmul, TensorProduct.map_tmul]
        congr 1
        · exact eF.symm_apply_apply m
        · exact eG.symm_apply_apply n
      | add x y hx hy =>
        simp only [map_add]
        rw [hx, hy]
    exact hleft.injective
  · -- surjective: m ⊗ₜ n is hit by (fL m) ⊗ₜ (gL n)
    intro x
    induction x with
    | zero => exact ⟨0, map_zero _⟩
    | tmul m n =>
      refine ⟨fL m ⊗ₜ gL n, ?_⟩
      rw [tensorΦ, TensorProduct.map_tmul, hfR m, hgR n]
    | add x y hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [map_add, ha, hb]⟩

/-- The tensor product of two difference modules: `Φ_{M⊗N} = Φ_M ⊗ Φ_N`. -/
noncomputable def tensor (F : DifferenceModule D M) (G : DifferenceModule D N) :
    DifferenceModule D (M ⊗[R] N) where
  Φ := tensorΦ F G
  bijective := tensorΦ_bijective F G

/-- The σ-semilinear map on `R` given by `σ` itself: `r ↦ σ r`, semilinear because
`σ (a • r) = σ a • σ r` (which over `R`-as-its-own-module is just `map_mul`). -/
def unitΦ : R →ₛₗ[(D.σ : R →+* R)] R where
  toFun := D.σ
  map_add' := map_add D.σ
  map_smul' := fun a r => by
    simp only [smul_eq_mul, RingHom.coe_coe]
    exact map_mul D.σ a r

/-- The unit difference module `𝟙 = (R, σ)`: the base ring as a module over itself,
with shift `Φ = σ`. This is the tensor identity — `M ⊗ 𝟙 ≅ M`. -/
def unit : DifferenceModule D R where
  Φ := unitΦ
  bijective := D.σ.bijective

#check @DifferenceModule.unit

end DifferenceModule
