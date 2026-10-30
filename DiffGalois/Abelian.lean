import Mathlib
import DiffGalois.Basic
import DiffGalois.Module
set_option linter.style.whitespace false
set_option linter.style.longLine false
set_option linter.style.missingEnd false

/-! # Difference modules form an abelian category — Floor 3, sub-brick 1

The category of difference modules over `(R, σ)` is abelian. We build the abelian
structure **by hand on `DifferenceModule`** (not by transport from `ModuleCat` of a
skew ring), lifting mathlib's underlying `R`-module kernels/cokernels equipped with
the induced shift `Φ`. Keeping one category with native tensor (rigid ⊗, already
built) and native abelian is what makes the monoidal structure exact — the coherence
Tannakian reconstruction will need.

Atom of the whole floor: the shift `Φ` preserves the kernel of a difference-module
morphism (because morphisms commute with `Φ`), so the kernel is a sub-difference-module.
Everything — cokernel, image, the abelian axioms — is built from this and its dual.
-/

open CategoryTheory

namespace DifferenceModule

variable {R : Type*} [CommRing R] {D : DifferenceRing R}
  {M : Type*} [AddCommGroup M] [Module R M]
  {N : Type*} [AddCommGroup N] [Module R N]
  {F : DifferenceModule D M} {G : DifferenceModule D N}

/-- The shift `Φ` preserves the kernel of a difference-module morphism: because `f`
commutes with the shifts, `f (Φ m) = Φ (f m) = Φ 0 = 0` whenever `f m = 0`. This is
the atom of the abelian structure — the kernel is a *sub-difference-module*. -/
theorem Φ_mem_ker (f : Hom F G) {m : M}
    (hm : m ∈ LinearMap.ker f.toLinearMap) :
    F.Φ m ∈ LinearMap.ker f.toLinearMap := by
  rw [LinearMap.mem_ker] at hm ⊢
  rw [f.comm m, hm, map_zero]

/-- The shift `Φ` preserves the range of a difference-module morphism: if `x = f m`,
then `Φ x = Φ (f m) = f (Φ m)` is again in the range. The mirror of `Φ_mem_ker` —
this is what lets `Φ` descend to the cokernel `N ⧸ range f`. -/
theorem Φ_mem_range (f : Hom F G) {x : N}
    (hx : x ∈ LinearMap.range f.toLinearMap) :
    G.Φ x ∈ LinearMap.range f.toLinearMap := by
  rw [LinearMap.mem_range] at hx ⊢
  obtain ⟨m, rfl⟩ := hx
  exact ⟨F.Φ m, f.comm m⟩

/-- The kernel of a difference-module morphism, as a difference module: the submodule
`ker f` with `Φ` restricted to it (well-defined by `Φ_mem_ker`). Bijectivity of the
restricted `Φ` uses that `Φ` preserves `ker` in both directions — surjectivity runs
the commutation backward through `G.Φ` injective. -/
noncomputable def kernel (f : Hom F G) :
    DifferenceModule D (LinearMap.ker f.toLinearMap) where
  Φ := F.Φ.restrict (fun m hm => Φ_mem_ker f hm)
  bijective := by
    constructor
    · -- injective: restriction of the injective F.Φ
      intro x y hxy
      have h : F.Φ (x : M) = F.Φ (y : M) := by
        have hc := congrArg (Subtype.val) hxy
        simpa using hc
      exact Subtype.ext (F.bijective.1 h)
    · -- surjective: preimage of a kernel element is again in the kernel
      rintro ⟨k, hk⟩
      obtain ⟨m, hm⟩ := F.bijective.2 k
      refine ⟨⟨m, ?_⟩, ?_⟩
      · rw [LinearMap.mem_ker]
        apply G.bijective.1
        rw [map_zero, ← f.comm m, hm]
        exact LinearMap.mem_ker.mp hk
      · apply Subtype.ext
        rw [LinearMap.coe_restrict_apply]
        exact hm

/-- The image of a difference-module morphism, as a difference module: the submodule
`range f` with `Φ` (the codomain shift `G.Φ`) restricted to it (well-defined by
`Φ_mem_range`). Bijectivity of the restricted `Φ` uses that `Φ` preserves `range` in
both directions — surjectivity runs the commutation backward through `G.Φ` injective. -/
noncomputable def image (f : Hom F G) :
    DifferenceModule D (LinearMap.range f.toLinearMap) where
  Φ := G.Φ.restrict (fun x hx => Φ_mem_range f hx)
  bijective := by
    constructor
    · -- injective: restriction of the injective G.Φ
      intro x y hxy
      have h : G.Φ (x : N) = G.Φ (y : N) := by
        have hc := congrArg (Subtype.val) hxy
        simpa using hc
      exact Subtype.ext (G.bijective.1 h)
    · -- surjective: preimage of a range element is again in the range
      rintro ⟨x, hx⟩
      rw [LinearMap.mem_range] at hx
      obtain ⟨m, hm⟩ := hx
      obtain ⟨p, hp⟩ := F.bijective.2 m
      have hpre : G.Φ (f.toLinearMap p) = x := by
        rw [← f.comm p, hp, hm]
      have hmem : f.toLinearMap p ∈ LinearMap.range f.toLinearMap :=
        LinearMap.mem_range.mpr ⟨p, rfl⟩
      exact ⟨⟨f.toLinearMap p, hmem⟩, Subtype.ext (by rw [LinearMap.coe_restrict_apply]; exact hpre)⟩

/-- The coimage of a difference-module morphism: the quotient `M ⧸ ker f` with `Φ`
(the domain shift `F.Φ`) descended via `Submodule.mapQ` (well-defined by `Φ_mem_ker`).
The mirror of `cokernel`. Surjectivity is immediate from `F.Φ` surjective; injectivity
needs `Φ` to preserve `ker` backward (run the commutation backward through `G.Φ` injective). -/
noncomputable def coimage (f : Hom F G) :
    DifferenceModule D (M ⧸ LinearMap.ker f.toLinearMap) where
  Φ := (LinearMap.ker f.toLinearMap).mapQ (LinearMap.ker f.toLinearMap) F.Φ
        (by intro z hz; exact Φ_mem_ker f hz)
  bijective := by
    have hback : ∀ z : M, F.Φ z ∈ LinearMap.ker f.toLinearMap →
        z ∈ LinearMap.ker f.toLinearMap := by
      intro z hz
      rw [LinearMap.mem_ker] at hz ⊢
      apply G.bijective.1
      rw [map_zero, ← f.comm z]
      exact hz
    constructor
    · -- injective
      intro a b hab
      obtain ⟨na, rfl⟩ := Submodule.Quotient.mk_surjective (p := LinearMap.ker f.toLinearMap) a
      obtain ⟨nb, rfl⟩ := Submodule.Quotient.mk_surjective (p := LinearMap.ker f.toLinearMap) b
      rw [Submodule.mapQ_apply, Submodule.mapQ_apply, Submodule.Quotient.eq] at hab
      rw [Submodule.Quotient.eq]
      apply hback
      rw [map_sub]
      exact hab
    · -- surjective
      intro y
      obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective (p := LinearMap.ker f.toLinearMap) y
      obtain ⟨m, hm⟩ := F.bijective.2 n
      refine ⟨Submodule.Quotient.mk m, ?_⟩
      rw [Submodule.mapQ_apply, hm]

/-- **First isomorphism theorem for difference modules.** The canonical linear equivalence
`(M ⧸ ker f) ≃ range f` intertwines the shifts of the coimage and the image — i.e. it is an
isomorphism *of difference modules*, not merely of modules. This is the factorization
`coimage f ≅ image f` that makes the category of difference modules abelian in substance. -/
theorem quotKerEquivRange_comm (f : Hom F G) (x : M ⧸ LinearMap.ker f.toLinearMap) :
    f.toLinearMap.quotKerEquivRange ((coimage f).Φ x)
      = (image f).Φ (f.toLinearMap.quotKerEquivRange x) := by
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective (p := LinearMap.ker f.toLinearMap) x
  apply Subtype.ext
  change (f.toLinearMap.quotKerEquivRange ((coimage f).Φ (Submodule.Quotient.mk m)) : N)
     = ((image f).Φ (f.toLinearMap.quotKerEquivRange (Submodule.Quotient.mk m)) : N)
  change (f.toLinearMap.quotKerEquivRange (Submodule.Quotient.mk (F.Φ m)) : N)
     = ((image f).Φ (f.toLinearMap.quotKerEquivRange (Submodule.Quotient.mk m)) : N)
  rw [LinearMap.quotKerEquivRange_apply_mk]
  change f.toLinearMap (F.Φ m)
     = ((G.Φ.restrict (fun x hx => Φ_mem_range f hx))
          (f.toLinearMap.quotKerEquivRange (Submodule.Quotient.mk m)) : N)
  rw [LinearMap.coe_restrict_apply, LinearMap.quotKerEquivRange_apply_mk]
  exact f.comm m
