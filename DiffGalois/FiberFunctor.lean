import Mathlib
import DiffGalois.Basic
import DiffGalois.Module
import DiffGalois.Tensor
set_option linter.style.whitespace false
set_option linter.style.longLine false
set_option linter.style.missingEnd false

/-! # The fiber functor — Floor 4

The fiber functor `ω` sends a difference module to its space of **σ-invariants**
(the "solutions"): `ω(M) = ker(Φ − id) = {m : Φ m = m}`, a module over the ring of
**constants** (the σ-fixed elements). This is the pivot of the theory — the
difference-Galois group is `Aut⊗(ω)`.

Atom of the floor: the σ-invariants of a difference module as a sub-module over the
constants, i.e. `{m : F.Φ m = m}`.
-/

namespace DifferenceModule

variable {R : Type*} [CommRing R] {D : DifferenceRing R}
  {M : Type*} [AddCommGroup M] [Module R M]

/-- The σ-invariants (solutions) of a difference module: the elements fixed by `Φ`.
`ω(M)`, the value of the fiber functor, as a predicate. -/
def IsInvariant (F : DifferenceModule D M) (m : M) : Prop := F.Φ m = m

/-- The invariants are closed under addition. -/
theorem isInvariant_add (F : DifferenceModule D M) {m n : M}
    (hm : F.IsInvariant m) (hn : F.IsInvariant n) : F.IsInvariant (m + n) := by
  unfold IsInvariant at *
  rw [map_add, hm, hn]

/-- Zero is invariant. -/
theorem isInvariant_zero (F : DifferenceModule D M) : F.IsInvariant (0 : M) := by
  unfold IsInvariant
  rw [map_zero]

/-- The invariants are closed under negation. -/
theorem isInvariant_neg (F : DifferenceModule D M) {m : M}
    (hm : F.IsInvariant m) : F.IsInvariant (-m) := by
  unfold IsInvariant at *
  rw [map_neg, hm]

/-- **The key closure: invariants are closed under scaling by constants** (not by all of
`R`). If `Φ m = m` and `σ c = c`, then `Φ (c • m) = σc • Φ m = c • m`. This is *why* the
fiber functor lands in modules over the constants — the invariants feel only the σ-fixed
scalars. -/
theorem isInvariant_const_smul (F : DifferenceModule D M) {c : R} {m : M}
    (hc : D.σ c = c) (hm : F.IsInvariant m) : F.IsInvariant (c • m) := by
  unfold IsInvariant at *
  rw [Φ_smul, hc, hm]
/-- **The fiber functor on objects: `ω(M)`.** The σ-invariants (solutions) of a
difference module, as a submodule over the constants `k = D.constants`. This is the
value of the fiber functor — a `k`-module, built from the closure atoms above. The
difference-Galois group will be defined as the ⊗-automorphisms of this functor. -/
def omega (F : DifferenceModule D M) : Submodule (D.constants) M where
  carrier := {m | F.IsInvariant m}
  add_mem' hm hn := F.isInvariant_add hm hn
  zero_mem' := F.isInvariant_zero
  smul_mem' c _ hm := F.isInvariant_const_smul c.2 hm

/-- Membership in `ω(M)`: `m` is a solution iff `Φ` fixes it. -/
theorem mem_omega (F : DifferenceModule D M) {m : M} :
    m ∈ F.omega ↔ F.Φ m = m := Iff.rfl

/-- A difference-module morphism sends solutions to solutions: if `Φ m = m` then
`G.Φ (f m) = f (F.Φ m) = f m`. This is what lets the fiber functor act on morphisms. -/
theorem isInvariant_map {N : Type*} [AddCommGroup N] [Module R N] {G : DifferenceModule D N}
    (f : Hom F G) {m : M} (hm : F.IsInvariant m) : G.IsInvariant (f.toLinearMap m) := by
  unfold IsInvariant at *
  rw [← f.comm m, hm]

/-- **The fiber functor on morphisms: `ω(f)`.** A difference-module morphism `f`
restricts to a `k`-linear map on the solutions `ω(F) → ω(G)`, `m ↦ f m` (a solution
by `isInvariant_map`). With `omega` on objects, this makes `ω` a functor. -/
def omega_map {R : Type*} [CommRing R] {D : DifferenceRing R}
    {M : Type*} [AddCommGroup M] [Module R M] {F : DifferenceModule D M}
    {N : Type*} [AddCommGroup N] [Module R N] {G : DifferenceModule D N}
    (f : Hom F G) : F.omega →ₗ[↥(D.constants)] G.omega where
  toFun := fun m => ⟨f.toLinearMap (m : M), isInvariant_map f m.2⟩
  map_add' := by
    intro x y
    apply Subtype.ext
    simp only [Submodule.coe_add, map_add]
  map_smul' := by
    intro c x
    apply Subtype.ext
    simp only [SetLike.val_smul, RingHom.id_apply]
    rw [← IsScalarTower.algebraMap_smul R c (x : M),
        ← IsScalarTower.algebraMap_smul R c (f.toLinearMap (x : M)),
        map_smul]

/-- `ω` preserves identities: `ω(id) = id`. -/
@[simp] theorem omega_map_id {R : Type*} [CommRing R] {D : DifferenceRing R}
    {M : Type*} [AddCommGroup M] [Module R M] (F : DifferenceModule D M) :
    omega_map (Hom.id F) = LinearMap.id := by
  ext m
  rfl

/-- `ω` preserves composition: `ω(g ∘ f) = ω(g) ∘ ω(f)`. -/
@[simp] theorem omega_map_comp {R : Type*} [CommRing R] {D : DifferenceRing R}
    {M : Type*} [AddCommGroup M] [Module R M]
    {N : Type*} [AddCommGroup N] [Module R N]
    {P : Type*} [AddCommGroup P] [Module R P]
    {F : DifferenceModule D M} {G : DifferenceModule D N} {H : DifferenceModule D P}
    (g : Hom G H) (f : Hom F G) :
    omega_map (Hom.comp g f) = (omega_map g).comp (omega_map f) := by
  ext m
  rfl

/-- **`ω` preserves injectivity** (`ω` is left-exact, first piece): if a morphism `f` is
injective on the underlying modules, then `ω(f)` is injective on solutions. This is the
restriction-of-an-injection-is-injective move, on the invariant submodule. -/
theorem omega_map_injective {N : Type*} [AddCommGroup N] [Module R N]
    {F : DifferenceModule D M} {G : DifferenceModule D N}
    (f : Hom F G) (hf : Function.Injective f.toLinearMap) :
    Function.Injective (omega_map f) := by
  intro x y hxy
  apply Subtype.ext
  apply hf
  have hc := congrArg (Subtype.val) hxy
  simpa [omega_map] using hc

/-- **`ω` preserves kernels** (left-exactness, direct form): a solution `x` is killed by
`ω(f)` exactly when it lies in the kernel of `f`. So `ker(ω f)` = the solutions inside
`ker f` — this is what it means for the fiber functor to be left-exact. -/
theorem omega_map_eq_zero_iff {N : Type*} [AddCommGroup N] [Module R N]
    {F : DifferenceModule D M} {G : DifferenceModule D N}
    (f : Hom F G) (x : F.omega) :
    omega_map f x = 0 ↔ (↑x : M) ∈ LinearMap.ker f.toLinearMap := by
  rw [Subtype.ext_iff, LinearMap.mem_ker]
  rfl

/-- **Monoidal atom: a tensor of solutions is a solution of the tensor.** If `Φ_F m = m`
and `Φ_G n = n`, then `Φ_{F⊗G}(m ⊗ n) = m ⊗ n`. This is what makes the comparison map
`ω(F) ⊗ ω(G) → ω(F ⊗ G)` well-defined — the monoidal structure of the fiber functor. -/
theorem isInvariant_tmul {N : Type*} [AddCommGroup N] [Module R N]
    (F : DifferenceModule D M) (G : DifferenceModule D N) {m : M} {n : N}
    (hm : F.IsInvariant m) (hn : G.IsInvariant n) :
    (F.tensor G).IsInvariant (m ⊗ₜ[R] n) := by
  unfold IsInvariant at *
  change (F.tensor G).Φ (m ⊗ₜ[R] n) = m ⊗ₜ[R] n
  change (tensorΦ F G) (m ⊗ₜ[R] n) = m ⊗ₜ[R] n
  rw [tensorΦ, TensorProduct.map_tmul, hm, hn]

open scoped TensorProduct in
/-- **The monoidal comparison map: `ω(F) ⊗ ω(G) → ω(F ⊗ G)`.** Sends a tensor of solutions
`m ⊗ n` to the solution `m ⊗ n` of the tensor module (well-defined by `isInvariant_tmul`).
This is the structure map making the fiber functor monoidal. -/
noncomputable def omegaTensorBilin {N : Type*} [AddCommGroup N] [Module R N]
    (F : DifferenceModule D M) (G : DifferenceModule D N) :
    F.omega →ₗ[↥(D.constants)] G.omega →ₗ[↥(D.constants)] (F.tensor G).omega :=
  LinearMap.mk₂ (↥(D.constants))
    (fun m n => ⟨(↑m : M) ⊗ₜ[R] (↑n : N), isInvariant_tmul F G m.2 n.2⟩)
    (fun m₁ m₂ n => by
      apply Subtype.ext
      simp only [Submodule.coe_add]
      rw [TensorProduct.add_tmul])
    (fun c m n => by
      apply Subtype.ext
      simp only [SetLike.val_smul]
      rfl)
    (fun m n₁ n₂ => by
      apply Subtype.ext
      simp only [Submodule.coe_add]
      rw [TensorProduct.tmul_add])
    (fun c m n => by
      apply Subtype.ext
      simp only [SetLike.val_smul]
      exact (TensorProduct.smul_tmul c (↑m : M) (↑n : N)).symm)
