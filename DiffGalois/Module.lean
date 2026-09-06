import Mathlib
import DiffGalois.Basic

/-- A difference module over a difference ring `(R, D.σ)`: an `R`-module `M`
equipped with a `σ`-semilinear bijective endomorphism `Φ`. This is exactly a
linear difference equation, coordinate-free — `Φ` is the "shift" acting on
solution space, twisting scalars by `σ`. -/
structure DifferenceModule {R : Type*} [CommRing R] (D : DifferenceRing R)
    (M : Type*) [AddCommGroup M] [Module R M] where
  /-- The semilinear shift map: `Φ (r • m) = σ r • Φ m`. -/
  Φ : M →ₛₗ[(D.σ : R →+* R)] M
  /-- `Φ` is bijective (a difference module's shift is invertible). -/
  bijective : Function.Bijective Φ

namespace DifferenceModule

/-- A morphism of difference modules: an `R`-linear map that commutes with
the shift maps `Φ`. This is the whole content — `f ∘ Φ_M = Φ_N ∘ f` — and it's
what makes difference modules a category, hence what the Galois correspondence
will eventually act on. -/
structure Hom {R : Type*} [CommRing R] {D : DifferenceRing R}
    {M : Type*} [AddCommGroup M] [Module R M]
    {N : Type*} [AddCommGroup N] [Module R N]
    (F : DifferenceModule D M) (G : DifferenceModule D N) where
  /-- The underlying `R`-linear map. -/
  toLinearMap : M →ₗ[R] N
  /-- The map commutes with the shifts: `f (Φ_M m) = Φ_N (f m)`. -/
  comm : ∀ m, toLinearMap (F.Φ m) = G.Φ (toLinearMap m)

namespace Hom

variable {R : Type*} [CommRing R] {D : DifferenceRing R}
  {M : Type*} [AddCommGroup M] [Module R M]
  {N : Type*} [AddCommGroup N] [Module R N]
  {F : DifferenceModule D M} {G : DifferenceModule D N}

/-- Apply a difference-module morphism to an element. -/
instance : FunLike (Hom F G) M N where
  coe f := f.toLinearMap
  coe_injective' := by
    intro f g h
    cases f; cases g
    simp only [DFunLike.coe_fn_eq] at h
    congr

/-- The defining commutation, in applied form. -/
theorem map_Φ (f : Hom F G) (m : M) : f (F.Φ m) = G.Φ (f m) := f.comm m

/-- The identity morphism of difference modules. -/
def id {R : Type*} [CommRing R] {D : DifferenceRing R}
    {M : Type*} [AddCommGroup M] [Module R M]
    (F : DifferenceModule D M) : Hom F F where
  toLinearMap := LinearMap.id
  comm := fun _ => rfl

/-- Composition of difference-module morphisms: the underlying linear maps compose,
and commutation with `Φ` is preserved (`g(f(Φ m)) = g(Φ(f m)) = Φ(g(f m))`). -/
def comp {R : Type*} [CommRing R] {D : DifferenceRing R}
    {M : Type*} [AddCommGroup M] [Module R M]
    {N : Type*} [AddCommGroup N] [Module R N]
    {P : Type*} [AddCommGroup P] [Module R P]
    {F : DifferenceModule D M} {G : DifferenceModule D N} {H : DifferenceModule D P}
    (g : Hom G H) (f : Hom F G) : Hom F H where
  toLinearMap := g.toLinearMap.comp f.toLinearMap
  comm := fun m => by
    simp only [LinearMap.comp_apply]
    rw [f.comm m, g.comm (f.toLinearMap m)]

/-- Two morphisms are equal if their underlying linear maps agree. -/
@[ext] theorem ext {R : Type*} [CommRing R] {D : DifferenceRing R}
    {M : Type*} [AddCommGroup M] [Module R M]
    {N : Type*} [AddCommGroup N] [Module R N]
    {F : DifferenceModule D M} {G : DifferenceModule D N}
    {f g : Hom F G} (h : f.toLinearMap = g.toLinearMap) : f = g := by
  cases f; cases g; congr

/-- Left identity: `id ∘ f = f`. -/
@[simp] theorem id_comp {R : Type*} [CommRing R] {D : DifferenceRing R}
    {M : Type*} [AddCommGroup M] [Module R M]
    {N : Type*} [AddCommGroup N] [Module R N]
    {F : DifferenceModule D M} {G : DifferenceModule D N}
    (f : Hom F G) : comp (id G) f = f := by
  apply ext
  rfl

/-- Right identity: `f ∘ id = f`. -/
@[simp] theorem comp_id {R : Type*} [CommRing R] {D : DifferenceRing R}
    {M : Type*} [AddCommGroup M] [Module R M]
    {N : Type*} [AddCommGroup N] [Module R N]
    {F : DifferenceModule D M} {G : DifferenceModule D N}
    (f : Hom F G) : comp f (id F) = f := by
  apply ext
  rfl

/-- Associativity of composition. -/
theorem comp_assoc {R : Type*} [CommRing R] {D : DifferenceRing R}
    {M : Type*} [AddCommGroup M] [Module R M]
    {N : Type*} [AddCommGroup N] [Module R N]
    {P : Type*} [AddCommGroup P] [Module R P]
    {Q : Type*} [AddCommGroup Q] [Module R Q]
    {F : DifferenceModule D M} {G : DifferenceModule D N}
    {H : DifferenceModule D P} {K : DifferenceModule D Q}
    (h : Hom H K) (g : Hom G H) (f : Hom F G) :
    comp (comp h g) f = comp h (comp g f) := by
  apply ext
  rfl

end Hom

variable {R : Type*} [CommRing R] {D : DifferenceRing R}
  {M : Type*} [AddCommGroup M] [Module R M] (F : DifferenceModule D M)

/-- The defining semilinearity: `Φ` twists scalars by `σ`. -/
theorem Φ_smul (r : R) (m : M) : F.Φ (r • m) = D.σ r • F.Φ m :=
  map_smulₛₗ F.Φ r m

/-- `Φ` preserves addition. -/
theorem Φ_add (m n : M) : F.Φ (m + n) = F.Φ m + F.Φ n :=
  map_add F.Φ m n

/-- A *finite* difference module: a difference module whose underlying `R`-module
is finite and free. This is the object the Galois theory actually applies to —
finiteness is exactly what forces the difference-Galois group to be an *algebraic*
group. Classical difference-Galois (Picard–Vessiot) is the theory of these. -/
structure FiniteDifferenceModule {R : Type*} [CommRing R] (D : DifferenceRing R)
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Free R M]
    extends DifferenceModule D M

namespace FiniteDifferenceModule

variable {R : Type*} [CommRing R] {D : DifferenceRing R}
  {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Free R M]
  (F : FiniteDifferenceModule D M)

/-- The rank of a finite difference module (the dimension of the underlying
free module) — the size of the linear system the module represents. -/
noncomputable def rank : ℕ := Module.finrank R M

/-- The underlying difference module. -/
theorem Φ_smul (r : R) (m : M) : F.Φ (r • m) = D.σ r • F.Φ m :=
  map_smulₛₗ F.Φ r m

end FiniteDifferenceModule

end DifferenceModule
