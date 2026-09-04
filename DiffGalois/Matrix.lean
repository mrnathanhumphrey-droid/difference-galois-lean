import Mathlib
import DiffGalois.Basic
import DiffGalois.Module
set_option linter.style.whitespace false

open DifferenceRing

variable {R : Type*} [CommRing R] (D : DifferenceRing R) {n : ℕ}

/-- Apply the difference automorphism `σ` componentwise to a vector.
This is the ingredient the matrix shift `Φ(v) = A · σ(v)` is built from. -/
def vecσ (v : Fin n → R) : Fin n → R := fun i => D.σ (v i)

/-- `vecσ` is additive. -/
theorem vecσ_add (v w : Fin n → R) : vecσ D (v + w) = vecσ D v + vecσ D w := by
  funext i
  simp only [vecσ, Pi.add_apply, map_add]

/-- `vecσ` twists scalar multiplication by `σ` (semilinearity, componentwise). -/
theorem vecσ_smul (r : R) (v : Fin n → R) :
    vecσ D (r • v) = D.σ r • vecσ D v := by
  funext i
  simp only [vecσ, Pi.smul_apply, smul_eq_mul, map_mul]
/-- The shift map of a matrix difference system: `Φ(v) = A · σ(v)`.
Apply `σ` componentwise, then multiply by the matrix `A`. This is the
concrete linear difference equation `σ(v) = A⁻¹ v` in operator form —
the object your `A_r` towers are instances of. -/
def matrixΦ (A : Matrix (Fin n) (Fin n) R) (v : Fin n → R) : Fin n → R :=
  A.mulVec (vecσ D v)

/-- The matrix shift is additive. -/
theorem matrixΦ_add (A : Matrix (Fin n) (Fin n) R) (v w : Fin n → R) :
    matrixΦ D A (v + w) = matrixΦ D A v + matrixΦ D A w := by
  simp only [matrixΦ, vecσ_add, Matrix.mulVec_add]

/-- The matrix shift twists scalars by `σ` (semilinearity). -/
theorem matrixΦ_smul (A : Matrix (Fin n) (Fin n) R) (r : R) (v : Fin n → R) :
    matrixΦ D A (r • v) = D.σ r • matrixΦ D A v := by
  simp only [matrixΦ, vecσ_smul, Matrix.mulVec_smul]
/-- The inverse shift map, when `A` is invertible: `Φ⁻¹(w) = σ⁻¹(A⁻¹ · w)`.
Undo the matrix, then undo `σ` componentwise. -/
def matrixΦinv (A : Matrix (Fin n) (Fin n) R) [Invertible A] (w : Fin n → R) : Fin n → R :=
  fun i => D.σ.symm ((⅟A).mulVec w i)

/-- The matrix shift is bijective when `A` is invertible. This is what lets a
matrix system become a genuine `DifferenceModule`: invertible matrix + `σ` an
automorphism ⟹ the shift is a bijection of solution space. -/
theorem matrixΦ_bijective (A : Matrix (Fin n) (Fin n) R) [Invertible A] :
    Function.Bijective (matrixΦ D A) := by
  constructor
  · -- injective
    intro v w h
    simp only [matrixΦ] at h
    have h2 : vecσ D v = vecσ D w := by
      have := congrArg ((⅟A).mulVec ·) h
      simpa [Matrix.mulVec_mulVec, invOf_mul_self, Matrix.one_mulVec] using this
    funext i
    have : D.σ (v i) = D.σ (w i) := congrFun h2 i
    exact D.σ.injective this
  · -- surjective
    intro w
    refine ⟨matrixΦinv D A w, ?_⟩
    have hcancel : vecσ D (matrixΦinv D A w) = (⅟A).mulVec w := by
      funext i
      simp only [vecσ, matrixΦinv, RingEquiv.apply_symm_apply]
    simp only [matrixΦ, hcancel, Matrix.mulVec_mulVec, mul_invOf_self, Matrix.one_mulVec]
/-- A matrix system as a difference module. Given an invertible matrix `A` over
a difference ring `(R, σ)`, the shift `Φ(v) = A · σ(v)` makes `Fin n → R` a
difference module. **This is the bridge**: every concrete matrix difference
equation — including the `A_r` truncations of a q-difference tower — is an
instance of the abstract `DifferenceModule` via this construction. -/
noncomputable def matrixToDiffModule (A : Matrix (Fin n) (Fin n) R) [Invertible A] :
    DifferenceModule D (Fin n → R) where
  Φ := ({
      toFun := matrixΦ D A
      map_add' := matrixΦ_add D A
      map_smul' := matrixΦ_smul D A } : (Fin n → R) →ₛₗ[(D.σ : R →+* R)] (Fin n → R))
  bijective := matrixΦ_bijective D A
