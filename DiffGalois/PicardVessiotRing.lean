import Mathlib
import DiffGalois.Basic
import DiffGalois.Module
import DiffGalois.PicardVessiot
set_option linter.style.whitespace false
set_option linter.style.longLine false
set_option linter.style.missingEnd false

/-! # The universal Picard–Vessiot ring R₀ = k[X_ij, 1/det] — sub-brick 3a

Following vdP–Singer §1.3. Over a difference ring `(R, σ)` with an invertible
system matrix `A ∈ GLₙ`, the universal solution ring is built in three layers:
  (3a) the polynomial ring in n² generic variables  R[X_ij]  — this step
  (3b) the twisted σ:  σ on coefficients, and X ↦ A·X on variables
  (3c) localize away from det(X) so X becomes invertible (a fundamental matrix)

This file, step 3a: R₀' := MvPolynomial (Fin n × Fin n) R, and the generic
matrix `genMatrix` whose (i,j) entry is the variable X_{i,j}.
-/

open MvPolynomial

namespace DifferenceRing

variable {R : Type*} [CommRing R] (D : DifferenceRing R) (n : ℕ)

/-- The polynomial ring over `R` in `n²` generic variables `X_{i,j}`
(indexed by `Fin n × Fin n`) — the base layer of the universal PV ring,
before localizing at the determinant. -/
abbrev PVpoly : Type _ := MvPolynomial (Fin n × Fin n) R

/-- The generic `n × n` matrix over `PVpoly`: its `(i,j)` entry is the
variable `X_{i,j}`. This is the formal fundamental solution matrix. -/
noncomputable def genMatrix : Matrix (Fin n) (Fin n) (PVpoly (R := R) n) :=
  fun i j => X (i, j)

/-- σ acting on coefficients only: the ring equiv on `PVpoly` induced by `D.σ`
on the coefficient ring `R`, fixing every variable `X_{i,j}`. This is the
first (clean) half of the twisted σ; the variable-substitution X ↦ A·X is the
second half. -/
noncomputable def coeffσ : PVpoly (R := R) n ≃+* PVpoly (R := R) n :=
  MvPolynomial.mapEquiv (Fin n × Fin n) D.σ

variable {n} in
/-- The variable-substitution rule for `X ↦ A · X`: the variable `X_{i,j}`
is sent to the `(i,j)` entry of `A · X`, i.e. `∑ₖ C(A i k) · X_{k,j}`.
Here `A` is a matrix over the base ring `R`, entering as constants. -/
noncomputable def substFun (A : Matrix (Fin n) (Fin n) R) :
    (Fin n × Fin n) → PVpoly (R := R) n :=
  fun ij => ∑ k, C (A ij.1 k) * X (k, ij.2)

variable {n} in
/-- The ring endomorphism of `PVpoly` substituting `X ↦ A · X` (each variable
`X_{i,j}` replaced by the `(i,j)` entry of `A · X`). Built as `bind₁` of the
substitution rule; it is an `R`-algebra hom. Invertibility (when `A ∈ GLₙ`) is
proven separately via the inverse substitution `bind₁ (substFun A⁻¹)`. -/
noncomputable def substHom (A : Matrix (Fin n) (Fin n) R) :
    PVpoly (R := R) n →ₐ[R] PVpoly (R := R) n :=
  bind₁ (substFun A)

variable {n} in
/-- Key lemma for invertibility: substituting `X ↦ A·X` then `X ↦ ⅟A·X` returns
each variable to itself. The matrix identity `A · ⅟A = 1` threaded through the
double substitution. -/
theorem substFun_comp_left (A : Matrix (Fin n) (Fin n) R) [Invertible A]
    (ij : Fin n × Fin n) :
    bind₁ (substFun (⅟A)) (substFun A ij) = X ij := by
  simp only [substFun, map_sum]
  simp only [map_mul, bind₁_C_right, bind₁_X_right, substFun]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [← mul_assoc, ← Finset.sum_mul]
  have hAA : ∀ x, (∑ i, C (A ij.1 i) * C (⅟A i x))
      = (C ((1 : Matrix (Fin n) (Fin n) R) ij.1 x) : PVpoly (R := R) n) := by
    intro x
    simp only [← map_mul]
    rw [← map_sum, ← Matrix.mul_apply, mul_invOf_self]
  simp only [hAA]
  rw [Finset.sum_eq_single ij.1]
  · rw [Matrix.one_apply_eq, map_one, one_mul]
  · intro b _ hb
    rw [Matrix.one_apply_ne (Ne.symm hb), map_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ ij.1) h

variable {n} in
/-- Mirror of `substFun_comp_left`: substituting `X ↦ ⅟A·X` then `X ↦ A·X`
also returns each variable to itself (matrix identity `⅟A · A = 1`). -/
theorem substFun_comp_right (A : Matrix (Fin n) (Fin n) R) [Invertible A]
    (ij : Fin n × Fin n) :
    bind₁ (substFun A) (substFun (⅟A) ij) = X ij := by
  simp only [substFun, map_sum]
  simp only [map_mul, bind₁_C_right, bind₁_X_right, substFun]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [← mul_assoc, ← Finset.sum_mul]
  have hAA : ∀ x, (∑ i, C ((⅟A) ij.1 i) * C (A i x))
      = (C ((1 : Matrix (Fin n) (Fin n) R) ij.1 x) : PVpoly (R := R) n) := by
    intro x
    simp only [← map_mul]
    rw [← map_sum, ← Matrix.mul_apply, invOf_mul_self]
  simp only [hAA]
  rw [Finset.sum_eq_single ij.1]
  · rw [Matrix.one_apply_eq, map_one, one_mul]
  · intro b _ hb
    rw [Matrix.one_apply_ne (Ne.symm hb), map_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ ij.1) h

variable {n} in
/-- The substitution `X ↦ A·X` as an `R`-algebra **equivalence** of `PVpoly`,
for invertible `A`. Its inverse is the substitution by `⅟A`; the round-trips
collapse to the identity via `bind₁_bind₁` and the two `substFun_comp` lemmas.
This is the twisted-σ's variable action — the heart of the universal PV ring. -/
noncomputable def substEquiv (A : Matrix (Fin n) (Fin n) R) [Invertible A] :
    PVpoly (R := R) n ≃ₐ[R] PVpoly (R := R) n :=
  AlgEquiv.ofAlgHom (substHom A) (substHom (⅟A))
    (by
      apply MvPolynomial.algHom_ext
      intro ij
      simp only [AlgHom.comp_apply, substHom, AlgHom.coe_id, id_eq]
      rw [bind₁_bind₁, bind₁_X_right]
      exact substFun_comp_right A ij)
    (by
      apply MvPolynomial.algHom_ext
      intro ij
      simp only [AlgHom.comp_apply, substHom, AlgHom.coe_id, id_eq]
      rw [bind₁_bind₁, bind₁_X_right]
      exact substFun_comp_left A ij)

variable {n} in
/-- The full twisted shift σ on `PVpoly`: apply `D.σ` to coefficients, then
substitute `X ↦ A·X`. This is the σ making `PVpoly` (pre-localization) a
difference ring in which the generic matrix `X` is a formal solution of
`σ(X) = A·X`. Composition of `coeffσ` (coefficients) and `substEquiv A`
(variables); the two commute since they act on disjoint data. -/
noncomputable def pvσ (A : Matrix (Fin n) (Fin n) R) [Invertible A] :
    PVpoly (R := R) n ≃+* PVpoly (R := R) n :=
  (coeffσ D n).trans (substEquiv A).toRingEquiv

variable {n} in
/-- The pre-localization coordinate ring `PVpoly = R[X_ij]` as a **difference
ring**, with the twisted shift `pvσ` (σ on coefficients, `X ↦ A·X` on
variables). The generic matrix `X` is the formal fundamental solution. -/
noncomputable def pvDifferenceRing (A : Matrix (Fin n) (Fin n) R) [Invertible A] :
    DifferenceRing (PVpoly (R := R) n) where
  σ := pvσ D A

variable {n} in
/-- The determinant of the generic matrix `X` — the element we localize away
from, so that `X` becomes invertible in the localized ring. -/
noncomputable def genDet : PVpoly (R := R) n :=
  (genMatrix (R := R) n).det

variable {n} in
/-- The universal PV ring `R₀ = R[X_ij, 1/det]`: the localization of `PVpoly`
away from `genDet = det X`. In this ring the generic matrix `X` is invertible,
so it is a genuine fundamental matrix in GLₙ. -/
noncomputable abbrev PVloc : Type _ :=
  Localization.Away (genDet (R := R) (n := n))

variable {n} in
/-- `pvσ` sends `genDet` to an associate of `genDet` (namely `det A · genDet`,
with `det A` a unit), so it preserves the localization. -/
theorem pvσ_genDet_associated (A : Matrix (Fin n) (Fin n) R) [Invertible A] :
    Associated (pvσ D A (genDet (n := n))) (genDet (n := n)) := by
  have hkey : pvσ D A (genDet (n := n)) = C A.det * genDet (n := n) := by
    unfold genDet
    have hmat : (D.pvσ A).mapMatrix (genMatrix (R := R) n)
        = (C.mapMatrix A) * genMatrix (R := R) n := by
      have hX : ∀ p q : Fin n, (D.pvσ A) (X (p, q)) = substFun A (p, q) := by
        intro p q
        simp only [pvσ, RingEquiv.coe_trans, Function.comp_apply,
          coeffσ, mapEquiv_apply, map_X, AlgEquiv.coe_ringEquiv, substEquiv]
        change bind₁ (substFun A) (X (p, q)) = substFun A (p, q)
        rw [bind₁_X_right]
      refine Matrix.ext (fun i j => ?_)
      change (D.pvσ A) (genMatrix (R := R) n i j) = ∑ x, C (A i x) * X (x, j)
      rw [genMatrix, hX]
      simp only [substFun]
    rw [RingEquiv.map_det, hmat, Matrix.det_mul, ← RingHom.map_det]
  have hdetU : IsUnit (A.det) := Matrix.isUnit_det_of_invertible A
  obtain ⟨u, hu⟩ := IsUnit.map (C : R →+* PVpoly (R := R) n) hdetU
  refine (Associated.symm ⟨u, ?_⟩)
  rw [hu, mul_comm, ← hkey]

variable {n} in
/-- `PVloc` is also the localization away from `pvσ genDet` (an associate of
`genDet`), so `pvσ` can be transported through the localization. -/
theorem pvσ_genDet_away (A : Matrix (Fin n) (Fin n) R) [Invertible A] :
    IsLocalization.Away (pvσ D A (genDet (n := n))) (PVloc (R := R) (n := n)) :=
  IsLocalization.Away.of_associated (pvσ_genDet_associated D A).symm

variable {n} in
/-- `pvσ` maps the powers of `genDet` onto the powers of `pvσ genDet` — the
submonoid-image fact that transports the localization through `pvσ`. -/
theorem powers_genDet_map (A : Matrix (Fin n) (Fin n) R) [Invertible A] :
    (Submonoid.powers (genDet (n := n))).map (pvσ D A).toMonoidHom
      = Submonoid.powers (pvσ D A (genDet (n := n))) := by
  simp [Submonoid.map_powers]

variable {n} in
/-- The twisted shift `pvσ` extended to a ring equivalence of the localized ring
`PVloc`. Built from the base equiv `pvσ` via `ringEquivOfRingEquiv`, using that
`pvσ` maps `powers genDet` onto `powers (pvσ genDet)` and that `PVloc` localizes
away from both (they're associates). This is the σ under which the now-invertible
`X` satisfies σ(X) = A·X. -/
noncomputable def pvσLoc (A : Matrix (Fin n) (Fin n) R) [Invertible A] :
    PVloc (R := R) (n := n) ≃+* PVloc (R := R) (n := n) :=
  haveI := pvσ_genDet_away D A
  IsLocalization.ringEquivOfRingEquiv
    (M := Submonoid.powers (genDet (n := n)))
    (T := Submonoid.powers (pvσ D A (genDet (n := n))))
    (PVloc (R := R) (n := n)) (PVloc (R := R) (n := n))
    (pvσ D A) (powers_genDet_map D A)

variable {n} in
/-- The localized ring `PVloc = R[X_ij, 1/det]` as a difference ring, carrying the
extended twisted shift `pvσLoc`. Here `genDet` is inverted, so the generic matrix
`X` is invertible — a genuine fundamental matrix in GLₙ. -/
noncomputable def pvLocDifferenceRing (A : Matrix (Fin n) (Fin n) R) [Invertible A] :
    DifferenceRing (PVloc (R := R) (n := n)) where
  σ := pvσLoc D A

/-- The descended shift `quotσ` acts on residues by `σ`: `quotσ (mk x) = mk (σ x)`.
The bridge that makes a difference ideal of `R/I` pull back to one of `R`. -/
theorem quotσ_mk (I : Ideal R) (h : D.IsDifferenceIdeal I)
    (h' : ∀ x ∈ I, D.σ.symm x ∈ I) (x : R) :
    D.quotσ I h h' (Ideal.Quotient.mk I x) = Ideal.Quotient.mk I (D.σ x) := by
  simp only [quotσ, RingEquiv.ofRingHom_apply, Ideal.quotientMap_mk, RingEquiv.coe_toRingHom]

/-- The preimage under `mk` of a difference ideal of `R/I` is a difference ideal of `R`.
Uses `quotσ_mk` to transport σ-stability across the quotient. -/
theorem isDifferenceIdeal_comap_mk (I : Ideal R) (h : D.IsDifferenceIdeal I)
    (h' : ∀ x ∈ I, D.σ.symm x ∈ I) (J : Ideal (R ⧸ I))
    (hJ : (D.quotientDifferenceRing I h h').IsDifferenceIdeal J) :
    D.IsDifferenceIdeal (J.comap (Ideal.Quotient.mk I)) := by
  intro x hx
  rw [Ideal.mem_comap] at hx ⊢
  rw [← quotσ_mk]
  exact hJ _ hx

/-- The quotient of a difference ring by a MAXIMAL difference ideal is σ-simple
(condition 1 of a Picard–Vessiot ring). A difference ideal `J` of `R/I` pulls back
to a difference ideal of `R` containing `I`; maximality forces it to be `I` (so
`J = ⊥`) or `R` (so `J = ⊤`). -/
theorem isSigmaSimple_quotient_of_maximal (I : Ideal R)
    (h : D.IsDifferenceIdeal I) (h' : ∀ x ∈ I, D.σ.symm x ∈ I)
    (hmax : ∀ J, D.IsDifferenceIdeal J → I < J → J = ⊤)
    (hIne : I ≠ ⊤) :
    (D.quotientDifferenceRing I h h').IsSigmaSimple := by
  refine ⟨?_, ?_⟩
  · apply nontrivial_of_ne (1 : R ⧸ I) 0
    intro hcontra
    rw [← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem] at hcontra
    exact hIne ((Ideal.eq_top_iff_one I).2 hcontra)
  · intro J hJ
    have hdiff : D.IsDifferenceIdeal (J.comap (Ideal.Quotient.mk I)) :=
      isDifferenceIdeal_comap_mk D I h h' J hJ
    have hIJ' : I ≤ J.comap (Ideal.Quotient.mk I) := by
      intro x hx
      simp only [Ideal.mem_comap]
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
      exact J.zero_mem
    have hmapeq : Ideal.map (Ideal.Quotient.mk I) (J.comap (Ideal.Quotient.mk I)) = J :=
      Ideal.map_comap_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective J
    rcases eq_or_lt_of_le hIJ' with heq | hlt
    · left
      rw [← hmapeq, ← heq]
      simp [Ideal.map_quotient_self]
    · right
      rw [← hmapeq, hmax _ hdiff hlt]
      exact Ideal.map_top _

#check @DifferenceRing.isSigmaSimple_quotient_of_maximal

variable {n} in
/-- PVloc-level compatibility: the extended shift `pvσLoc` agrees with `D.σ` on the
image of `R`. Reduces (via `ringEquivOfRingEquiv_eq`) to `pvσ (C x) = C (D.σ x)`. -/
theorem pvσLoc_algebraMap (A : Matrix (Fin n) (Fin n) R) [Invertible A] (x : R) :
    pvσLoc D A (algebraMap R (PVloc (R := R) (n := n)) x)
      = algebraMap R (PVloc (R := R) (n := n)) (D.σ x) := by
  have hpvσC : pvσ D A (C x) = C (D.σ x) := by
    simp only [pvσ, RingEquiv.coe_trans, Function.comp_apply, coeffσ, mapEquiv_apply,
      map_C, AlgEquiv.coe_ringEquiv, substEquiv]
    change bind₁ (substFun A) (C (D.σ x)) = C (D.σ x)
    rw [bind₁_C_right]
  rw [IsScalarTower.algebraMap_apply R (PVpoly (R := R) n) (PVloc (R := R) (n := n)) x,
      IsScalarTower.algebraMap_apply R (PVpoly (R := R) n) (PVloc (R := R) (n := n)) (D.σ x)]
  simp only [MvPolynomial.algebraMap_eq]
  haveI := pvσ_genDet_away D A
  unfold pvσLoc
  rw [IsLocalization.ringEquivOfRingEquiv_eq, hpvσC]

variable {n} in
/-- `pvσLoc` on the image of a variable `X_{p,q}`: the image of `pvσ`'s action on it,
i.e. of `substFun A (p,q) = ∑ₖ C(A p k)·X_{k,q}`. Variable-level companion of
`pvσLoc_algebraMap`. -/
theorem pvσLoc_algebraMap_X (A : Matrix (Fin n) (Fin n) R) [Invertible A] (p q : Fin n) :
    pvσLoc D A (algebraMap (PVpoly (R := R) n) (PVloc (R := R) (n := n)) (X (p, q)))
      = algebraMap (PVpoly (R := R) n) (PVloc (R := R) (n := n))
          (∑ k, C (A p k) * X (k, q)) := by
  have hpvσX : pvσ D A (X (p, q)) = ∑ k, C (A p k) * X (k, q) := by
    simp only [pvσ, RingEquiv.coe_trans, Function.comp_apply, coeffσ, mapEquiv_apply,
      map_X, AlgEquiv.coe_ringEquiv, substEquiv]
    change bind₁ (substFun A) (X (p, q)) = ∑ k, C (A p k) * X (k, q)
    rw [bind₁_X_right]
    simp only [substFun]
  haveI := pvσ_genDet_away D A
  unfold pvσLoc
  rw [IsLocalization.ringEquivOfRingEquiv_eq, hpvσX]

variable {n} in
/-- **Prop 1.20 (Picard–Vessiot existence).** For an invertible `A` over a
difference ring `D` with the universal ring `R[X_ij,1/det]` nontrivial, the quotient
of `PVloc` by a maximal difference ideal is a Picard–Vessiot ring for `σ(Y) = A·Y`. -/
theorem exists_isPicardVessiot (A : Matrix (Fin n) (Fin n) R) [Invertible A]
    (hnt : (⊤ : Ideal (PVloc (R := R) (n := n))) ≠ ⊥) :
    ∃ (I : Ideal (PVloc (R := R) (n := n)))
      (hd : (pvLocDifferenceRing D A).IsDifferenceIdeal I)
      (hd' : ∀ x ∈ I, (pvLocDifferenceRing D A).σ.symm x ∈ I),
      D.IsPicardVessiot ((pvLocDifferenceRing D A).quotientDifferenceRing I hd hd') A := by
  obtain ⟨I, hIdiff, hIne, hImax⟩ :=
    (pvLocDifferenceRing D A).exists_maximal_differenceIdeal hnt
  have hI' : ∀ x ∈ I, (pvLocDifferenceRing D A).σ.symm x ∈ I := by
    have hsub : I ≤ Ideal.comap (pvLocDifferenceRing D A).σ I :=
      fun x hx => Ideal.mem_comap.mpr (hIdiff x hx)
    have hcomap_diff : (pvLocDifferenceRing D A).IsDifferenceIdeal
        (Ideal.comap (pvLocDifferenceRing D A).σ I) :=
      fun x hx => Ideal.mem_comap.mpr (hIdiff _ (Ideal.mem_comap.mp hx))
    have heq : Ideal.comap (pvLocDifferenceRing D A).σ I = I := by
      rcases eq_or_lt_of_le hsub with h | h
      · exact h.symm
      · exfalso
        have htop : Ideal.comap (pvLocDifferenceRing D A).σ I = ⊤ :=
          hImax _ hcomap_diff h
        apply hIne
        rw [Ideal.eq_top_iff_one] at htop ⊢
        rw [Ideal.mem_comap, map_one] at htop
        exact htop
    intro x hx
    have hmem : (pvLocDifferenceRing D A).σ.symm x
        ∈ Ideal.comap (pvLocDifferenceRing D A).σ I :=
      Ideal.mem_comap.mpr (by rw [RingEquiv.apply_symm_apply]; exact hx)
    rwa [heq] at hmem
  refine ⟨I, hIdiff, hI', ?_, ?_, ?_⟩
  · -- compat: reduces (via quotσ_mk) to PVloc-level compatibility `hloc`
    intro x
    have hloc : (pvLocDifferenceRing D A).σ (algebraMap R (PVloc (R := R) (n := n)) x)
        = algebraMap R (PVloc (R := R) (n := n)) (D.σ x) := pvσLoc_algebraMap D A x
    have hAM : ∀ y : R, (algebraMap R (PVloc ⧸ I)) y
        = Ideal.Quotient.mk I (algebraMap R (PVloc (R := R) (n := n)) y) := fun y =>
      IsScalarTower.algebraMap_apply R (PVloc (R := R) (n := n)) (PVloc ⧸ I) y
    rw [hAM, hAM]
    change (pvLocDifferenceRing D A).quotσ I hIdiff hI'
        (Ideal.Quotient.mk I (algebraMap R (PVloc (R := R) (n := n)) x))
      = Ideal.Quotient.mk I (algebraMap R (PVloc (R := R) (n := n)) (D.σ x))
    rw [(pvLocDifferenceRing D A).quotσ_mk I hIdiff hI', hloc]
  · exact isSigmaSimple_quotient_of_maximal (pvLocDifferenceRing D A) I hIdiff hI' hImax hIne
  · -- fundamental: F = generic matrix mapped into the quotient
    set φ : PVpoly (R := R) n →+* (PVloc ⧸ I) :=
      (Ideal.Quotient.mk I).comp (algebraMap (PVpoly (R := R) n) (PVloc (R := R) (n := n)))
      with hφ
    refine ⟨φ.mapMatrix (genMatrix (R := R) n), ?_, ?_, ?_⟩
    · -- (1) IsUnit (det F): genDet inverted in PVloc, units descend through mk
      rw [← RingHom.map_det, hφ, RingHom.comp_apply]
      exact (IsLocalization.Away.algebraMap_isUnit
        (genDet (R := R) (n := n))).map (Ideal.Quotient.mk I)
    · -- (2) F.map σ = A · F : entrywise
      ext p q
      simp only [Matrix.map_apply, RingHom.mapMatrix_apply, genMatrix]
      change (pvLocDifferenceRing D A).quotσ I hIdiff hI'
            (Ideal.Quotient.mk I (algebraMap (PVpoly (R := R) n) (PVloc (R := R) (n := n)) (X (p, q))))
          = (A.map ⇑(algebraMap R (PVloc ⧸ I)) * φ.mapMatrix (genMatrix (R := R) n)) p q
      rw [(pvLocDifferenceRing D A).quotσ_mk I hIdiff hI']
      change (Ideal.Quotient.mk I)
          (pvσLoc D A (algebraMap (PVpoly (R := R) n) (PVloc (R := R) (n := n)) (X (p, q)))) = _
      rw [pvσLoc_algebraMap_X D A p q]
      rw [map_sum (algebraMap (PVpoly (R := R) n) (PVloc (R := R) (n := n))),
          map_sum (Ideal.Quotient.mk I)]
      simp only [map_mul, Matrix.mul_apply, Matrix.map_apply, RingHom.mapMatrix_apply,
        genMatrix]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      congr 1
    · -- (3) adjoin = ⊤: PVloc⧸I generated over R by entries of F and 1/det F
      set φₐ : PVpoly (R := R) n →ₐ[R] (PVloc ⧸ I) :=
        (Ideal.Quotient.mkₐ R I).comp
          (IsScalarTower.toAlgHom R (PVpoly (R := R) n) (PVloc (R := R) (n := n)))
        with hφₐ
      have hφₐφ : ∀ x : PVpoly (R := R) n, φₐ x = φ x := by
        intro x; rw [hφₐ, hφ]; rfl
      have hfold : ∀ x : PVpoly (R := R) n,
          (Ideal.Quotient.mk I)
            (algebraMap (PVpoly (R := R) n) (PVloc (R := R) (n := n)) x) = φ x := by
        intro x; rw [hφ]; rfl
      have hunit : IsUnit (φ.mapMatrix (genMatrix (R := R) n)).det := by
        rw [← RingHom.map_det, hφ, RingHom.comp_apply]
        exact (IsLocalization.Away.algebraMap_isUnit
          (genDet (R := R) (n := n))).map (Ideal.Quotient.mk I)
      have hdgen : φ (genDet (R := R) (n := n))
          = (φ.mapMatrix (genMatrix (R := R) n)).det := by
        simp only [genDet, ← RingHom.map_det]
      set d := (φ.mapMatrix (genMatrix (R := R) n)).det with hd
      have hφmem : ∀ a : PVpoly (R := R) n,
          φ a ∈ Algebra.adjoin R
            ({s | ∃ i j, φ.mapMatrix (genMatrix (R := R) n) i j = s} ∪ {Ring.inverse d}) := by
        intro a
        have hsub : ⇑φₐ '' Set.range (X : (Fin n × Fin n) → PVpoly (R := R) n)
            ⊆ ({s | ∃ i j, φ.mapMatrix (genMatrix (R := R) n) i j = s} ∪ {Ring.inverse d}) := by
          rintro _ ⟨_, ⟨ij, rfl⟩, rfl⟩
          exact Or.inl ⟨ij.1, ij.2, by rw [hφₐφ]; rfl⟩
        have key : φₐ a ∈ Algebra.adjoin R
            (⇑φₐ '' Set.range (X : (Fin n × Fin n) → PVpoly (R := R) n)) := by
          rw [← AlgHom.map_adjoin, MvPolynomial.adjoin_range_X]
          exact Subalgebra.mem_map.mpr ⟨a, Algebra.mem_top, rfl⟩
        have hmono := Algebra.adjoin_mono hsub key
        rwa [hφₐφ] at hmono
      rw [eq_top_iff]
      rintro w -
      obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective w
      obtain ⟨m, a, ha⟩ := IsLocalization.Away.surj (genDet (R := R) (n := n)) z
      have ha' : (Ideal.Quotient.mk I) z * d ^ m = φ a := by
        have h := congrArg (Ideal.Quotient.mk I) ha
        rw [map_mul, map_pow, hfold, hfold] at h
        rw [← hdgen]; exact h
      have hz : (Ideal.Quotient.mk I) z = φ a * (Ring.inverse d) ^ m := by
        have hc : (Ideal.Quotient.mk I) z * d ^ m * (Ring.inverse d) ^ m
            = φ a * (Ring.inverse d) ^ m := by rw [ha']
        rwa [mul_assoc, ← mul_pow, Ring.mul_inverse_cancel d hunit, one_pow, mul_one] at hc
      rw [hz]
      have hinv : Ring.inverse d ∈ Algebra.adjoin R
          ({s | ∃ i j, φ.mapMatrix (genMatrix (R := R) n) i j = s} ∪ {Ring.inverse d}) :=
        Algebra.subset_adjoin (Or.inr rfl)
      exact Subalgebra.mul_mem _ (hφmem a) (Subalgebra.pow_mem _ hinv m)
