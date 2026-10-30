import Mathlib
import DiffGalois.Basic
set_option linter.style.longLine false
set_option linter.style.whitespace false

namespace DiffGalois

variable {R : Type*} [CommRing R]

/-- `σ` composed with itself `n` times, bundled. Note `sigmaPow σ 1 = σ`. -/
def sigmaPow (σ : R →+* R) : ℕ → (R →+* R)
  | 0     => RingHom.id R
  | (n+1) => σ.comp (sigmaPow σ n)

@[simp] lemma sigmaPow_zero (σ : R →+* R) : sigmaPow σ 0 = RingHom.id R := rfl

lemma sigmaPow_succ (σ : R →+* R) (n : ℕ) :
    sigmaPow σ (n + 1) = σ.comp (sigmaPow σ n) := rfl

lemma sigmaPow_add (σ : R →+* R) (m n : ℕ) :
    sigmaPow σ (m + n) = (sigmaPow σ m).comp (sigmaPow σ n) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h : m + 1 + n = (m + n) + 1 := by omega
    rw [h, sigmaPow_succ, sigmaPow_succ, ih, RingHom.comp_assoc]

/-- Constant family `n ↦ R` indexing the inversive-closure tower. -/
abbrev InvSys (R : Type*) (_ : ℕ) : Type _ := R

instance (i : ℕ) : CommRing (InvSys R i) := inferInstanceAs (CommRing R)

/-- Transition maps: from level `i` to level `j ≥ i`, apply `σ` exactly `j - i` times. -/
def invMap (σ : R →+* R) (i j : ℕ) (_ : i ≤ j) : InvSys R i →+* InvSys R j :=
  sigmaPow σ (j - i)

/-- Transition maps as a plain function family (the form `Ring.DirectLimit` consumes). -/
abbrev invFun (σ : R →+* R) : ∀ i j : ℕ, i ≤ j → InvSys R i → InvSys R j :=
  fun i j h => (invMap σ i j h : InvSys R i → InvSys R j)

instance invDirectedSystem (σ : R →+* R) :
    DirectedSystem (InvSys R) (invFun σ · · ·) where
  map_self := by
    intro i x
    simp only [invFun, invMap, Nat.sub_self, sigmaPow_zero, RingHom.id_apply]
  map_map := by
    intro k j i hij hjk x
    simp only [invFun, invMap]
    have hexp : (k - j) + (j - i) = k - i := by omega
    rw [← hexp, sigmaPow_add, RingHom.comp_apply]

lemma sigmaPow_one (σ : R →+* R) : sigmaPow σ 1 = σ := by
  change σ.comp (sigmaPow σ 0) = σ
  rw [sigmaPow_zero, RingHom.comp_id]

/-- The inversive closure of `(R, σ)`: the colimit `R →σ R →σ R → ⋯`. -/
abbrev InvClosure (σ : R →+* R) : Type _ :=
  Ring.DirectLimit (InvSys R) (invFun σ · · ·)

/-- Embed level `i` of the tower into the closure. `toClosure σ 0` is the canonical `R ↪ closure`. -/
noncomputable def toClosure (σ : R →+* R) (i : ℕ) : InvSys R i →+* InvClosure σ :=
  Ring.DirectLimit.of (InvSys R) (invFun σ · · ·) i

/-- Transition maps vanish in the closure. -/
lemma toClosure_invFun (σ : R →+* R) {i j : ℕ} (h : i ≤ j) (x : InvSys R i) :
    toClosure σ j (invFun σ i j h x) = toClosure σ i x := by
  simp only [toClosure, Ring.DirectLimit.of_f]

/-- The key one-step relation: at the next level, `σ` collapses to the identity embedding. -/
lemma toClosure_step (σ : R →+* R) (i : ℕ) (x : R) :
    toClosure σ (i + 1) (σ x) = toClosure σ i x := by
  have h := toClosure_invFun σ (Nat.le_succ i) x
  have he : invFun σ i (i + 1) (Nat.le_succ i) x = σ x := by
    simp only [invFun, invMap]
    rw [show i + 1 - i = 1 from by omega, sigmaPow_one]
  rw [he] at h
  exact h

lemma sigmaPow_comm (σ : R →+* R) (n : ℕ) :
    σ.comp (sigmaPow σ n) = (sigmaPow σ n).comp σ := by
  rw [← sigmaPow_succ, sigmaPow_add, sigmaPow_one]

lemma sigma_sigmaPow_apply (σ : R →+* R) (n : ℕ) (x : R) :
    σ (sigmaPow σ n x) = sigmaPow σ n (σ x) := by
  rw [← RingHom.comp_apply, sigmaPow_comm, RingHom.comp_apply]

lemma sigma_invFun (σ : R →+* R) {i j : ℕ} (h : i ≤ j) (x : R) :
    σ (invFun σ i j h x) = invFun σ i j h (σ x) := by
  simp only [invFun, invMap]
  exact sigma_sigmaPow_apply σ (j - i) x

/-- The shift endomorphism on the closure: `σ` acting levelwise. -/
noncomputable def sigmaInf (σ : R →+* R) : InvClosure σ →+* InvClosure σ :=
  Ring.DirectLimit.lift (InvSys R) (invFun σ · · ·) (InvClosure σ)
    (fun i => (toClosure σ i).comp σ)
    (fun i j hij x => by
      simp only [RingHom.comp_apply]
      rw [sigma_invFun σ hij x]
      exact toClosure_invFun σ hij (σ x))

@[simp] lemma sigmaInf_toClosure (σ : R →+* R) (i : ℕ) (x : R) :
    sigmaInf σ (toClosure σ i x) = toClosure σ i (σ x) := by
  unfold sigmaInf toClosure
  rw [Ring.DirectLimit.lift_of]
  rfl

lemma sigmaPow_injective (σ : R →+* R) (hσ : Function.Injective σ) (n : ℕ) :
    Function.Injective (sigmaPow σ n) := by
  induction n with
  | zero => rw [sigmaPow_zero, RingHom.coe_id]; exact Function.injective_id
  | succ n ih => rw [sigmaPow_succ, RingHom.coe_comp]; exact hσ.comp ih

lemma sigmaInf_surjective (σ : R →+* R) : Function.Surjective (sigmaInf σ) := by
  intro z
  obtain ⟨i, x, rfl⟩ := Ring.DirectLimit.exists_of z
  refine ⟨toClosure σ (i + 1) x, ?_⟩
  rw [sigmaInf_toClosure]
  exact toClosure_step σ i x

lemma sigmaInf_injective (σ : R →+* R) (hσ : Function.Injective σ) :
    Function.Injective (sigmaInf σ) := by
  refine (injective_iff_map_eq_zero (sigmaInf σ)).mpr fun z hz => ?_
  obtain ⟨i, x, rfl⟩ := Ring.DirectLimit.exists_of z
  have hz2 : sigmaInf σ (toClosure σ i x) = 0 := hz
  rw [sigmaInf_toClosure] at hz2
  have hz3 : Ring.DirectLimit.of (InvSys R) (invFun σ · · ·) i (σ x) = 0 := hz2
  obtain ⟨j, hij, hj⟩ := Ring.DirectLimit.of.zero_exact hz3
  have hcomm : sigmaPow σ (j - i) (σ x) = 0 := hj
  rw [← sigma_sigmaPow_apply] at hcomm
  have hx0 : sigmaPow σ (j - i) x = 0 := hσ (by rw [hcomm, map_zero])
  have hfin : toClosure σ i x = 0 := by
    rw [← toClosure_invFun σ hij x]
    have hz4 : invFun σ i j hij x = 0 := hx0
    rw [hz4, map_zero]
  exact hfin

lemma sigmaInf_bijective (σ : R →+* R) (hσ : Function.Injective σ) :
    Function.Bijective (sigmaInf σ) :=
  ⟨sigmaInf_injective σ hσ, sigmaInf_surjective σ⟩

/-- `σ` promoted to an automorphism of its inversive closure. -/
noncomputable def sigmaInfEquiv (σ : R →+* R) (hσ : Function.Injective σ) :
    InvClosure σ ≃+* InvClosure σ :=
  RingEquiv.ofBijective (sigmaInf σ) (sigmaInf_bijective σ hσ)

/-- The inversive closure of `(R, σ)` as a genuine difference ring —
`σ` is now a bona-fide automorphism, so the whole difference-algebra
framework applies to it. -/
noncomputable def toDifferenceRing (σ : R →+* R) (hσ : Function.Injective σ) :
    DifferenceRing (InvClosure σ) :=
  { σ := sigmaInfEquiv σ hσ }

end DiffGalois
