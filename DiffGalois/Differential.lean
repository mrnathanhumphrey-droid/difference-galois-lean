import Mathlib
import DiffGalois.Basic
import DiffGalois.Module

set_option linter.style.whitespace false
set_option linter.style.longLine false

/-- A **σδ-ring**: a difference ring `(R, σ)` carrying a derivation `δ` that
commutes with `σ`. Ground floor of the parameterized (differential) theory —
the structure that lets us ask whether a solution satisfies an algebraic
*differential* equation, not just an algebraic one. -/
structure SigmaDeltaRing (R : Type*) [CommRing R] extends DifferenceRing R where
  /-- The derivation. -/
  δ : R → R
  /-- Additivity. -/
  δ_add : ∀ x y, δ (x + y) = δ x + δ y
  /-- The Leibniz (product) rule. -/
  δ_mul : ∀ x y, δ (x * y) = δ x * y + x * δ y
  /-- `σ` and `δ` commute — the Mahler pairing (δ = z·log z·d/dz against σ : z ↦ zᵖ). -/
  commute_σδ : ∀ x, σ (δ x) = δ (σ x)

namespace SigmaDeltaRing

variable {R : Type*} [CommRing R] (D : SigmaDeltaRing R)

/-- A derivation kills `0`. -/
theorem δ_zero : D.δ 0 = 0 := by
  have h := D.δ_add 0 0
  simp only [add_zero] at h
  linear_combination -h

/-- A derivation kills `1`. -/
theorem δ_one : D.δ 1 = 0 := by
  have h := D.δ_mul 1 1
  simp only [mul_one, one_mul] at h
  linear_combination -h

/-- **δ preserves σ-constants.** If `σ` fixes `c`, it fixes `δ c` too:
`σ (δ c) = δ (σ c) = δ c`. This is why the constant field carries its own
derivative — the "differential parameter" of the parameterized theory lives here. -/
theorem δ_constant {c : R} (hc : D.σ c = c) : D.σ (D.δ c) = D.δ c := by
  rw [D.commute_σδ, hc]

/-- Packaged: `δ` maps the constants subring into itself. -/
theorem δ_mem_constants {c : R} (hc : c ∈ D.toDifferenceRing.constants) :
    D.δ c ∈ D.toDifferenceRing.constants := by
  rw [DifferenceRing.mem_constants] at hc ⊢
  exact D.δ_constant hc

end SigmaDeltaRing

/-- A **σδ-module**: a difference module `(M, Φ)` over a σδ-ring that additionally
carries a δ-connection `nabla` — an additive map obeying the δ-Leibniz rule and
commuting with the shift `Φ`. This is the carrier of a *parameterized* linear
difference equation: `Φ` is the equation, `nabla` is the derivative in the
parameter that hypertranscendence is about. `Φ ∘ nabla = nabla ∘ Φ` is consistent
precisely because `σ` and `δ` commute (brick 1). -/
structure SigmaDeltaModule {R : Type*} [CommRing R] (D : SigmaDeltaRing R)
    (M : Type*) [AddCommGroup M] [Module R M]
    extends DifferenceModule D.toDifferenceRing M where
  /-- The δ-connection. -/
  nabla : M → M
  /-- Additivity. -/
  nabla_add : ∀ m n, nabla (m + n) = nabla m + nabla n
  /-- Leibniz: `∇ (r • m) = δr • m + r • ∇ m`. -/
  nabla_leibniz : ∀ (r : R) (m : M), nabla (r • m) = D.δ r • m + r • nabla m
  /-- The connection commutes with the shift. -/
  commute_Φ_nabla : ∀ m, Φ (nabla m) = nabla (Φ m)

namespace SigmaDeltaModule

variable {R : Type*} [CommRing R] {D : SigmaDeltaRing R}
  {M : Type*} [AddCommGroup M] [Module R M] (F : SigmaDeltaModule D M)

/-- The connection kills `0`. -/
theorem nabla_zero : F.nabla 0 = 0 := by
  have h := F.nabla_add 0 0
  rw [add_zero] at h
  have h2 : F.nabla 0 + F.nabla 0 = F.nabla 0 + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel h2

/-- A section is **horizontal** (δ-flat) when the connection kills it: `∇ m = 0`.
These carry no dependence on the differential parameter — the δ-analog of the
Φ-invariants, and exactly what the parameterized Galois group fixes. -/
def IsHorizontal (F : SigmaDeltaModule D M) (m : M) : Prop := F.nabla m = 0

/-- `0` is horizontal. -/
theorem isHorizontal_zero : F.IsHorizontal 0 := F.nabla_zero

/-- Horizontal sections are closed under addition. -/
theorem isHorizontal_add {m n : M} (hm : F.IsHorizontal m) (hn : F.IsHorizontal n) :
    F.IsHorizontal (m + n) := by
  unfold IsHorizontal at *
  rw [F.nabla_add, hm, hn, add_zero]

/-- Horizontal sections are closed under scaling by δ-constants (`δ r = 0`). -/
theorem isHorizontal_smul {r : R} (hr : D.δ r = 0) {m : M} (hm : F.IsHorizontal m) :
    F.IsHorizontal (r • m) := by
  unfold IsHorizontal at *
  rw [F.nabla_leibniz, hr, hm, zero_smul, smul_zero, add_zero]

end SigmaDeltaModule

namespace SigmaDeltaRing

variable {R : Type*} [CommRing R] (D : SigmaDeltaRing R)

/-- The rank-one **shift** `Φ_a : x ↦ a · σ x` — the order-one equation `σ y = a y`. -/
def lineShift (a : Rˣ) (x : R) : R := (a : R) * D.σ x

/-- The rank-one **connection** `∇_b : x ↦ δ x + b · x` — a twisted derivative on the line. -/
def lineNabla (b : R) (x : R) : R := D.δ x + b * x

/-- **Coboundary bridge (algebra core).** On the line, `∇_b = δ + b·` commutes with
`Φ_a = a·σ` for every `x` **iff** the logarithmic-derivative coboundary relation holds:
`a · σ b = δ a + a · b`   (equivalently `σ b − b = δ a / a`).
`⇐` is expansion; `⇒` is evaluation at `x = 1` (where `δ1 = 0`, `σ1 = 1`). -/
theorem lineShift_commute_iff (a : Rˣ) (b : R) :
    (∀ x, D.lineShift a (D.lineNabla b x) = D.lineNabla b (D.lineShift a x))
      ↔ (a : R) * D.σ b = D.δ (a : R) + (a : R) * b := by
  constructor
  · intro h
    have h1 := h 1
    simp only [lineShift, lineNabla, map_one, mul_one, D.δ_one, zero_add] at h1
    linear_combination h1
  · intro hab x
    simp only [lineShift, lineNabla, map_add, map_mul, D.commute_σδ, D.δ_mul]
    linear_combination (D.σ x) * hab

/-- The **logarithmic derivative** of a unit `a`: `δa / a = a⁻¹ · δa`. -/
def dlog (a : Rˣ) : R := (↑a⁻¹ : R) * D.δ (a : R)

/-- The rank-one compatibility relation, rewritten as an **additive σ-coboundary**:
`a·σb = δa + a·b` ⟺ `σ b − b = δa/a`. The right-hand side is exactly the target
shape of the `W1` criterion (`target = dlog a`). -/
theorem line_relation_iff_coboundary (a : Rˣ) (b : R) :
    (a : R) * D.σ b = D.δ (a : R) + (a : R) * b ↔ D.σ b - b = D.dlog a := by
  have hinv : (↑a : R) * (↑a⁻¹ : R) = 1 := a.mul_inv
  have hinv' : (↑a⁻¹ : R) * (↑a : R) = 1 := a.inv_mul
  simp only [dlog]
  constructor
  · intro h
    linear_combination (↑a⁻¹ : R) * h - (D.σ b - b) * hinv'
  · intro h2
    linear_combination (↑a : R) * h2 + D.δ (↑a : R) * hinv

/-- The rank-one equation `σ y = a·y` is **δ-reducible** (the parameter can be
absorbed) when the logarithmic derivative `δa/a` is a σ-coboundary. Its negation
is the hypertranscendence condition. -/
def IsDeltaReducible (a : Rˣ) : Prop := ∃ b : R, D.σ b - b = D.dlog a

/-- **Master equivalence (rank one).** These coincide:
1. `δ`-reducible — `δa/a` is a coboundary (`∃ b, σb − b = δa/a`);
2. some `b` solves the compatibility relation `a·σb = δa + a·b`;
3. some `b` makes the connection `∇_b` commute with the shift `Φ_a` on the whole line. -/
theorem isDeltaReducible_iff (a : Rˣ) :
    D.IsDeltaReducible a
      ↔ ∃ b : R, ∀ x, D.lineShift a (D.lineNabla b x) = D.lineNabla b (D.lineShift a x) := by
  unfold IsDeltaReducible
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, (D.lineShift_commute_iff a b).mpr ((D.line_relation_iff_coboundary a b).mpr hb)⟩
  · rintro ⟨b, hb⟩
    exact ⟨b, (D.line_relation_iff_coboundary a b).mp ((D.lineShift_commute_iff a b).mp hb)⟩

/-- The rank-one equation `σ y = a·y` is **δ-transcendental (hypertranscendental)**
when it is *not* δ-reducible: `δa/a` is not a σ-coboundary, so no rational connection
absorbs the parameter. The order-one summit condition (DHR Prop 3.1). -/
def IsDeltaTranscendental (a : Rˣ) : Prop := ¬ D.IsDeltaReducible a

/-- Unpacked: no `b` trivialises the logarithmic derivative. -/
theorem isDeltaTranscendental_iff (a : Rˣ) :
    D.IsDeltaTranscendental a ↔ ∀ b : R, D.σ b - b ≠ D.dlog a := by
  simp only [IsDeltaTranscendental, IsDeltaReducible, not_exists]

/-- `Φ_a` is additive. -/
theorem lineShift_add (a : Rˣ) (x y : R) :
    D.lineShift a (x + y) = D.lineShift a x + D.lineShift a y := by
  simp only [lineShift, map_add, mul_add]

/-- `Φ_a` is σ-semilinear. -/
theorem lineShift_smul (a : Rˣ) (r x : R) :
    D.lineShift a (r • x) = D.σ r • D.lineShift a x := by
  simp only [lineShift, smul_eq_mul, map_mul]; ring

/-- `Φ_a` is bijective (`a` a unit, `σ` an automorphism). -/
theorem lineShift_bijective (a : Rˣ) : Function.Bijective (D.lineShift a) := by
  constructor
  · intro x y h
    have h' : (a : R) * D.σ x = (a : R) * D.σ y := h
    have h2 : D.σ x = D.σ y := by
      have h3 := congrArg (fun t => (↑a⁻¹ : R) * t) h'
      simp only [← mul_assoc, a.inv_mul, one_mul] at h3
      exact h3
    exact D.σ.injective h2
  · intro y
    refine ⟨D.σ.symm ((↑a⁻¹ : R) * y), ?_⟩
    change (a : R) * D.σ (D.σ.symm ((↑a⁻¹ : R) * y)) = y
    rw [RingEquiv.apply_symm_apply, ← mul_assoc, a.mul_inv, one_mul]

/-- The rank-one **difference module** for `σ y = a·y` (shift `Φ_a = a·σ`). -/
noncomputable def lineDiffModule (a : Rˣ) : DifferenceModule D.toDifferenceRing R where
  Φ := ({ toFun := D.lineShift a
          map_add' := D.lineShift_add a
          map_smul' := D.lineShift_smul a } : R →ₛₗ[(D.toDifferenceRing.σ : R →+* R)] R)
  bijective := D.lineShift_bijective a

/-- **Inhabiting the tower.** A compatible datum `(a, b)` — i.e. `a·σb = δa + a·b`,
the reducibility relation — makes the line `R` a genuine σδ-module: shift `Φ_a = a·σ`,
connection `∇_b = δ + b·`. The reducibility witness `b` literally builds the module,
so bricks 1–7 are not vacuous. -/
noncomputable def lineModule (a : Rˣ) (b : R)
    (hab : (a : R) * D.σ b = D.δ (a : R) + (a : R) * b) :
    SigmaDeltaModule D R where
  toDifferenceModule := D.lineDiffModule a
  nabla := D.lineNabla b
  nabla_add := fun x y => by simp only [lineNabla, D.δ_add]; ring
  nabla_leibniz := fun r x => by simp only [lineNabla, smul_eq_mul, D.δ_mul]; ring
  commute_Φ_nabla := fun x => by
    change D.lineShift a (D.lineNabla b x) = D.lineNabla b (D.lineShift a x)
    exact (D.lineShift_commute_iff a b).mpr hab x

end SigmaDeltaRing
