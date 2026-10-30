import Mathlib
import DiffGalois.Basic
import DiffGalois.Module
import DiffGalois.Matrix
set_option linter.style.whitespace false
set_option linter.style.longLine false

open RatFunc

/-! # The coboundary criterion (W1)

The wall for the q-difference tower lives here, not in the group objects: it is a
statement about which right-hand sides `σ(ψ) − ψ = target` admit a rational
solution `ψ`. This file generalizes the QDiff2 result `P2_not_coboundary`
(the single case `target = z⁻²`) to the criterion that governs the monomial
model's collapse — the wall as a theorem.

Working over `ℚ(z)` with `σ : z ↦ z³`. The σ-engine below is lifted verbatim
from the green QDiff2.lean (reproduced so this file is self-contained). -/

/-! ## The σ-engine (proven in QDiff2, reproduced verbatim) -/

/-- σ : z ↦ z³, as a ring hom on ℚ(z). -/
noncomputable def σ : RatFunc ℚ →+* RatFunc ℚ :=
  RatFunc.mapRingHom (Polynomial.aeval (Polynomial.X ^ 3 : Polynomial ℚ)).toRingHom (by
    intro p hp
    simp only [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero] at hp ⊢
    intro h
    apply hp
    have hinj : Function.Injective
        (Polynomial.aeval (Polynomial.X ^ 3 : Polynomial ℚ) : Polynomial ℚ →ₐ[ℚ] Polynomial ℚ) := by
      have heq : (Polynomial.aeval (Polynomial.X ^ 3 : Polynomial ℚ) : Polynomial ℚ →ₐ[ℚ] Polynomial ℚ)
          = Polynomial.expand ℚ 3 :=
        Polynomial.algHom_ext (by rw [Polynomial.aeval_X, Polynomial.expand_X])
      rw [heq]
      exact Polynomial.expand_injective (by norm_num)
    exact hinj (by simpa using h))

/-- σ commutes with algebraMap ℚ[X] → ℚ(z), computing to aeval(X³) on the polynomial. -/
lemma σ_algebraMap (p : Polynomial ℚ) :
    σ (algebraMap (Polynomial ℚ) (RatFunc ℚ) p)
      = algebraMap (Polynomial ℚ) (RatFunc ℚ) ((Polynomial.aeval (Polynomial.X ^ 3 : Polynomial ℚ)) p) := by
  unfold σ
  rw [coe_mapRingHom_eq_coe_map,
    show algebraMap (Polynomial ℚ) (RatFunc ℚ) p
        = algebraMap (Polynomial ℚ) (RatFunc ℚ) p / algebraMap (Polynomial ℚ) (RatFunc ℚ) 1 by
      rw [map_one, div_one],
    map_apply_div, map_one, map_one, div_one]
  rfl

/-- THE keystone: σ sends the variable to X³. -/
@[simp] lemma σ_X : σ (X : RatFunc ℚ) = X ^ 3 := by
  rw [show (X : RatFunc ℚ) = algebraMap (Polynomial ℚ) (RatFunc ℚ) Polynomial.X from
      (RatFunc.algebraMap_X (K := ℚ)).symm,
    σ_algebraMap, Polynomial.aeval_X, map_pow, RatFunc.algebraMap_X]

/-- σ fixes constants. -/
@[simp] lemma σ_C (c : ℚ) : σ (RatFunc.C c) = RatFunc.C c := by
  have h : (RatFunc.C c : RatFunc ℚ) = algebraMap (Polynomial ℚ) (RatFunc ℚ) (Polynomial.C c) := rfl
  rw [h, σ_algebraMap, Polynomial.aeval_C, Polynomial.algebraMap_eq]

/-- σ on powers: σ(Xⁿ) = X^(3n). -/
@[simp] lemma σ_X_pow (n : ℕ) : σ ((X : RatFunc ℚ) ^ n) = X ^ (3 * n) := by
  rw [map_pow, σ_X, ← pow_mul]

/-- σ on inverse powers: σ(X⁻ⁿ) = X^(-3n). -/
lemma σ_X_zpow (n : ℤ) : σ ((X : RatFunc ℚ) ^ n) = X ^ (3 * n) := by
  rw [map_zpow₀, σ_X, ← zpow_natCast (X : RatFunc ℚ) 3, ← zpow_mul]
  ring_nf

/-- σ triples the order of vanishing at 0. -/
lemma rootMult_comp_X_pow (p : Polynomial ℚ) (hp : p ≠ 0) :
    Polynomial.rootMultiplicity 0 (p.comp (Polynomial.X ^ 3)) =
    3 * Polynomial.rootMultiplicity 0 p := by
  rw [Polynomial.rootMultiplicity_eq_natTrailingDegree,
      Polynomial.rootMultiplicity_eq_natTrailingDegree]
  simp only [Polynomial.C_0, add_zero, Polynomial.comp_X]
  rw [← Polynomial.expand_eq_comp_X_pow]
  have h3 : (0 : ℕ) < 3 := by norm_num
  apply le_antisymm
  · apply Polynomial.natTrailingDegree_le_of_ne_zero
    rw [Polynomial.coeff_expand_mul' h3]
    exact Polynomial.coeff_natTrailingDegree_ne_zero.mpr hp
  · apply Polynomial.le_natTrailingDegree (Polynomial.expand_ne_zero h3 |>.mpr hp)
    intro m hm
    rw [Polynomial.coeff_expand h3]
    split_ifs with hdvd
    · apply Polynomial.coeff_eq_zero_of_lt_natTrailingDegree
      omega
    · rfl
/-- σ shifts the pole monomials up one level: σ(z^(−2·3^j)) = z^(−2·3^(j+1)). -/
lemma σ_pole_monomial (j : ℕ) :
    σ ((X : RatFunc ℚ) ^ (-2 * 3 ^ j : ℤ)) = (X : RatFunc ℚ) ^ (-2 * 3 ^ (j+1) : ℤ) := by
  rw [σ_X_zpow]
  congr 1
  ring

/-! ## W1 witness, indexed over range n (telescoping-friendly) -/

/-- Partial sums of the coefficients: `S r k = r 0 + ... + r (k-1)` (sum of first k). -/
def partialS (r : ℕ → ℚ) (k : ℕ) : ℚ := ∑ i ∈ Finset.range k, r i

/-- The witness: `ψ = − Σ_{j<n} (partialS r (j+1)) · z^(−2·3^j)`.
Built so that σ(ψ)−ψ telescopes to the target when the total sum vanishes. -/
noncomputable def wPsi (r : ℕ → ℚ) (n : ℕ) : RatFunc ℚ :=
  ∑ j ∈ Finset.range n, RatFunc.C (- partialS r (j+1)) * (X : RatFunc ℚ) ^ (-2 * 3 ^ j : ℤ)

/-- The RHS target: `Σ_{j<n} r j · z^(−2·3^j)`. -/
noncomputable def wTarget (r : ℕ → ℚ) (n : ℕ) : RatFunc ℚ :=
  ∑ j ∈ Finset.range n, RatFunc.C (r j) * (X : RatFunc ℚ) ^ (-2 * 3 ^ j : ℤ)

/-- Adding one term to a partial sum: `partialS r (j+1) = partialS r j + r j`. -/
lemma partialS_succ (r : ℕ → ℚ) (j : ℕ) :
    partialS r (j+1) = partialS r j + r j := by
  unfold partialS
  rw [Finset.sum_range_succ]

/-- σ applied to the witness, with each pole monomial shifted up a level. -/
lemma σ_wPsi (r : ℕ → ℚ) (n : ℕ) :
    σ (wPsi r n)
      = ∑ j ∈ Finset.range n, RatFunc.C (- partialS r (j+1)) * (X : RatFunc ℚ) ^ (-2 * 3 ^ (j+1) : ℤ) := by
  unfold wPsi
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_mul, σ_C, σ_pole_monomial]

/-- σ(ψ) − ψ as a single sum of coefficient times monomial-difference. -/
lemma σ_wPsi_sub (r : ℕ → ℚ) (n : ℕ) :
    σ (wPsi r n) - wPsi r n
      = ∑ j ∈ Finset.range n,
          RatFunc.C (- partialS r (j+1))
            * ((X : RatFunc ℚ) ^ (-2 * 3 ^ (j+1) : ℤ) - (X : RatFunc ℚ) ^ (-2 * 3 ^ j : ℤ)) := by
  rw [σ_wPsi]
  unfold wPsi
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The key identity WITH boundary term (no hypothesis on the sum yet):
`σ(ψ) − ψ = wTarget − (partialS r n)·z^(−2·3^n)`.
Proven by induction; `sum_range_succ` peels one level each step. -/
lemma σ_wPsi_sub_eq (r : ℕ → ℚ) (n : ℕ) :
    σ (wPsi r n) - wPsi r n
      = wTarget r n - RatFunc.C (partialS r n) * (X : RatFunc ℚ) ^ (-2 * 3 ^ n : ℤ) := by
  induction n with
  | zero => simp [wPsi, wTarget, partialS]
  | succ n ih =>
    unfold wPsi wTarget at *
    rw [Finset.sum_range_succ, Finset.sum_range_succ, map_add, map_mul, σ_C, σ_pole_monomial]
    have hps := partialS_succ r n
    have hCneg : ∀ k, RatFunc.C (-partialS r k) = - RatFunc.C (partialS r k) := fun k => map_neg _ _
    have hC : RatFunc.C (partialS r (n+1)) = RatFunc.C (partialS r n) + RatFunc.C (r n) := by
      rw [hps, map_add]
    rw [hC, hCneg (n+1), hC]
    linear_combination ih

/-- W1, easy half: if the coefficients sum to zero, the witness solves the equation.
`σ(ψ) − ψ = Σ_{j<n} r j · z^(−2·3^j)`. -/
theorem W1_of_sum_zero (r : ℕ → ℚ) (n : ℕ) (hsum : partialS r n = 0) :
    σ (wPsi r n) - wPsi r n = wTarget r n := by
  rw [σ_wPsi_sub_eq, hsum, map_zero, zero_mul, sub_zero]

/-! ## W1 — the hard half (solution exists ⟹ Σ = 0) and the full criterion -/

/-- Single-monomial coboundary: `c · z^(−2·3^m)` is a σ-coboundary only if `c = 0`.
This is the P2 pole-order argument, generalized to one monomial (cleaner than P2 —
one pole, no num/denom cross-term). The load-bearing pole lemma for W1's hard half. -/
theorem single_monomial_coboundary (c : ℚ) (m : ℕ)
    (h : ∃ φ : RatFunc ℚ, σ φ - φ = RatFunc.C c * (X : RatFunc ℚ) ^ (-2 * 3 ^ m : ℤ)) :
    c = 0 := by
  induction m generalizing c with
  | zero =>
    obtain ⟨φ, hφ⟩ := h
    by_contra hc
    have hφ0 : φ ≠ 0 := by
      rintro rfl
      simp only [map_zero, sub_zero] at hφ
      apply hc
      have hz : (X : RatFunc ℚ) ^ (-2 * 3 ^ 0 : ℤ) ≠ 0 := zpow_ne_zero _ RatFunc.X_ne_zero
      rw [eq_comm, mul_eq_zero] at hφ
      rcases hφ with hcc | hzz
      · have : (c : ℚ) = 0 := by
          have := RatFunc.C_injective (K := ℚ)
          apply this
          rw [map_zero]; exact hcc
        exact this
      · exact absurd hzz hz
    rw [← RatFunc.num_div_denom φ, map_div₀, σ_algebraMap, σ_algebraMap] at hφ
    set a := φ.num with ha
    set b := φ.denom with hb
    have hbne : b ≠ 0 := RatFunc.denom_ne_zero φ
    have hb0 : (algebraMap (Polynomial ℚ) (RatFunc ℚ) b) ≠ 0 := by simpa using hbne
    have hB0 : (algebraMap (Polynomial ℚ) (RatFunc ℚ) ((Polynomial.aeval (Polynomial.X ^ 3 : Polynomial ℚ)) b)) ≠ 0 := by
      rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (Polynomial ℚ) (RatFunc ℚ))]
      intro hh
      apply hbne
      have hinj : Function.Injective
          (Polynomial.aeval (Polynomial.X ^ 3 : Polynomial ℚ) : Polynomial ℚ →ₐ[ℚ] Polynomial ℚ) := by
        have heq : (Polynomial.aeval (Polynomial.X ^ 3 : Polynomial ℚ) : Polynomial ℚ →ₐ[ℚ] Polynomial ℚ)
            = Polynomial.expand ℚ 3 :=
          Polynomial.algHom_ext (by rw [Polynomial.aeval_X, Polynomial.expand_X])
        rw [heq]; exact Polynomial.expand_injective (by norm_num)
      exact hinj (by simpa using hh)
    rw [div_sub_div _ _ hB0 hb0, div_eq_iff (mul_ne_zero hB0 hb0)] at hφ
    have hmul := congrArg (· * (X : RatFunc ℚ) ^ (2 * 3 ^ 0 : ℤ)) hφ
    simp only at hmul
    have hpole : (X : RatFunc ℚ) ^ (-2 * 3 ^ 0 : ℤ) * (X : RatFunc ℚ) ^ (2 * 3 ^ 0 : ℤ) = 1 := by
      rw [← zpow_add₀ RatFunc.X_ne_zero]; norm_num
    have hrhs : C c * (X : RatFunc ℚ) ^ (-2 * 3 ^ 0 : ℤ) *
          ((algebraMap (Polynomial ℚ) ℚ⟮X⟯) ((Polynomial.aeval (Polynomial.X ^ 3 : Polynomial ℚ)) b) *
            (algebraMap (Polynomial ℚ) ℚ⟮X⟯) b) * (X : RatFunc ℚ) ^ (2 * 3 ^ 0 : ℤ)
        = C c * ((algebraMap (Polynomial ℚ) ℚ⟮X⟯) ((Polynomial.aeval (Polynomial.X ^ 3 : Polynomial ℚ)) b) *
            (algebraMap (Polynomial ℚ) ℚ⟮X⟯) b) := by
      rw [show C c * (X : RatFunc ℚ) ^ (-2 * 3 ^ 0 : ℤ) *
            ((algebraMap (Polynomial ℚ) ℚ⟮X⟯) ((Polynomial.aeval (Polynomial.X ^ 3 : Polynomial ℚ)) b) *
              (algebraMap (Polynomial ℚ) ℚ⟮X⟯) b) * (X : RatFunc ℚ) ^ (2 * 3 ^ 0 : ℤ)
          = C c * ((algebraMap (Polynomial ℚ) ℚ⟮X⟯) ((Polynomial.aeval (Polynomial.X ^ 3 : Polynomial ℚ)) b) *
              (algebraMap (Polynomial ℚ) ℚ⟮X⟯) b) * ((X : RatFunc ℚ) ^ (-2 * 3 ^ 0 : ℤ) * (X : RatFunc ℚ) ^ (2 * 3 ^ 0 : ℤ)) by ring]
      rw [hpole, mul_one]
    rw [hrhs] at hmul
    have hXpow : (X : RatFunc ℚ) ^ (2 * 3 ^ 0 : ℤ)
        = algebraMap (Polynomial ℚ) (RatFunc ℚ) (Polynomial.X ^ (2 * 3 ^ 0)) := by
      rw [map_pow, RatFunc.algebraMap_X, ← zpow_natCast (X : RatFunc ℚ) (2 * 3 ^ 0)]; norm_num
    rw [hXpow] at hmul
    rw [show (C c : RatFunc ℚ) = algebraMap (Polynomial ℚ) (RatFunc ℚ) (Polynomial.C c) from rfl] at hmul
    rw [← map_mul, ← map_mul, ← map_sub, ← map_mul, ← map_mul, ← map_mul,
        (IsFractionRing.injective (Polynomial ℚ) (RatFunc ℚ)).eq_iff] at hmul
    have hcomp : ∀ p : Polynomial ℚ, (Polynomial.aeval (Polynomial.X ^ 3 : Polynomial ℚ)) p = p.comp (Polynomial.X ^ 3) := by
      intro p; simp [Polynomial.aeval_def, Polynomial.comp]
    rw [hcomp, hcomp] at hmul
    have hane : a ≠ 0 := RatFunc.num_ne_zero hφ0
    have hcop : IsCoprime a b := RatFunc.isCoprime_num_denom φ
    have hcne : Polynomial.C c ≠ 0 := by rw [ne_eq, Polynomial.C_eq_zero]; exact hc
    have hAcne : a.comp (Polynomial.X ^ 3) ≠ 0 := by
      rw [← hcomp]; intro hh; apply hane
      have hinj : Function.Injective
          (Polynomial.aeval (Polynomial.X ^ 3 : Polynomial ℚ) : Polynomial ℚ →ₐ[ℚ] Polynomial ℚ) := by
        have heq : (Polynomial.aeval (Polynomial.X ^ 3 : Polynomial ℚ) : Polynomial ℚ →ₐ[ℚ] Polynomial ℚ)
            = Polynomial.expand ℚ 3 :=
          Polynomial.algHom_ext (by rw [Polynomial.aeval_X, Polynomial.expand_X])
        rw [heq]; exact Polynomial.expand_injective (by norm_num)
      exact hinj (by simpa using hh)
    have hBcne : b.comp (Polynomial.X ^ 3) ≠ 0 := by
      rw [← hcomp]; intro hh; apply hbne
      have hinj : Function.Injective
          (Polynomial.aeval (Polynomial.X ^ 3 : Polynomial ℚ) : Polynomial ℚ →ₐ[ℚ] Polynomial ℚ) := by
        have heq : (Polynomial.aeval (Polynomial.X ^ 3 : Polynomial ℚ) : Polynomial ℚ →ₐ[ℚ] Polynomial ℚ)
            = Polynomial.expand ℚ 3 :=
          Polynomial.algHom_ext (by rw [Polynomial.aeval_X, Polynomial.expand_X])
        rw [heq]; exact Polynomial.expand_injective (by norm_num)
      exact hinj (by simpa using hh)
    set s := Polynomial.rootMultiplicity 0 a with hs
    set t := Polynomial.rootMultiplicity 0 b with ht
    have hRHS : Polynomial.rootMultiplicity 0 (Polynomial.C c * (b.comp (Polynomial.X ^ 3) * b)) = 4 * t := by
      rw [Polynomial.rootMultiplicity_mul (mul_ne_zero hcne (mul_ne_zero hBcne hbne)),
          Polynomial.rootMultiplicity_mul (mul_ne_zero hBcne hbne),
          rootMult_comp_X_pow b hbne]
      have hCc : Polynomial.rootMultiplicity 0 (Polynomial.C c) = 0 := by
        rw [Polynomial.rootMultiplicity_eq_zero]
        rw [Polynomial.IsRoot.def, Polynomial.eval_C]; exact hc
      rw [hCc, ← ht]; ring
    have hLHSne : (a.comp (Polynomial.X ^ 3) * b - b.comp (Polynomial.X ^ 3) * a) * Polynomial.X ^ (2 * 3 ^ 0) ≠ 0 := by
      rw [hmul]; exact mul_ne_zero hcne (mul_ne_zero hBcne hbne)
    have hcrossne : a.comp (Polynomial.X ^ 3) * b - b.comp (Polynomial.X ^ 3) * a ≠ 0 := by
      intro hh; rw [hh, zero_mul] at hLHSne; exact hLHSne rfl
    have hLHS : Polynomial.rootMultiplicity 0
        ((a.comp (Polynomial.X ^ 3) * b - b.comp (Polynomial.X ^ 3) * a) * Polynomial.X ^ (2 * 3 ^ 0))
        = Polynomial.rootMultiplicity 0 (a.comp (Polynomial.X ^ 3) * b - b.comp (Polynomial.X ^ 3) * a)
          + 2 * 3 ^ 0 := by
      rw [Polynomial.rootMultiplicity_mul (mul_ne_zero hcrossne (pow_ne_zero _ Polynomial.X_ne_zero))]
      congr 1
      have : Polynomial.rootMultiplicity (0:ℚ) (Polynomial.X ^ (2 * 3 ^ 0)) = 2 * 3 ^ 0 := by
        rw [← Polynomial.count_roots, Polynomial.roots_X_pow]; simp
      exact this
    have hmaster : Polynomial.rootMultiplicity 0 (a.comp (Polynomial.X ^ 3) * b - b.comp (Polynomial.X ^ 3) * a) + 2 * 3 ^ 0 = 4 * t := by
      rw [← hLHS, hmul, hRHS]
    have hmin : s = 0 ∨ t = 0 := by
      by_contra hh
      rw [not_or] at hh
      obtain ⟨hs0, ht0⟩ := hh
      have hXa : (Polynomial.X : Polynomial ℚ) ∣ a := by
        have : a.IsRoot 0 := by rw [← Polynomial.rootMultiplicity_pos hane]; omega
        simpa using (Polynomial.dvd_iff_isRoot (a := (0:ℚ))).mpr this
      have hXb : (Polynomial.X : Polynomial ℚ) ∣ b := by
        have : b.IsRoot 0 := by rw [← Polynomial.rootMultiplicity_pos hbne]; omega
        simpa using (Polynomial.dvd_iff_isRoot (a := (0:ℚ))).mpr this
      have hunit := hcop.isUnit_of_dvd' hXa hXb
      exact Polynomial.not_isUnit_X hunit
    have hAb : Polynomial.rootMultiplicity 0 (a.comp (Polynomial.X ^ 3) * b) = 3 * s + t := by
      rw [Polynomial.rootMultiplicity_mul (mul_ne_zero hAcne hbne), rootMult_comp_X_pow a hane, ← hs, ← ht]
    have hBa : Polynomial.rootMultiplicity 0 (b.comp (Polynomial.X ^ 3) * a) = 3 * t + s := by
      rw [Polynomial.rootMultiplicity_mul (mul_ne_zero hBcne hane), rootMult_comp_X_pow b hbne, ← hs, ← ht]
    have hlow : min (3 * s + t) (3 * t + s) ≤ Polynomial.rootMultiplicity 0 (a.comp (Polynomial.X ^ 3) * b - b.comp (Polynomial.X ^ 3) * a) := by
      have hneg : Polynomial.rootMultiplicity 0 (-(b.comp (Polynomial.X ^ 3) * a)) = 3 * t + s := by
        rw [← Polynomial.count_roots, ← Polynomial.count_roots, Polynomial.roots_neg] at *
        rw [← hBa, Polynomial.count_roots]
      have := Polynomial.rootMultiplicity_add (0:ℚ)
        (p := a.comp (Polynomial.X ^ 3) * b) (q := -(b.comp (Polynomial.X ^ 3) * a)) (by rwa [← sub_eq_add_neg])
      rw [← sub_eq_add_neg, hAb, hneg] at this
      exact this
    have hAb_eq : a.comp (Polynomial.X ^ 3) * b
        = (a.comp (Polynomial.X ^ 3) * b - b.comp (Polynomial.X ^ 3) * a) + b.comp (Polynomial.X ^ 3) * a := by ring
    have hupp : min (Polynomial.rootMultiplicity 0 (a.comp (Polynomial.X ^ 3) * b - b.comp (Polynomial.X ^ 3) * a)) (3 * t + s) ≤ 3 * s + t := by
      have := Polynomial.rootMultiplicity_add (0:ℚ)
        (p := a.comp (Polynomial.X ^ 3) * b - b.comp (Polynomial.X ^ 3) * a)
        (q := b.comp (Polynomial.X ^ 3) * a) (by rw [← hAb_eq]; exact mul_ne_zero hAcne hbne)
      rw [← hAb_eq, hAb, hBa] at this
      exact this
    omega
  | succ m ih =>
    obtain ⟨φ, hφ⟩ := h
    -- RHS = σ(C c · z^(−2·3^m)), since σ triples the exponent and fixes C c.
    have hσg : σ (RatFunc.C c * (X : RatFunc ℚ) ^ (-2 * 3 ^ m : ℤ))
        = RatFunc.C c * (X : RatFunc ℚ) ^ (-2 * 3 ^ (m+1) : ℤ) := by
      rw [map_mul, σ_C, σ_pole_monomial]
    -- φ − g solves the level-m equation with the same coefficient c.
    apply ih c
    refine ⟨φ - RatFunc.C c * (X : RatFunc ℚ) ^ (-2 * 3 ^ m : ℤ), ?_⟩
    rw [map_sub]
    -- σ(φ−g) − (φ−g) = (σφ − φ) − (σg − g) = σg − (σg − g) = g
    rw [hσg] at *
    linear_combination hφ

/-- W1, hard half: if the coboundary equation has ANY rational solution `ψ`,
then the coefficients must sum to zero. This is the pole-order direction —
the generalization of QDiff2's `P2_not_coboundary`. -/
theorem W1_sum_zero_of_solvable (r : ℕ → ℚ) (n : ℕ)
    (h : ∃ ψ : RatFunc ℚ, σ ψ - ψ = wTarget r n) : partialS r n = 0 := by
  obtain ⟨ψ, hψ⟩ := h
  -- ψ − wPsi solves the single-monomial equation with coefficient partialS r n.
  have hkey : σ (ψ - wPsi r n) - (ψ - wPsi r n)
      = RatFunc.C (partialS r n) * (X : RatFunc ℚ) ^ (-2 * 3 ^ n : ℤ) := by
    have he := σ_wPsi_sub_eq r n
    rw [map_sub]
    -- σψ − σ(wPsi) − (ψ − wPsi) = (σψ − ψ) − (σ(wPsi) − wPsi) = wTarget − (wTarget − C(partialS)·z^…)
    linear_combination hψ - he
  exact single_monomial_coboundary (partialS r n) n ⟨ψ - wPsi r n, hkey⟩

/-- **W1 — the coboundary criterion.** The target `Σ_{j<n} r j · z^(−2·3^j)`
is a σ-coboundary if and only if the coefficients sum to zero. This is the
load-bearing stone of the wall: W2 and W3 stand on it. -/
theorem W1 (r : ℕ → ℚ) (n : ℕ) :
    (∃ ψ : RatFunc ℚ, σ ψ - ψ = wTarget r n) ↔ partialS r n = 0 := by
  constructor
  · exact W1_sum_zero_of_solvable r n
  · intro hsum
    exact ⟨wPsi r n, W1_of_sum_zero r n hsum⟩

/-- Pole-order core for the weighted single monomial at level 0. Pure `ℚ[X]`
root multiplicity; a nonzero constant weight `w₀` is invisible to `rootMultiplicity`,
so this is `single_monomial_coboundary`'s zero-case arithmetic with `C w₀ *` threaded in. -/
theorem weighted_pole_core (w₀ c : ℚ) (hw : w₀ ≠ 0) (a b : Polynomial ℚ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hcop : IsCoprime a b)
    (hid : (Polynomial.C w₀ * a.comp (Polynomial.X ^ 3) * b
              - b.comp (Polynomial.X ^ 3) * a) * Polynomial.X ^ (2 * 3 ^ 0)
            = Polynomial.C c * (b.comp (Polynomial.X ^ 3) * b)) :
    c = 0 := by
  by_contra hc
  have hcne : Polynomial.C c ≠ 0 := by rw [ne_eq, Polynomial.C_eq_zero]; exact hc
  have hwne : Polynomial.C w₀ ≠ 0 := by rw [ne_eq, Polynomial.C_eq_zero]; exact hw
  have hexp : (Polynomial.aeval (Polynomial.X ^ 3 : Polynomial ℚ) : Polynomial ℚ →ₐ[ℚ] Polynomial ℚ)
      = Polynomial.expand ℚ 3 :=
    Polynomial.algHom_ext (by rw [Polynomial.aeval_X, Polynomial.expand_X])
  have hinj : Function.Injective
      (Polynomial.aeval (Polynomial.X ^ 3 : Polynomial ℚ) : Polynomial ℚ →ₐ[ℚ] Polynomial ℚ) := by
    rw [hexp]; exact Polynomial.expand_injective (by norm_num)
  have hcompa : (Polynomial.aeval (Polynomial.X ^ 3 : Polynomial ℚ)) a = a.comp (Polynomial.X ^ 3) := by
    simp [Polynomial.aeval_def, Polynomial.comp]
  have hcompb : (Polynomial.aeval (Polynomial.X ^ 3 : Polynomial ℚ)) b = b.comp (Polynomial.X ^ 3) := by
    simp [Polynomial.aeval_def, Polynomial.comp]
  have hAcne : a.comp (Polynomial.X ^ 3) ≠ 0 := fun hh => ha (hinj (by rw [hcompa, hh, map_zero]))
  have hBcne : b.comp (Polynomial.X ^ 3) ≠ 0 := fun hh => hb (hinj (by rw [hcompb, hh, map_zero]))
  set s := Polynomial.rootMultiplicity 0 a with hs
  set t := Polynomial.rootMultiplicity 0 b with ht
  have hCw : Polynomial.rootMultiplicity 0 (Polynomial.C w₀) = 0 := by
    rw [Polynomial.rootMultiplicity_eq_zero]
    rw [Polynomial.IsRoot.def, Polynomial.eval_C]
    exact hw
  have hCc : Polynomial.rootMultiplicity 0 (Polynomial.C c) = 0 := by
    rw [Polynomial.rootMultiplicity_eq_zero]
    rw [Polynomial.IsRoot.def, Polynomial.eval_C]
    exact hc
  have hRHS : Polynomial.rootMultiplicity 0 (Polynomial.C c * (b.comp (Polynomial.X ^ 3) * b)) = 4 * t := by
    rw [Polynomial.rootMultiplicity_mul (mul_ne_zero hcne (mul_ne_zero hBcne hb)),
        Polynomial.rootMultiplicity_mul (mul_ne_zero hBcne hb), rootMult_comp_X_pow b hb, hCc]
    try omega
  have hAb : Polynomial.rootMultiplicity 0 (Polynomial.C w₀ * a.comp (Polynomial.X ^ 3) * b) = 3 * s + t := by
    rw [Polynomial.rootMultiplicity_mul (mul_ne_zero (mul_ne_zero hwne hAcne) hb),
        Polynomial.rootMultiplicity_mul (mul_ne_zero hwne hAcne),
        rootMult_comp_X_pow a ha, hCw]
    try omega
  have hBa : Polynomial.rootMultiplicity 0 (b.comp (Polynomial.X ^ 3) * a) = 3 * t + s := by
    rw [Polynomial.rootMultiplicity_mul (mul_ne_zero hBcne ha), rootMult_comp_X_pow b hb]
    try omega
  have hcrossne : Polynomial.C w₀ * a.comp (Polynomial.X ^ 3) * b - b.comp (Polynomial.X ^ 3) * a ≠ 0 := by
    intro hh; rw [hh, zero_mul] at hid
    exact (mul_ne_zero hcne (mul_ne_zero hBcne hb)) hid.symm
  have hLHS : Polynomial.rootMultiplicity 0
      ((Polynomial.C w₀ * a.comp (Polynomial.X ^ 3) * b - b.comp (Polynomial.X ^ 3) * a)
        * Polynomial.X ^ (2 * 3 ^ 0))
      = Polynomial.rootMultiplicity 0
          (Polynomial.C w₀ * a.comp (Polynomial.X ^ 3) * b - b.comp (Polynomial.X ^ 3) * a) + 2 * 3 ^ 0 := by
    rw [Polynomial.rootMultiplicity_mul (mul_ne_zero hcrossne (pow_ne_zero _ Polynomial.X_ne_zero))]
    congr 1
    have : Polynomial.rootMultiplicity (0:ℚ) (Polynomial.X ^ (2 * 3 ^ 0)) = 2 * 3 ^ 0 := by
      rw [← Polynomial.count_roots, Polynomial.roots_X_pow]; simp
    exact this
  have hmaster : Polynomial.rootMultiplicity 0
      (Polynomial.C w₀ * a.comp (Polynomial.X ^ 3) * b - b.comp (Polynomial.X ^ 3) * a) + 2 * 3 ^ 0 = 4 * t := by
    rw [← hLHS, hid, hRHS]
  have hmin : s = 0 ∨ t = 0 := by
    by_contra hh
    rw [not_or] at hh
    obtain ⟨hs0, ht0⟩ := hh
    have hXa : (Polynomial.X : Polynomial ℚ) ∣ a := by
      have : a.IsRoot 0 := by rw [← Polynomial.rootMultiplicity_pos ha]; omega
      simpa using (Polynomial.dvd_iff_isRoot (a := (0:ℚ))).mpr this
    have hXb : (Polynomial.X : Polynomial ℚ) ∣ b := by
      have : b.IsRoot 0 := by rw [← Polynomial.rootMultiplicity_pos hb]; omega
      simpa using (Polynomial.dvd_iff_isRoot (a := (0:ℚ))).mpr this
    exact Polynomial.not_isUnit_X (hcop.isUnit_of_dvd' hXa hXb)
  have hAb : Polynomial.rootMultiplicity 0 (Polynomial.C w₀ * a.comp (Polynomial.X ^ 3) * b) = 3 * s + t := by
    rw [Polynomial.rootMultiplicity_mul (mul_ne_zero (mul_ne_zero hwne hAcne) hb),
        Polynomial.rootMultiplicity_mul (mul_ne_zero hwne hAcne),
        rootMult_comp_X_pow a ha, hCw]
    omega
  have hBa : Polynomial.rootMultiplicity 0 (b.comp (Polynomial.X ^ 3) * a) = 3 * t + s := by
    rw [Polynomial.rootMultiplicity_mul (mul_ne_zero hBcne ha), rootMult_comp_X_pow b hb]
  have hlow : min (3 * s + t) (3 * t + s)
      ≤ Polynomial.rootMultiplicity 0
          (Polynomial.C w₀ * a.comp (Polynomial.X ^ 3) * b - b.comp (Polynomial.X ^ 3) * a) := by
    have hneg : Polynomial.rootMultiplicity 0 (-(b.comp (Polynomial.X ^ 3) * a)) = 3 * t + s := by
      rw [← Polynomial.count_roots, Polynomial.roots_neg, Polynomial.count_roots, hBa]
    have := Polynomial.rootMultiplicity_add (0:ℚ)
      (p := Polynomial.C w₀ * a.comp (Polynomial.X ^ 3) * b) (q := -(b.comp (Polynomial.X ^ 3) * a))
      (by rw [← sub_eq_add_neg]; exact hcrossne)
    rw [← sub_eq_add_neg, hAb, hneg] at this
    exact this
  have hAb_eq : Polynomial.C w₀ * a.comp (Polynomial.X ^ 3) * b
      = (Polynomial.C w₀ * a.comp (Polynomial.X ^ 3) * b - b.comp (Polynomial.X ^ 3) * a)
        + b.comp (Polynomial.X ^ 3) * a := by ring
  have hupp : min (Polynomial.rootMultiplicity 0
        (Polynomial.C w₀ * a.comp (Polynomial.X ^ 3) * b - b.comp (Polynomial.X ^ 3) * a)) (3 * t + s)
      ≤ 3 * s + t := by
    have := Polynomial.rootMultiplicity_add (0:ℚ)
      (p := Polynomial.C w₀ * a.comp (Polynomial.X ^ 3) * b - b.comp (Polynomial.X ^ 3) * a)
      (q := b.comp (Polynomial.X ^ 3) * a) (by rw [← hAb_eq]; exact mul_ne_zero (mul_ne_zero hwne hAcne) hb)
    rw [← hAb_eq, hAb, hBa] at this
    exact this
  omega
