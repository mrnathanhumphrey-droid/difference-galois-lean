import Mathlib          -- start broad; trim later
set_option linter.style.whitespace false
set_option linter.style.longLine false

open RatFunc

-- All declarations in this worked example live in the `QDiff2` namespace so that its
-- local `σ` (and the shared helper lemmas) coexist with the general criterion in
-- `DiffGalois.Coboundary`.
namespace QDiff2

/-! ============================================================
    TIER 0 — the keystone. σ and how it acts on the variable.
    All plumbing (RatFunc coercion). Close against LIVE library.
    Everything below cites these.
    ============================================================ -/

-- σ : z ↦ z³, as a ring hom on ℚ(z).
noncomputable def σ : RatFunc ℚ →+* RatFunc ℚ :=
  RatFunc.mapRingHom (Polynomial.aeval (Polynomial.X ^ 3 : Polynomial ℚ)).toRingHom (by
    intro p hp
    simp only [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero] at hp ⊢
    intro h
    apply hp
    have hinj : Function.Injective
        (Polynomial.aeval (Polynomial.X ^ 3 : Polynomial ℚ) : Polynomial ℚ →ₐ[ℚ] Polynomial ℚ) := by
      -- aeval(X³) = expand ℚ 3 (both send X ↦ X³, and AlgHoms out of ℚ[X] are determined on X),
      -- and expand ℚ n is injective for 0 < n.
      have heq : (Polynomial.aeval (Polynomial.X ^ 3 : Polynomial ℚ) : Polynomial ℚ →ₐ[ℚ] Polynomial ℚ)
          = Polynomial.expand ℚ 3 :=
        Polynomial.algHom_ext (by rw [Polynomial.aeval_X, Polynomial.expand_X])
      rw [heq]
      exact Polynomial.expand_injective (by norm_num)
    exact hinj (by simpa using h))

-- helper: σ commutes with algebraMap ℚ[X] → ℚ(z), computing to aeval(X³) on the polynomial.
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

-- THE keystone lemma. σ sends the variable to X³. Everything cites this.
@[simp] lemma σ_X : σ (X : RatFunc ℚ) = X ^ 3 := by
  rw [show (X : RatFunc ℚ) = algebraMap (Polynomial ℚ) (RatFunc ℚ) Polynomial.X from
      (RatFunc.algebraMap_X (K := ℚ)).symm,
    σ_algebraMap, Polynomial.aeval_X, map_pow, RatFunc.algebraMap_X]

-- σ fixes constants (needed for P2's pole argument).
@[simp] lemma σ_C (c : ℚ) : σ (RatFunc.C c) = RatFunc.C c := by
  have h : (RatFunc.C c : RatFunc ℚ) = algebraMap (Polynomial ℚ) (RatFunc ℚ) (Polynomial.C c) := rfl
  rw [h, σ_algebraMap, Polynomial.aeval_C, Polynomial.algebraMap_eq]

/-! ============================================================
    TIER 1 — computational consequences of σ_X.
    Should fall by rw [σ_X] + map lemmas once Tier 0 is green.
    Mostly easy.
    ============================================================ -/

-- σ on powers: σ(Xⁿ) = X^(3n).
@[simp] lemma σ_X_pow (n : ℕ) : σ ((X : RatFunc ℚ) ^ n) = X ^ (3 * n) := by
  rw [map_pow, σ_X, ← pow_mul]

-- σ on inverse powers: σ(X⁻ⁿ) = X^(-3n).  Needed for P2 (z⁻² lives here).
lemma σ_X_zpow (n : ℤ) : σ ((X : RatFunc ℚ) ^ n) = X ^ (3 * n) := by
  rw [map_zpow₀, σ_X, ← zpow_natCast (X : RatFunc ℚ) 3, ← zpow_mul]
  ring_nf

/-! ============================================================
    TIER 2 — the Rung-3 CONTENT. The two coboundary facts.
    P1 trivial once Tier 1. P2 is the REAL proof (you + me).
    ============================================================ -/

-- P1: the diagonal is a coboundary — σ(y) = z⁴·y has a rational solution (y = z²).
theorem P1_coboundary : ∃ y : RatFunc ℚ, σ y = X ^ 4 * y := by
  refine ⟨X ^ 2, ?_⟩
  rw [map_pow, σ_X]
  ring

-- σ triples the order of vanishing at 0: composing with X³ triples rootMultiplicity at 0.
lemma rootMult_comp_X_pow (p : Polynomial ℚ) (hp : p ≠ 0) :
    Polynomial.rootMultiplicity 0 (p.comp (Polynomial.X ^ 3)) =
    3 * Polynomial.rootMultiplicity 0 p := by
  rw [Polynomial.rootMultiplicity_eq_natTrailingDegree,
      Polynomial.rootMultiplicity_eq_natTrailingDegree]
  simp only [Polynomial.C_0, add_zero, Polynomial.comp_X]
  rw [← Polynomial.expand_eq_comp_X_pow]
  have h3 : (0 : ℕ) < 3 := by norm_num
  apply le_antisymm
  · -- trailing degree ≤ 3t: the coeff at 3t is nonzero
    apply Polynomial.natTrailingDegree_le_of_ne_zero
    rw [Polynomial.coeff_expand_mul' h3]
    exact Polynomial.coeff_natTrailingDegree_ne_zero.mpr hp
  · -- 3t ≤ trailing degree: all coeffs below 3t vanish
    apply Polynomial.le_natTrailingDegree (Polynomial.expand_ne_zero h3 |>.mpr hp)
    intro m hm
    rw [Polynomial.coeff_expand h3]
    split_ifs with hdvd
    · apply Polynomial.coeff_eq_zero_of_lt_natTrailingDegree
      omega
    · rfl



-- P2: the off-diagonal is NOT a coboundary — σ(ψ) − ψ = z⁻² has no rational solution.
theorem P2_not_coboundary : ¬ ∃ ψ : RatFunc ℚ, σ ψ - ψ = X⁻¹ ^ 2 := by
  rintro ⟨ψ, hψ⟩
  -- ψ ≠ 0, since σψ - ψ = X⁻² ≠ 0
  have hψ0 : ψ ≠ 0 := by
    rintro rfl
    simp at hψ
    exact pow_ne_zero 2 RatFunc.X_ne_zero hψ.symm
  have key : X ^ 2 * σ ψ - X ^ 2 * ψ = 1 := by
    rw [← mul_sub, hψ]
    rw [← mul_pow]
    rw [mul_inv_cancel₀ RatFunc.X_ne_zero, one_pow]
  rw [← RatFunc.num_div_denom ψ] at key
  rw [map_div₀, σ_algebraMap, σ_algebraMap] at key
  have hb : (algebraMap (Polynomial ℚ) (RatFunc ℚ) ψ.denom) ≠ 0 := by
      simpa using RatFunc.denom_ne_zero ψ
  have hB : (algebraMap (Polynomial ℚ) (RatFunc ℚ) ((Polynomial.aeval (Polynomial.X ^ 3 : Polynomial ℚ)) ψ.denom)) ≠ 0 := by
      have hinj : Function.Injective
          (Polynomial.aeval (Polynomial.X ^ 3 : Polynomial ℚ) : Polynomial ℚ →ₐ[ℚ] Polynomial ℚ) := by
        have heq : (Polynomial.aeval (Polynomial.X ^ 3 : Polynomial ℚ) : Polynomial ℚ →ₐ[ℚ] Polynomial ℚ)
            = Polynomial.expand ℚ 3 :=
          Polynomial.algHom_ext (by rw [Polynomial.aeval_X, Polynomial.expand_X])
        rw [heq]
        exact Polynomial.expand_injective (by norm_num)
      have h1 : (Polynomial.aeval (Polynomial.X ^ 3 : Polynomial ℚ)) ψ.denom ≠ 0 := by
        intro h
        exact RatFunc.denom_ne_zero ψ (hinj (by simpa using h))
      simp only [ne_eq, map_eq_zero_iff (algebraMap (Polynomial ℚ) (RatFunc ℚ))
        (IsFractionRing.injective (Polynomial ℚ) (RatFunc ℚ))]
      exact h1
  field_simp [hb, hB] at key
  rw [show (X : RatFunc ℚ) ^ 2 = algebraMap (Polynomial ℚ) (RatFunc ℚ) (Polynomial.X ^ 2) by
    rw [map_pow, RatFunc.algebraMap_X]] at key
  rw [← map_mul, ← map_mul, ← map_sub, ← map_mul, ← map_mul] at key
  rw [(IsFractionRing.injective (Polynomial ℚ) (RatFunc ℚ)).eq_iff] at key
  set a := ψ.num with ha
  set b := ψ.denom with hb'
  have hcop : IsCoprime a b := RatFunc.isCoprime_num_denom ψ
  have hbne : b ≠ 0 := RatFunc.denom_ne_zero ψ
  have hB0 : (Polynomial.aeval (Polynomial.X ^ 3 : Polynomial ℚ)) b ≠ 0 := by
    intro h
    apply hbne
    have hinj : Function.Injective
        (Polynomial.aeval (Polynomial.X ^ 3 : Polynomial ℚ) : Polynomial ℚ →ₐ[ℚ] Polynomial ℚ) := by
      have heq : (Polynomial.aeval (Polynomial.X ^ 3 : Polynomial ℚ) : Polynomial ℚ →ₐ[ℚ] Polynomial ℚ)
          = Polynomial.expand ℚ 3 :=
        Polynomial.algHom_ext (by rw [Polynomial.aeval_X, Polynomial.expand_X])
      rw [heq]; exact Polynomial.expand_injective (by norm_num)
    exact hinj (by simpa using h)
  have hcomp : ∀ p : Polynomial ℚ, (Polynomial.aeval (Polynomial.X ^ 3 : Polynomial ℚ)) p = p.comp (Polynomial.X ^ 3) := by
    intro p
    simp [Polynomial.aeval_def, Polynomial.comp]
  rw [hcomp, hcomp] at key
  have hRHS : Polynomial.rootMultiplicity 0 (b.comp (Polynomial.X ^ 3) * b)
      = 4 * Polynomial.rootMultiplicity 0 b := by
    rw [Polynomial.rootMultiplicity_mul (by
      apply mul_ne_zero
      · rw [← hcomp]; exact hB0
      · exact hbne)]
    rw [rootMult_comp_X_pow b hbne]
    ring
  have hLHSne : Polynomial.X ^ 2 * (a.comp (Polynomial.X ^ 3) * b - b.comp (Polynomial.X ^ 3) * a) ≠ 0 := by
    rw [key]
    exact mul_ne_zero (by rw [← hcomp]; exact hB0) hbne
  have heq_mult : Polynomial.rootMultiplicity 0
      (Polynomial.X ^ 2 * (a.comp (Polynomial.X ^ 3) * b - b.comp (Polynomial.X ^ 3) * a))
      = 4 * Polynomial.rootMultiplicity 0 b := by
    rw [key, hRHS]
  have hcrossne : a.comp (Polynomial.X ^ 3) * b - b.comp (Polynomial.X ^ 3) * a ≠ 0 := by
    intro h
    rw [h, mul_zero] at hLHSne
    exact hLHSne rfl
  have hLHS_split : Polynomial.rootMultiplicity 0
      (Polynomial.X ^ 2 * (a.comp (Polynomial.X ^ 3) * b - b.comp (Polynomial.X ^ 3) * a))
      = 2 + Polynomial.rootMultiplicity 0 (a.comp (Polynomial.X ^ 3) * b - b.comp (Polynomial.X ^ 3) * a) := by
    rw [Polynomial.rootMultiplicity_mul (mul_ne_zero (pow_ne_zero 2 Polynomial.X_ne_zero) hcrossne)]
    congr 1
    have : Polynomial.rootMultiplicity (0 : ℚ) (Polynomial.X ^ 2) = 2 := by
      rw [← Polynomial.count_roots, Polynomial.roots_X_pow]
      simp
    exact this
  have hcombine : 2 + Polynomial.rootMultiplicity 0 (a.comp (Polynomial.X ^ 3) * b - b.comp (Polynomial.X ^ 3) * a)
      = 4 * Polynomial.rootMultiplicity 0 b := by
    rw [← hLHS_split, heq_mult]
  have ht1 : 1 ≤ Polynomial.rootMultiplicity 0 b := by omega
  have hXb : (Polynomial.X : Polynomial ℚ) ∣ b := by
    have hpos : b.IsRoot 0 := by
      rw [← Polynomial.rootMultiplicity_pos (x := (0:ℚ)) hbne] at *
      omega
    have := (Polynomial.dvd_iff_isRoot (a := (0:ℚ))).mpr hpos
    simpa using this
  have hXa : ¬ (Polynomial.X : Polynomial ℚ) ∣ a := by
    intro hXa
    have hunit : IsUnit (Polynomial.X : Polynomial ℚ) := hcop.isUnit_of_dvd' hXa hXb
    exact Polynomial.not_isUnit_X hunit
  have hra : Polynomial.rootMultiplicity 0 a = 0 := by
    apply Polynomial.rootMultiplicity_eq_zero
    rw [← Polynomial.dvd_iff_isRoot]
    simpa using hXa
  have hane : a ≠ 0 := fun h => hXa (h ▸ dvd_zero _)
  have hAne : a.comp (Polynomial.X ^ 3) ≠ 0 := by
    rw [← hcomp]
    intro h
    apply hane
    have hinj : Function.Injective
        (Polynomial.aeval (Polynomial.X ^ 3 : Polynomial ℚ) : Polynomial ℚ →ₐ[ℚ] Polynomial ℚ) := by
      have heq : (Polynomial.aeval (Polynomial.X ^ 3 : Polynomial ℚ) : Polynomial ℚ →ₐ[ℚ] Polynomial ℚ)
          = Polynomial.expand ℚ 3 :=
        Polynomial.algHom_ext (by rw [Polynomial.aeval_X, Polynomial.expand_X])
      rw [heq]; exact Polynomial.expand_injective (by norm_num)
    exact hinj (by simpa using h)
  have hAb : Polynomial.rootMultiplicity 0 (a.comp (Polynomial.X ^ 3) * b)
      = Polynomial.rootMultiplicity 0 b := by
    rw [Polynomial.rootMultiplicity_mul (mul_ne_zero hAne hbne), rootMult_comp_X_pow a hane, hra]
    ring
  have hBa : Polynomial.rootMultiplicity 0 (b.comp (Polynomial.X ^ 3) * a)
      = 3 * Polynomial.rootMultiplicity 0 b := by
    rw [Polynomial.rootMultiplicity_mul (mul_ne_zero (by rw [← hcomp]; exact hB0) hane),
      rootMult_comp_X_pow b hbne, hra]
    ring
  set t := Polynomial.rootMultiplicity 0 b with ht
  have hneg : Polynomial.rootMultiplicity 0 (-(b.comp (Polynomial.X ^ 3) * a))
      = Polynomial.rootMultiplicity 0 (b.comp (Polynomial.X ^ 3) * a) := by
    rw [← Polynomial.count_roots, ← Polynomial.count_roots, Polynomial.roots_neg]
  have hlow : t ≤ Polynomial.rootMultiplicity 0 (a.comp (Polynomial.X ^ 3) * b - b.comp (Polynomial.X ^ 3) * a) := by
    have := Polynomial.rootMultiplicity_add (0:ℚ) (p := a.comp (Polynomial.X ^ 3) * b) (q := -(b.comp (Polynomial.X ^ 3) * a)) (by rwa [← sub_eq_add_neg])
    rw [← sub_eq_add_neg, hAb, hneg, hBa] at this
    omega
  have hAb_eq : a.comp (Polynomial.X ^ 3) * b
      = (a.comp (Polynomial.X ^ 3) * b - b.comp (Polynomial.X ^ 3) * a) + b.comp (Polynomial.X ^ 3) * a := by
    ring
  have hupp : min (Polynomial.rootMultiplicity 0 (a.comp (Polynomial.X ^ 3) * b - b.comp (Polynomial.X ^ 3) * a)) (3 * t) ≤ t := by
    have := Polynomial.rootMultiplicity_add (0:ℚ)
      (p := a.comp (Polynomial.X ^ 3) * b - b.comp (Polynomial.X ^ 3) * a)
      (q := b.comp (Polynomial.X ^ 3) * a) (by rw [← hAb_eq]; exact mul_ne_zero hAne hbne)
    rw [← hAb_eq, hAb, hBa] at this
    exact this
  omega  -- THE REAL MATH: pole-order. pole m ⟹ σ(ψ)−ψ pole 3m ≠ 2; m=0 ⟹ regular ≠ z⁻².
         -- Needs order/valuation on RatFunc. This is the one you + I actually build.


-- Tool 3 (Laurent, likely cleanest for P2):

/-! ============================================================
    TIER 3 — the group conclusion. DEFERRED.
    G₁ = 𝔾ₐ needs a build-by-hand group object (no PV in mathlib).
    The CONTENT is P1 + P2 above; this is interpretation. Later.
    ============================================================ -/

    -- the valuation object at prime X:

end QDiff2
