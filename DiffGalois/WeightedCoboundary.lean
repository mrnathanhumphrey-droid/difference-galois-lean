import Mathlib
import DiffGalois.Coboundary
set_option linter.style.whitespace false
set_option linter.style.longLine false

open RatFunc

/-- Weighted partial sum: `wS c r 0 = 0`, `wS c r (k+1) = c · wS c r k + r k`.
At `c = 1` this is `partialS`. -/
def wS (c : ℚ) (r : ℕ → ℚ) : ℕ → ℚ
  | 0 => 0
  | (k+1) => c * wS c r k + r k

lemma wS_closed_form (c : ℚ) (r : ℕ → ℚ) (n : ℕ) :
    wS c r n = ∑ i ∈ Finset.range n, c ^ (n - 1 - i) * r i := by
  induction n with
  | zero => simp [wS]
  | succ n ih =>
    rw [Finset.sum_range_succ, show wS c r (n + 1) = c * wS c r n + r n from rfl, ih]
    have htop : c ^ (n + 1 - 1 - n) * r n = r n := by
      have h0 : n + 1 - 1 - n = 0 := by omega
      rw [h0, pow_zero, one_mul]
    have hlow : ∑ i ∈ Finset.range n, c ^ (n + 1 - 1 - i) * r i
        = c * ∑ i ∈ Finset.range n, c ^ (n - 1 - i) * r i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hin : i < n := Finset.mem_range.mp hi
      have hexp : n + 1 - 1 - i = (n - 1 - i) + 1 := by omega
      rw [hexp, pow_succ]
      ring
    rw [htop, hlow]

lemma wS_one (r : ℕ → ℚ) (n : ℕ) :
    wS 1 r n = ∑ i ∈ Finset.range n, r i := by
  rw [wS_closed_form]
  apply Finset.sum_congr rfl
  intro i _
  rw [one_pow, one_mul]

lemma wS_pos (c : ℚ) (r : ℕ → ℚ) (n : ℕ) (hc : 0 < c)
    (hr : ∀ i, 0 ≤ r i) (k : ℕ) (hk : k < n) (hrk : 0 < r k) :
    0 < wS c r n := by
  rw [wS_closed_form]
  apply Finset.sum_pos'
  · intro i _
    exact mul_nonneg (pow_pos hc _).le (hr i)
  · exact ⟨k, Finset.mem_range.mpr hk, mul_pos (pow_pos hc _) hrk⟩

lemma wS_ne_zero_of_dominant (c : ℚ) (r : ℕ → ℚ) (n : ℕ) (hc : 0 < c)
    (hr : ∀ i, 0 ≤ r i) (k : ℕ) (hk : k < n) (hrk : 0 < r k) :
    wS c r n ≠ 0 :=
  (wS_pos c r n hc hr k hk hrk).ne'

/-- The weight-`c` witness `h = − Σ_{j<n} (wS c r (j+1)) · z^(−2·3^j)`. -/
noncomputable def wPsiC (c : ℚ) (r : ℕ → ℚ) (n : ℕ) : RatFunc ℚ :=
  ∑ j ∈ Finset.range n, RatFunc.C (- wS c r (j+1)) * (X : RatFunc ℚ) ^ (-2 * 3 ^ j : ℤ)

/-- Weighted key identity (with boundary term). Adapted from your `σ_wPsi_sub_eq`. -/
lemma wPsiC_sub_eq (c : ℚ) (r : ℕ → ℚ) (n : ℕ) :
    RatFunc.C c * σ (wPsiC c r n) - wPsiC c r n
      = wTarget r n - RatFunc.C (c * wS c r n) * (X : RatFunc ℚ) ^ (-2 * 3 ^ n : ℤ) := by
  induction n with
  | zero => simp [wPsiC, wTarget, wS]
  | succ n ih =>
    unfold wPsiC wTarget at *
    rw [Finset.sum_range_succ, Finset.sum_range_succ,
        map_add, mul_add, map_mul, σ_C, σ_pole_monomial]
    have hwS : wS c r (n + 1) = c * wS c r n + r n := rfl
    have e1 : RatFunc.C (- wS c r (n + 1))
        = - (RatFunc.C c * RatFunc.C (wS c r n) + RatFunc.C (r n)) := by
      rw [hwS, map_neg, map_add, map_mul]
    have e2 : RatFunc.C (c * wS c r (n + 1))
        = RatFunc.C c * (RatFunc.C c * RatFunc.C (wS c r n) + RatFunc.C (r n)) := by
      rw [hwS, map_mul, map_add, map_mul]
    have e3 : RatFunc.C (c * wS c r n) = RatFunc.C c * RatFunc.C (wS c r n) :=
      map_mul _ _ _
    rw [e1, e2]
    linear_combination ih - (X : RatFunc ℚ) ^ (-2 * 3 ^ n : ℤ) * e3

/-- Forward half: if the weighted sum vanishes, the weight-`c` coboundary is solvable. -/
theorem W1c_of_wS_zero (c : ℚ) (r : ℕ → ℚ) (n : ℕ) (h : wS c r n = 0) :
    RatFunc.C c * σ (wPsiC c r n) - wPsiC c r n = wTarget r n := by
  rw [wPsiC_sub_eq, h, mul_zero, map_zero, zero_mul, sub_zero]

lemma wReduction (c : ℚ) (r : ℕ → ℚ) (n : ℕ) (h : RatFunc ℚ)
    (hh : RatFunc.C c * σ h - h = wTarget r n) :
    RatFunc.C c * σ (h - wPsiC c r n) - (h - wPsiC c r n)
      = RatFunc.C (c * wS c r n) * (X : RatFunc ℚ) ^ (-2 * 3 ^ n : ℤ) := by
  rw [map_sub, mul_sub]
  linear_combination hh - wPsiC_sub_eq c r n

theorem weighted_single_monomial_zero (w₀ c : ℚ) (hw : w₀ ≠ 0)
    (h : ∃ φ : RatFunc ℚ, RatFunc.C w₀ * σ φ - φ = RatFunc.C c * (X : RatFunc ℚ) ^ (-2 * 3 ^ 0 : ℤ)) :
    c = 0 := by
  obtain ⟨φ, hφ⟩ := h
  rcases eq_or_ne φ 0 with rfl | hφ0
  · simp only [map_zero, mul_zero, sub_zero] at hφ
    have hz : (X : RatFunc ℚ) ^ (-2 * 3 ^ 0 : ℤ) ≠ 0 := zpow_ne_zero _ RatFunc.X_ne_zero
    rw [eq_comm, mul_eq_zero] at hφ
    rcases hφ with hcc | hzz
    · apply RatFunc.C_injective (K := ℚ)
      rw [map_zero]; exact hcc
    · exact absurd hzz hz
  · have hexp : (Polynomial.aeval (Polynomial.X ^ 3 : Polynomial ℚ) : Polynomial ℚ →ₐ[ℚ] Polynomial ℚ)
        = Polynomial.expand ℚ 3 :=
      Polynomial.algHom_ext (by rw [Polynomial.aeval_X, Polynomial.expand_X])
    have hinj : Function.Injective
        (Polynomial.aeval (Polynomial.X ^ 3 : Polynomial ℚ) : Polynomial ℚ →ₐ[ℚ] Polynomial ℚ) := by
      rw [hexp]; exact Polynomial.expand_injective (by norm_num)
    have hcomp : ∀ p : Polynomial ℚ,
        (Polynomial.aeval (Polynomial.X ^ 3 : Polynomial ℚ)) p = p.comp (Polynomial.X ^ 3) := by
      intro p; simp [Polynomial.aeval_def, Polynomial.comp]
    rw [← RatFunc.num_div_denom φ, map_div₀, σ_algebraMap, σ_algebraMap, ← mul_div_assoc] at hφ
    set a := φ.num with ha
    set b := φ.denom with hb
    have hbne : b ≠ 0 := RatFunc.denom_ne_zero φ
    have hane : a ≠ 0 := RatFunc.num_ne_zero hφ0
    have hb0 : (algebraMap (Polynomial ℚ) (RatFunc ℚ) b) ≠ 0 := by simpa using hbne
    have hB0 : (algebraMap (Polynomial ℚ) (RatFunc ℚ)
        ((Polynomial.aeval (Polynomial.X ^ 3 : Polynomial ℚ)) b)) ≠ 0 := by
      rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (Polynomial ℚ) (RatFunc ℚ))]
      intro hh
      apply hbne
      exact hinj (by simpa using hh)
    rw [div_sub_div _ _ hB0 hb0, div_eq_iff (mul_ne_zero hB0 hb0)] at hφ
    have hmul := congrArg (· * (X : RatFunc ℚ) ^ (2 * 3 ^ 0 : ℤ)) hφ
    simp only at hmul
    have hpole : (X : RatFunc ℚ) ^ (-2 * 3 ^ 0 : ℤ) * (X : RatFunc ℚ) ^ (2 * 3 ^ 0 : ℤ) = 1 := by
      rw [← zpow_add₀ RatFunc.X_ne_zero]; norm_num
    have hrhs : RatFunc.C c * (X : RatFunc ℚ) ^ (-2 * 3 ^ 0 : ℤ)
          * (algebraMap (Polynomial ℚ) (RatFunc ℚ) ((Polynomial.aeval (Polynomial.X ^ 3 : Polynomial ℚ)) b)
              * algebraMap (Polynomial ℚ) (RatFunc ℚ) b) * (X : RatFunc ℚ) ^ (2 * 3 ^ 0 : ℤ)
        = RatFunc.C c * (algebraMap (Polynomial ℚ) (RatFunc ℚ) ((Polynomial.aeval (Polynomial.X ^ 3 : Polynomial ℚ)) b)
              * algebraMap (Polynomial ℚ) (RatFunc ℚ) b) := by
      rw [show RatFunc.C c * (X : RatFunc ℚ) ^ (-2 * 3 ^ 0 : ℤ)
              * (algebraMap (Polynomial ℚ) (RatFunc ℚ) ((Polynomial.aeval (Polynomial.X ^ 3 : Polynomial ℚ)) b)
                  * algebraMap (Polynomial ℚ) (RatFunc ℚ) b) * (X : RatFunc ℚ) ^ (2 * 3 ^ 0 : ℤ)
            = RatFunc.C c * (algebraMap (Polynomial ℚ) (RatFunc ℚ) ((Polynomial.aeval (Polynomial.X ^ 3 : Polynomial ℚ)) b)
                  * algebraMap (Polynomial ℚ) (RatFunc ℚ) b)
                * ((X : RatFunc ℚ) ^ (-2 * 3 ^ 0 : ℤ) * (X : RatFunc ℚ) ^ (2 * 3 ^ 0 : ℤ)) by ring]
      rw [hpole, mul_one]
    rw [hrhs] at hmul
    have hXpow : (X : RatFunc ℚ) ^ (2 * 3 ^ 0 : ℤ)
        = algebraMap (Polynomial ℚ) (RatFunc ℚ) (Polynomial.X ^ (2 * 3 ^ 0)) := by
      rw [map_pow, RatFunc.algebraMap_X, ← zpow_natCast (X : RatFunc ℚ) (2 * 3 ^ 0)]; norm_num
    rw [hXpow,
        show (RatFunc.C c : RatFunc ℚ) = algebraMap (Polynomial ℚ) (RatFunc ℚ) (Polynomial.C c) from rfl,
        show (RatFunc.C w₀ : RatFunc ℚ) = algebraMap (Polynomial ℚ) (RatFunc ℚ) (Polynomial.C w₀) from rfl] at hmul
    simp only [← map_mul, ← map_sub] at hmul
    rw [(IsFractionRing.injective (Polynomial ℚ) (RatFunc ℚ)).eq_iff] at hmul
    simp only [hcomp] at hmul
    have hid : (Polynomial.C w₀ * a.comp (Polynomial.X ^ 3) * b - b.comp (Polynomial.X ^ 3) * a)
          * Polynomial.X ^ (2 * 3 ^ 0)
        = Polynomial.C c * (b.comp (Polynomial.X ^ 3) * b) := by linear_combination hmul
    exact weighted_pole_core w₀ c hw a b hane hbne (RatFunc.isCoprime_num_denom φ) hid

theorem single_monomial_coboundary_weighted (w₀ : ℚ) (hw : w₀ ≠ 0) (c : ℚ) (m : ℕ)
    (h : ∃ φ : RatFunc ℚ, RatFunc.C w₀ * σ φ - φ = RatFunc.C c * (X : RatFunc ℚ) ^ (-2 * 3 ^ m : ℤ)) :
    c = 0 := by
  induction m generalizing c with
  | zero => exact weighted_single_monomial_zero w₀ c hw h
  | succ m ih =>
    obtain ⟨φ, hφ⟩ := h
    have hdiv : c / w₀ = 0 := by
      apply ih (c / w₀)
      refine ⟨φ - RatFunc.C (c / w₀) * (X : RatFunc ℚ) ^ (-2 * 3 ^ m : ℤ), ?_⟩
      have hσg : σ (RatFunc.C (c / w₀) * (X : RatFunc ℚ) ^ (-2 * 3 ^ m : ℤ))
          = RatFunc.C (c / w₀) * (X : RatFunc ℚ) ^ (-2 * 3 ^ (m + 1) : ℤ) := by
        rw [map_mul, σ_C, σ_pole_monomial]
      have hww : RatFunc.C w₀ * RatFunc.C (c / w₀) = RatFunc.C c := by
        rw [← map_mul]
        congr 1
        field_simp
      rw [map_sub, mul_sub, hσg]
      linear_combination hφ - (X : RatFunc ℚ) ^ (-2 * 3 ^ (m + 1) : ℤ) * hww
    field_simp at hdiv
    simpa using hdiv

/-- The obstruction: for a nonzero weight `c`, if the weighted coboundary equation is
solvable then `wS c r n` vanishes. -/
theorem wObstruction (c : ℚ) (hc : c ≠ 0) (r : ℕ → ℚ) (n : ℕ)
    (h : ∃ h : RatFunc ℚ, RatFunc.C c * σ h - h = wTarget r n) :
    wS c r n = 0 := by
  obtain ⟨g, hg⟩ := h
  have hred : RatFunc.C c * σ (g - wPsiC c r n) - (g - wPsiC c r n)
      = RatFunc.C (c * wS c r n) * (X : RatFunc ℚ) ^ (-2 * 3 ^ n : ℤ) := wReduction c r n g hg
  have hcws : c * wS c r n = 0 :=
    single_monomial_coboundary_weighted c hc (c * wS c r n) n ⟨g - wPsiC c r n, hred⟩
  rcases mul_eq_zero.mp hcws with h0 | h0
  · exact absurd h0 hc
  · exact h0

/-- **The weighted coboundary criterion.** For a nonzero weight `c`, the target
`wTarget r n` is a `c`-weighted σ-coboundary iff `wS c r n = 0`. -/
theorem W1c (c : ℚ) (hc : c ≠ 0) (r : ℕ → ℚ) (n : ℕ) :
    (∃ h : RatFunc ℚ, RatFunc.C c * σ h - h = wTarget r n) ↔ wS c r n = 0 := by
  constructor
  · exact wObstruction c hc r n
  · intro hs
    exact ⟨wPsiC c r n, W1c_of_wS_zero c r n hs⟩
