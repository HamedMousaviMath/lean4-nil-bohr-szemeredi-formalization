import NilBohr.AmbientSelectorComparison
import NilBohr.ErgodicLimits

/-! The prime number theorem bounds the total Mangoldt mass in the shifted
parameter window. The finite count is monotone in its real test function, so
Lipschitz minorants and majorants give the sharp arc uniformly in the spatial set. -/

open Filter MeasureTheory Polynomial
open scoped Topology NNReal

namespace NilBohr
noncomputable section

/-- The normalized Mangoldt mass in the exact parameter window (1≤n≤M). -/
def ambientMangoldtMass (M : ℕ) : ℝ :=
  (∑ n ∈ positiveInterval M, ArithmeticFunction.vonMangoldt (n+1).toNat) / (M : ℝ)

private theorem ambientMangoldtMass_numerator (M : ℕ) :
    (∑ n ∈ positiveInterval M, ArithmeticFunction.vonMangoldt (n+1).toNat) =
      ∑ n ∈ Finset.range (M+2), ArithmeticFunction.vonMangoldt n := by
  classical
  rw [show M+2 = 2+M by omega, Finset.sum_range_add, Finset.sum_range_succ]
  simp only [Finset.sum_range_one, ArithmeticFunction.map_zero,
    ArithmeticFunction.vonMangoldt_apply_one, add_zero, zero_add]
  symm
  apply Finset.sum_bij (fun (i : ℕ) _ => (i : ℤ)+1)
  · intro i hi
    have hi' := Finset.mem_range.mp hi
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro i _ j _ hij
    omega
  · intro n hn
    obtain ⟨hl, hr⟩ := Finset.mem_Icc.mp hn
    refine ⟨(n-1).toNat, Finset.mem_range.mpr ?_, ?_⟩ <;> omega
  · intro i hi
    have h : ((i:ℤ)+1+1).toNat = 2+i := by omega
    simp only [h]

/-- Prime number theorem and higher-prime-power removal in the shifted window. -/
theorem tendsto_ambientMangoldtMass (hPNT : PrimeNumberTheorem) :
    Tendsto ambientMangoldtMass atTop (𝓝 1) := by
  let P (N : ℕ) := (∑ p ∈ primesThrough N, Real.log (p : ℝ)) / (N : ℝ)
  let L (N : ℕ) := (∑ n ∈ Finset.range (N+1), ArithmeticFunction.vonMangoldt n) / (N : ℝ)
  have hErr (N : ℕ) :
      ‖L N - P N‖ ≤
        (∑ n ∈ higherPrimePowersThrough N, ArithmeticFunction.vonMangoldt n) / (N : ℝ) := by
    simpa [L, P, primesThrough, div_eq_inv_mul, smul_eq_mul] using
      norm_sub_mangoldt_logPrime_le (u := fun _ => (1 : ℝ)) (B := 1) (by simp) N
  have hZero : Tendsto (fun N => L N - P N) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) hErr tendsto_higherPrimePowers_mangoldtMass_div
  have hL : Tendsto L atTop (𝓝 1) := by
    have hP : Tendsto P atTop (𝓝 1) := hPNT.theta
    simpa only [sub_add_cancel, zero_add] using hZero.add hP
  have hShift : Tendsto (fun M : ℕ => L (M+1)) atTop (𝓝 1) :=
    hL.comp (tendsto_add_atTop_nat 1)
  have hInv : Tendsto (fun M : ℕ => (M : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hRatio : Tendsto (fun M : ℕ => (1 : ℝ) + (M : ℝ)⁻¹) atTop (𝓝 1) := by
    simpa only [add_zero] using tendsto_const_nhds.add hInv
  have hProduct : Tendsto (fun M : ℕ => L (M+1) * ((1 : ℝ) + (M : ℝ)⁻¹))
      atTop (𝓝 1) := by
    simpa only [one_mul] using hShift.mul hRatio
  refine hProduct.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with M hM
  have h0 : (M : ℝ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  rw [ambientMangoldtMass, ambientMangoldtMass_numerator]
  simp only [L, Nat.cast_add, Nat.cast_one]
  have h1 : (M : ℝ) + 1 ≠ 0 := by positivity
  field_simp

/-- Formula (10) evaluated over the surviving base coordinates (x ∈ A).
All omitted integer coordinates have a zero first indicator. -/
theorem ambientSelectorCount_eq_explicit (N : ℕ) (A : Finset ℤ) (V : ℤ → ℝ)
    (F : Circle → ℂ) (hA : A ⊆ positiveInterval N) :
    ambientSelectorCount N A V F =
      (∑ x ∈ A, ∑ n ∈ positiveInterval N.sqrt,
        (ArithmeticFunction.vonMangoldt (n+1).toNat : ℂ) * F (V n : Circle) *
          ((if x ∈ A then 1 else 0) * (if x+n ∈ A then 1 else 0) *
            (if x+n^2 ∈ A then 1 else 0))) / ((N : ℂ) * (N.sqrt : ℂ)) := by
  let f : Fin 3 → ℤ → ℂ := fun _ x => if x ∈ A then 1 else 0
  let θ (n : ℤ) := (ArithmeticFunction.vonMangoldt (n+1).toNat : ℂ) * F (V n : Circle)
  have hzero : separatingFamily 1 0 = 0 := by simp [separatingFamily]
  have hs : SupportedOn A (f 0) := fun _ hx => if_neg hx
  change countingForm N N.sqrt (positiveInterval N) (separatingFamily 1) θ f = _
  rw [← countingForm_mono_window N N.sqrt hA _ hzero θ f hs]
  unfold countingForm
  apply congrArg (fun z : ℂ => z / ((N : ℂ) * (N.sqrt : ℂ)))
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro n hn
  simp [Fin.prod_univ_three, f, θ, separatingFamily, mul_assoc]

private def ambientIndicatorProduct (A : Finset ℤ) (x n : ℤ) : ℝ :=
  ∏ i : Fin 3, if x + (separatingFamily 1 i).eval n ∈ A then 1 else 0

private theorem ambientIndicatorProduct_nonneg (A : Finset ℤ) (x n : ℤ) :
    0 ≤ ambientIndicatorProduct A x n := by
  apply Finset.prod_nonneg
  intro i hi
  split <;> norm_num

private theorem ambientIndicatorProduct_le_one (A : Finset ℤ) (x n : ℤ) :
    ambientIndicatorProduct A x n ≤ 1 := by
  refine Finset.prod_le_one (fun i _ => ?_) (fun i _ => ?_)
  all_goals split <;> norm_num

private def ambientRealCount (N : ℕ) (A : Finset ℤ) (V : ℤ → ℝ) (F : Circle → ℝ) : ℝ :=
  (∑ x ∈ positiveInterval N, ∑ n ∈ positiveInterval N.sqrt,
    ArithmeticFunction.vonMangoldt (n+1).toNat * F (V n : Circle) *
      ambientIndicatorProduct A x n) / ((N : ℝ) * (N.sqrt : ℝ))

private theorem ambientSelectorCount_ofReal (N : ℕ) (A : Finset ℤ) (V : ℤ → ℝ)
    (F : Circle → ℝ) :
    ambientSelectorCount N A V (fun t => (F t : ℂ)) = (ambientRealCount N A V F : ℂ) := by
  unfold ambientSelectorCount countingForm ambientRealCount ambientIndicatorProduct
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro n hn
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  change (if x + (separatingFamily 1 i).eval n ∈ A then (1 : ℂ) else 0) =
    Complex.ofReal (if x + (separatingFamily 1 i).eval n ∈ A then (1 : ℝ) else 0)
  split <;> simp

private theorem ambientRealCount_mono (N : ℕ) (A : Finset ℤ) (V : ℤ → ℝ)
    {F G : Circle → ℝ} (h : ∀ t, F t ≤ G t) :
    ambientRealCount N A V F ≤ ambientRealCount N A V G := by
  unfold ambientRealCount
  apply div_le_div_of_nonneg_right _ (by positivity)
  gcongr with x hx n hn
  · exact ambientIndicatorProduct_nonneg _ _ _
  · exact ArithmeticFunction.vonMangoldt_nonneg
  · exact h _

private theorem ambientRealCount_one_nonneg (N : ℕ) (A : Finset ℤ) (V : ℤ → ℝ) :
    0 ≤ ambientRealCount N A V (fun _ => 1) := by
  unfold ambientRealCount
  refine div_nonneg ?_ (by positivity)
  exact Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun n _ =>
    mul_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg zero_le_one)
      (ambientIndicatorProduct_nonneg _ _ _)

private theorem ambientRealCount_one_le_mass (N : ℕ) (A : Finset ℤ) (V : ℤ → ℝ) :
    ambientRealCount N A V (fun _ => 1) ≤ ambientMangoldtMass N.sqrt := by
  unfold ambientRealCount ambientMangoldtMass
  calc
    _ ≤ (∑ _x ∈ positiveInterval N, ∑ n ∈ positiveInterval N.sqrt,
        ArithmeticFunction.vonMangoldt (n+1).toNat) / ((N : ℝ) * (N.sqrt : ℝ)) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.sum_le_sum
      intro n hn
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (ambientIndicatorProduct_le_one A x n) ArithmeticFunction.vonMangoldt_nonneg
    _ = _ := by
      by_cases hN : N = 0
      · simp [hN, positiveInterval]
      · have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN
        rw [Finset.sum_const, card_positiveInterval, nsmul_eq_mul, mul_div_mul_left _ _ hNr]

theorem ambientSelectorCount_one_norm_le_mass (N : ℕ) (A : Finset ℤ) (V : ℤ → ℝ) :
    ‖ambientSelectorCount N A V (fun _ => 1)‖ ≤ ambientMangoldtMass N.sqrt := by
  have h := ambientSelectorCount_ofReal N A V (fun _ => 1)
  simp only [Complex.ofReal_one] at h
  rw [h, Complex.norm_real, Real.norm_of_nonneg (ambientRealCount_one_nonneg _ _ _)]
  exact ambientRealCount_one_le_mass _ _ _

private theorem ambientMangoldtMass_eventually_lt_two (hPNT : PrimeNumberTheorem) :
    ∀ᶠ N : ℕ in atTop, ambientMangoldtMass N.sqrt < 2 := by
  have hSqrt : Tendsto Nat.sqrt atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop (b*b)] with n hn
    exact (Nat.le_sqrt).2 hn
  exact ((tendsto_ambientMangoldtMass hPNT).comp hSqrt).eventually (Iio_mem_nhds (by norm_num))

/-- In the PNT regime the unselected count is bounded uniformly in every spatial set. -/
theorem ambientSelectorCount_one_eventually_bounded (hPNT : PrimeNumberTheorem) :
    ∀ᶠ N : ℕ in atTop, ∀ (A : Finset ℤ) (V : ℤ → ℝ),
      ‖ambientSelectorCount N A V (fun _ => 1)‖ ≤ 2 := by
  filter_upwards [ambientMangoldtMass_eventually_lt_two hPNT] with N hn A V
  exact (ambientSelectorCount_one_norm_le_mass N A V).trans hn.le

private theorem circleMean_ambient_ofReal (F : Circle → ℝ) :
    circleMean (fun t => (F t : ℂ)) = Complex.ofReal (∫ t, F t ∂AddCircle.haarAddCircle) :=
  integral_complex_ofReal (f := F)

private theorem circleMean_ambient_bounded (F : Circle → ℝ) {K : ℝ≥0}
    (hLip : LipschitzWith K F) (h0 : ∀ t, 0 ≤ F t) (h1 : ∀ t, F t ≤ 1) :
    0 ≤ (∫ t, F t ∂AddCircle.haarAddCircle) ∧ (∫ t, F t ∂AddCircle.haarAddCircle) ≤ 1 := by
  have hi : Integrable F AddCircle.haarAddCircle :=
    hLip.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  exact ⟨integral_nonneg h0, by
    simpa using integral_mono hi (integrable_const (1 : ℝ)) h1⟩

/-- The proof-overview sharp-arc comparison, uniform in every spatial set
in the ambient interval. Both sides retain the shifted Mangoldt weight. -/
theorem ambientSelectorCount_sharp {V : ℤ → ℝ}
    (hTer : TeravainenFixedFamily) (hPNT : PrimeNumberTheorem)
    (hPhase : ∀ F : Circle → ℂ, (∃ K : ℝ≥0, LipschitzWith K F) → PrimeLocalPhase 2 V F)
    (J : OpenArc) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℤ, A ⊆ positiveInterval N →
      ‖ambientSelectorCount N A V (fun t => (J.circleIndicator t : ℂ)) -
        (J.length : ℂ) * ambientSelectorCount N A V (fun _ => 1)‖ < ε := by
  obtain ⟨l, u, K, hl, hu, horder, hmean, hgap⟩ :=
    J.exists_lipschitz_sandwich (show 0 < ε/10 by positivity)
  have hl0 (t : Circle) : 0 ≤ l t := (horder t).1
  have hl1 (t : Circle) : l t ≤ 1 :=
    (horder t).2.1.trans ((horder t).2.2.1.trans (horder t).2.2.2)
  have hu0 (t : Circle) : 0 ≤ u t :=
    (hl0 t).trans ((horder t).2.1.trans (horder t).2.2.1)
  have hu1 (t : Circle) : u t ≤ 1 := (horder t).2.2.2
  let μl := ∫ t, l t ∂AddCircle.haarAddCircle
  let μu := ∫ t, u t ∂AddCircle.haarAddCircle
  have hlIntegrable : Integrable l AddCircle.haarAddCircle :=
    hl.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have huIntegrable : Integrable u AddCircle.haarAddCircle :=
    hu.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_sub huIntegrable hlIntegrable] at hgap
  have hcent (F : Circle → ℝ) (hLip : LipschitzWith K F)
      (h0 : ∀ t, 0 ≤ F t) (h1 : ∀ t, F t ≤ 1) :
      ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℤ, A ⊆ positiveInterval N →
        |ambientRealCount N A V F -
          (∫ t, F t ∂AddCircle.haarAddCircle) * ambientRealCount N A V (fun _ => 1)| < ε/4 := by
    have hLip' : LipschitzWith K (fun t => (F t : ℂ)) := by
      simpa only [one_mul] using Complex.isometry_ofReal.lipschitz.comp hLip
    have hB (n : ℤ) :
        ‖(F (V n : Circle) : ℂ) - circleMean (fun t => (F t : ℂ))‖ ≤ 2 := by
      rw [circleMean_ambient_ofReal, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      obtain ⟨hm0, hm1⟩ := circleMean_ambient_bounded F hLip h0 h1
      exact abs_le.mpr ⟨by linarith [h0 (V n : Circle)], by linarith [h1 (V n : Circle)]⟩
    filter_upwards [ambientSelectorCount_centered hTer (hPhase _ ⟨K, hLip'⟩)
      (by norm_num : (0:ℝ) ≤ 2) hB (show 0 < ε/4 by positivity)] with N hN A hA
    have h := hN A hA
    rw [circleMean_ambient_ofReal, ambientSelectorCount_ofReal,
      show (fun _ : Circle => (1 : ℂ)) = (fun _ => ((1 : ℝ) : ℂ)) by simp,
      ambientSelectorCount_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs] at h
    exact h
  filter_upwards [ambientMangoldtMass_eventually_lt_two hPNT,
    hcent l hl hl0 hl1, hcent u hu hu0 hu1] with N hNmass hNl hNu A hA
  let B := ambientRealCount N A V (fun _ => 1)
  let T := ambientRealCount N A V J.circleIndicator
  have hB0 : 0 ≤ B := ambientRealCount_one_nonneg _ _ _
  have hB2 : B ≤ 2 := (ambientRealCount_one_le_mass _ _ _).trans hNmass.le
  have hTl : ambientRealCount N A V l ≤ T :=
    ambientRealCount_mono _ _ _ (fun t => (horder t).2.1)
  have hTu : T ≤ ambientRealCount N A V u :=
    ambientRealCount_mono _ _ _ (fun t => (horder t).2.2.1)
  have hμl : -(ε/10) < μl - J.length := (abs_lt.mp hmean).1
  have hμu : μu - J.length < ε/5 := by
    change μu - μl < ε/10 at hgap
    linarith [(abs_lt.mp hmean).2]
  have hlErr : -(ε/4) < ambientRealCount N A V l - μl * B := (abs_lt.mp (hNl A hA)).1
  have huErr : ambientRealCount N A V u - μu * B < ε/4 := (abs_lt.mp (hNu A hA)).2
  have hMassl : -(ε/5) ≤ (μl - J.length) * B := by
    calc
      _ ≤ -(ε/10) * B := by nlinarith [mul_nonneg (show 0 ≤ ε/10 by positivity) (sub_nonneg.mpr hB2)]
      _ ≤ _ := mul_le_mul_of_nonneg_right hμl.le hB0
  have hMassu : (μu - J.length) * B ≤ ε/2 := by
    calc
      _ ≤ (ε/5) * B := mul_le_mul_of_nonneg_right hμu.le hB0
      _ ≤ _ := by nlinarith [mul_nonneg (show 0 ≤ ε/5 by positivity) (sub_nonneg.mpr hB2)]
  rw [ambientSelectorCount_ofReal,
    show (fun _ : Circle => (1 : ℂ)) = (fun _ => ((1 : ℝ) : ℂ)) by simp,
    ambientSelectorCount_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, abs_lt]
  change -ε < T - J.length * B ∧ T - J.length * B < ε
  constructor <;> linarith

/-- The ambient comparison under the manuscript's admissibility hypotheses
and the analytic inputs already used for Proposition 6.2. -/
theorem heisenbergAmbientSelectorCount_sharp_of_literature {c₀ : ℝ}
    (hc₀ : 0 < c₀) (hc₁ : c₀ < 1/11) (hLit : PrimePhaseLiteratureInputs c₀)
    (hTer : TeravainenFixedFamily) (hPNT : PrimeNumberTheorem)
    {α β : ℝ} (hα : BadlyApproximable α) (hβ : AdmissibleBeta β)
    (J : OpenArc) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℤ, A ⊆ positiveInterval N →
      ‖ambientSelectorCount N A (heisenbergPhase α β) (fun t => (J.circleIndicator t : ℂ)) -
        (J.length : ℂ) * ambientSelectorCount N A (heisenbergPhase α β) (fun _ => 1)‖ < ε :=
  ambientSelectorCount_sharp hTer hPNT
    (heisenbergPrimeLocalPhase_of_literature hc₀ hc₁ hLit α β hα hβ 2 (by decide)) J hε

end
end NilBohr
