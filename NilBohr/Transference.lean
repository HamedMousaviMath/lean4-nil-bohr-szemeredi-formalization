import NilBohr.Ergodic

/-! The orbit identity in the proof of Proposition 7.1. -/

open Filter MeasureTheory Polynomial
open scoped BigOperators

namespace NilBohr

noncomputable def weightedErgodicAverage {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (T : ProbabilitySystem X μ) {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ)
    (f : Fin ℓ → X → ℂ) (v : ℤ → ℂ) (H : ℕ) (x : X) : ℂ :=
  (∑ n ∈ positiveInterval H, v n * ergodicSequence T P f n x) / (H : ℂ)

private theorem positiveInterval_card_orbit (N : ℕ) : (positiveInterval N).card = N := by
  rw [positiveInterval, Int.card_Icc]
  simp

theorem ProbabilitySystem.integral_iterate {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (T : ProbabilitySystem X μ) (m : ℤ) (a : X → ℂ) :
    ∫ z, a ((T.transform ^ m) z) ∂μ = ∫ z, a z ∂μ := by
  let e : X ≃ᵐ X := {
    toEquiv := T.transform ^ m
    measurable_toFun := (T.preserves m).measurable
    measurable_invFun := by
      change Measurable (⇑(T.transform ^ m)⁻¹)
      rw [← zpow_neg]
      exact (T.preserves (-m)).measurable }
  exact (T.preserves m).integral_comp e.measurableEmbedding a

/-- Truncated orbit inputs used for transference. The first input is the dual
test, and all subsequent functions are evaluated on the same orbit. -/
def orbitInputs {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (T : ProbabilitySystem X μ) {ℓ : ℕ} (f : Fin ℓ → X → ℂ) (g : X → ℂ)
    (Z : Finset ℤ) (z : X) : Fin (ℓ + 1) → ℤ → ℂ :=
  Fin.cases (fun m => g ((T.transform ^ m) z))
    (fun i m => if m ∈ Z then f i ((T.transform ^ m) z) else 0)

theorem orbit_counting_eq_average {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (T : ProbabilitySystem X μ) {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ)
    (f : Fin ℓ → X → ℂ) (g : X → ℂ) (v : ℤ → ℂ) (N H : ℕ)
    (Z : Finset ℤ) (hz : ∀ m ∈ positiveInterval N, ∀ n ∈ positiveInterval H,
      ∀ i, m + (P i).eval n ∈ Z) (z : X) :
    countingForm N H (positiveInterval N) (Fin.cases 0 P) v (orbitInputs T f g Z z) =
      (∑ m ∈ positiveInterval N, (fun x => weightedErgodicAverage T P f v H x * g x)
        ((T.transform ^ m) z)) / (N : ℂ) := by
  unfold countingForm
  simp only [weightedErgodicAverage, div_mul_eq_mul_div]
  rw [← Finset.sum_div, div_div, mul_comm (H : ℂ)]
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [Fin.prod_univ_succ, Fin.cases_zero, eval_zero, add_zero,
    orbitInputs, Fin.cases_succ, ergodicSequence, if_pos (hz m hm n hn)]
  have he (i : Fin ℓ) :
      (T.transform ^ (m + (P i).eval n)) z =
        (T.transform ^ (P i).eval n) ((T.transform ^ m) z) := by
    rw [add_comm, zpow_add, Equiv.Perm.mul_apply]
  simp_rw [he]
  simp only [hz m hm n hn, if_true]
  ring

/-- Averaging the orbit change of variables yields the discrete identity used
inside L¹ duality. The spatial set can be any finite window containing all
shifted coordinates. -/
theorem integral_orbit_countingForm {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (T : ProbabilitySystem X μ) {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ)
    (f : Fin ℓ → X → ℂ) (g : X → ℂ) (v : ℤ → ℂ) {N H : ℕ}
    (hN : 0 < N) (Z : Finset ℤ)
    (hz : ∀ m ∈ positiveInterval N, ∀ n ∈ positiveInterval H, ∀ i,
      m + (P i).eval n ∈ Z)
    (hInt : Integrable (fun x => weightedErgodicAverage T P f v H x * g x) μ) :
    (∫ z, countingForm N H (positiveInterval N) (Fin.cases 0 P) v
      (orbitInputs T f g Z z) ∂μ) =
      ∫ x, weightedErgodicAverage T P f v H x * g x ∂μ := by
  let a := fun x => weightedErgodicAverage T P f v H x * g x
  simp_rw [orbit_counting_eq_average T P f g v N H Z hz]
  change (∫ z, (∑ m ∈ positiveInterval N, a ((T.transform ^ m) z)) / (N : ℂ) ∂μ) = ∫ z, a z ∂μ
  have hEach (m : ℤ) : Integrable (fun z => a ((T.transform ^ m) z)) μ := by
    exact ((T.preserves m).integrable_comp hInt.aestronglyMeasurable).2 hInt
  simp_rw [div_eq_mul_inv]
  rw [integral_mul_const, integral_finset_sum _ (fun m _ => hEach m)]
  simp_rw [T.integral_iterate]
  simp only [Finset.sum_const, positiveInterval_card_orbit, nsmul_eq_mul]
  rw [mul_right_comm, mul_inv_cancel₀ (by exact_mod_cast hN.ne'), one_mul]

/-- A bounded dual test attaining the L¹ norm, with value zero at zero. -/
noncomputable def dualTestValue (z : ℂ) : ℂ :=
  (starRingEnd ℂ) z / (‖z‖ : ℂ)

theorem norm_dualTestValue_le (z : ℂ) : ‖dualTestValue z‖ ≤ 1 := by
  by_cases hz : z = 0
  · simp [dualTestValue, hz]
  · rw [dualTestValue, norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _), div_self (norm_ne_zero_iff.mpr hz)]

theorem mul_dualTestValue (z : ℂ) : z * dualTestValue z = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · simp [dualTestValue, hz]
  · rw [dualTestValue, ← mul_div_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      Complex.ofReal_pow, pow_two, mul_div_cancel_right₀]
    exact_mod_cast norm_ne_zero_iff.mpr hz

/-- Any uniform bound on the orbit count transfers to an L¹ bound. This applies
with the discrete estimate of Teräväinen once the phase bounds and the common
spatial window have been supplied. -/
theorem integral_norm_weightedErgodicAverage_le_of_orbit_bound
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    (T : ProbabilitySystem X μ) {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ)
    (f : Fin ℓ → X → ℂ) (v : ℤ → ℂ) {N H : ℕ}
    (hN : 0 < N) (Z : Finset ℤ)
    (hz : ∀ m ∈ positiveInterval N, ∀ n ∈ positiveInterval H, ∀ i,
      m + (P i).eval n ∈ Z)
    (hA : Integrable (weightedErgodicAverage T P f v H) μ)
    (E : ℝ)
    (hbound : ∀ (g : X → ℂ), (∀ x, ‖g x‖ ≤ 1) → ∀ z,
      ‖countingForm N H (positiveInterval N) (Fin.cases 0 P) v
        (orbitInputs T f g Z z)‖ ≤ E) :
    (∫ x, ‖weightedErgodicAverage T P f v H x‖ ∂μ) ≤ E := by
  let A := weightedErgodicAverage T P f v H
  let g := fun x => dualTestValue (A x)
  have hg (x : X) : ‖g x‖ ≤ 1 := norm_dualTestValue_le (A x)
  have hprod : (fun x => A x * g x) = (fun x => (‖A x‖ : ℂ)) :=
    funext (fun x => mul_dualTestValue (A x))
  have hInt : Integrable (fun x => A x * g x) μ := by
    rw [hprod]
    exact Complex.ofRealCLM.integrable_comp hA.norm
  have h := norm_integral_le_of_norm_le_const (μ := μ) (ae_of_all _ (hbound g hg))
  rw [integral_orbit_countingForm T P f g v hN Z hz hInt] at h
  change ‖∫ x, A x * g x ∂μ‖ ≤ E * μ.real Set.univ at h
  rw [hprod, integral_complex_ofReal, Complex.norm_real,
    Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _)),
    measureReal_univ_eq_one, mul_one] at h
  exact h

end NilBohr
