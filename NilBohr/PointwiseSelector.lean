import NilBohr.ArcApproximation
import NilBohr.ErgodicLimits

/-! Passage from Lipschitz weights to the selected prime interval. -/

open Filter MeasureTheory Polynomial
open scoped BigOperators ENNReal NNReal

namespace NilBohr

private theorem primeAverage_centered (u a : ℕ → ℂ) (c : ℂ) (N : ℕ) :
    primeAverage (fun p => (u p - c) * a p) N =
      primeAverage (fun p => u p * a p) N - c * primeAverage a N := by
  simp only [primeAverage, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, sub_div,
    mul_div_assoc]

private theorem primeAverage_centered_fun (u a : ℕ → ℂ) (c : ℂ) :
    primeAverage (fun p => (u p - c) * a p) =
      (fun N => primeAverage (fun p => u p * a p) N - c * primeAverage a N) :=
  funext (primeAverage_centered u a c)

private theorem primeAverage_one_of_two_le (N : ℕ) (hN : 2 ≤ N) :
    primeAverage (fun _ => 1) N = 1 := by
  have h : 2 ∈ primesThrough N := by
    simp [primesThrough, Nat.lt_succ_iff, Nat.prime_two, hN]
  have hc : ((primesThrough N).card : ℂ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr ⟨2, h⟩).ne'
  unfold primeAverage
  rw [Finset.sum_const, nsmul_eq_mul, mul_one, div_self hc]

/-- The smooth-weight prime limit, i.e. the last assertion of Proposition 7.1,
for all inputs on the fixed system and polynomial family. -/
def SmoothPrimeLimit {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (T : ProbabilitySystem X μ) {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ)
    (V : ℤ → ℝ) : Prop :=
  ∀ (f : Fin ℓ → X → ℂ), (∀ i, MemLp (f i) ∞ μ) →
    ∀ (F : Circle → ℂ), (∃ K : ℝ≥0, LipschitzWith K F) →
    ∀ᵐ x ∂μ, Tendsto (primeAverage (fun p =>
      (F (V ((p : ℤ) - 1) : Circle) - circleMean F) *
        ergodicSequence T P f ((p : ℤ) - 1) x)) atTop (nhds 0)

private theorem lipschitz_coe {F : Circle → ℝ} {K : ℝ≥0} (hF : LipschitzWith K F) :
    LipschitzWith K (fun t => (F t : ℂ)) := by
  simpa only [one_mul] using Complex.isometry_ofReal.lipschitz.comp hF

private theorem circleMean_ofReal (F : Circle → ℝ) :
    circleMean (fun t => (F t : ℂ)) = Complex.ofReal (∫ t, F t ∂AddCircle.haarAddCircle) :=
  integral_complex_ofReal (f := F)

private theorem real_primeAverage_tendsto_of_smooth
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    (T : ProbabilitySystem X μ) {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ) (V : ℤ → ℝ)
    (h : SmoothPrimeLimit T P V) (F : Circle → ℝ) {K : ℝ≥0} (hF : LipschitzWith K F) :
    Tendsto (fun N => (∑ p ∈ primesThrough N, F (V ((p : ℤ) - 1) : Circle)) /
      ((primesThrough N).card : ℝ)) atTop (nhds (∫ t, F t ∂AddCircle.haarAddCircle)) := by
  let m : ℝ := ∫ t, F t ∂AddCircle.haarAddCircle
  let u := fun p : ℕ => (F (V ((p : ℤ) - 1) : Circle) : ℂ)
  have h₁ := h (fun _ _ => 1) (fun _ => memLp_const 1) _ ⟨K, lipschitz_coe hF⟩
  obtain ⟨x, hx⟩ := h₁.exists
  have hc : Tendsto (fun N => primeAverage u N - (m : ℂ) *
      primeAverage (fun _ => 1) N) atTop (nhds 0) := by
    have heq := primeAverage_centered_fun u (fun _ => 1) (m : ℂ)
    rw [show (fun N => primeAverage u N - (m : ℂ) * primeAverage (fun _ => 1) N) =
      (fun N => primeAverage (fun p => u p * 1) N - (m : ℂ) * primeAverage (fun _ => 1) N)
        from by simp only [mul_one], ← heq]
    simpa only [u, m, circleMean_ofReal, ergodicSequence, Finset.prod_const_one] using hx
  have he : ∀ᶠ N in atTop, primeAverage u N - (m : ℂ) =
      primeAverage u N - (m : ℂ) * primeAverage (fun _ => 1) N :=
    (eventually_ge_atTop 2).mono (fun N hN => by rw [primeAverage_one_of_two_le _ hN, mul_one])
  have hd := (hc.congr' (he.mono (fun _ heN => heN.symm))).add (tendsto_const_nhds (x := (m : ℂ)))
  have hp : Tendsto (primeAverage u) atTop (nhds (m : ℂ)) := by
    simpa only [sub_add_cancel, zero_add] using hd
  simpa [u, primeAverage, ← Complex.ofReal_sum, ← Complex.ofReal_natCast,
    ← Complex.ofReal_div, Function.comp_def] using (Complex.continuous_re.tendsto _).comp hp

/-- Convert the smooth comparison to the centered interval assertion on a
common conull set for the chosen countable approximants. -/
theorem ae_centered_selector_of_smooth_limits
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    (T : ProbabilitySystem X μ) {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ)
    (f : Fin ℓ → X → ℂ) (hf : ∀ i, MemLp (f i) ∞ μ)
    (V : ℤ → ℝ) (J : OpenArc) (h : SmoothPrimeLimit T P V) :
    ∀ᵐ x ∂μ,
      let a := fun p : ℕ => ergodicSequence T P f ((p : ℤ) - 1) x
      Tendsto (fun N => selectedOverPrimes V J a N -
        (J.length : ℂ) * primeAverage a N) atTop (nhds 0) := by
  let tol := fun j : ℕ => (1 : ℝ) / (j + 1 : ℝ)
  have ht j : 0 < tol j := by dsimp [tol]; positivity
  choose l u K hl hu horder hmean hgap using fun j => J.exists_lipschitz_sandwich (ht j)
  obtain ⟨B, hB, hb⟩ := ae_ergodicSequence_bounded T P f hf
  have hp (j : ℕ) := h f hf _ ⟨K j, lipschitz_coe (hl j)⟩
  have hall := ae_all_iff.mpr hp
  filter_upwards [hb, hall] with x hx hxt
  intro a
  simp_rw [selectedOverPrimes_eq_weighted]
  apply centered_primeAverage_of_sandwich a _ J.length B hB (fun p => hx ((p : ℤ) - 1))
  intro ε hε
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hε
  have hj' : tol j < ε := hj
  refine ⟨fun p => l j (V ((p : ℤ) - 1) : Circle),
    fun p => u j (V ((p : ℤ) - 1) : Circle) - l j (V ((p : ℤ) - 1) : Circle),
    ∫ t, l j t ∂AddCircle.haarAddCircle, ∫ t, (u j t - l j t) ∂AddCircle.haarAddCircle,
    ?_, ?_, ((hmean j).trans hj').le, ((hgap j).trans hj').le, ?_, ?_⟩
  · intro p
    rw [← J.circleIndicator_coe]
    exact (horder j _).2.1
  · intro p
    rw [← J.circleIndicator_coe]
    have hle := (horder j (V ((p : ℤ) - 1) : Circle)).2.2.1
    simpa only [add_sub_cancel] using hle
  · simpa only [primeAverage_centered_fun, circleMean_ofReal] using hxt j
  · exact real_primeAverage_tendsto_of_smooth T P V h
      (fun t => u j t - l j t) ((hu j).sub (hl j))

/-- The normalized convergence deduction in Theorem 1.4. The open analytic
input in the current project is the family of smooth prime comparisons. -/
theorem pointwise_of_smooth_limits
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    (T : ProbabilitySystem X μ) {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ)
    (f : Fin ℓ → X → ℂ) (hf : ∀ i, MemLp (f i) ∞ μ)
    (V : ℤ → ℝ) (J : OpenArc) (h : SmoothPrimeLimit T P V)
    (hu : ∀ᵐ x ∂μ, ∃ L : ℂ,
      Tendsto (primeAverage (fun p => ergodicSequence T P f ((p : ℤ) - 1) x))
        atTop (nhds L)) :
    PrimePointwiseConclusion T P f V J := by
  have hall := ae_centered_selector_of_smooth_limits T P (fun _ _ => 1)
    (fun _ => memLp_const 1) V J h
  obtain ⟨x, hx⟩ := hall.exists
  have hc : Tendsto (fun N => (primeDensityRatio V J N : ℂ) -
      (J.length : ℂ) * primeAverage (fun _ => 1) N) atTop (nhds 0) := by
    simpa only [ergodicSequence, Finset.prod_const_one, selectedOverPrimes_one] using hx
  have he : ∀ᶠ N in atTop, (primeDensityRatio V J N : ℂ) - (J.length : ℂ) =
      (primeDensityRatio V J N : ℂ) - (J.length : ℂ) * primeAverage (fun _ => 1) N :=
    (eventually_ge_atTop 2).mono (fun N hN => by rw [primeAverage_one_of_two_le _ hN, mul_one])
  have hd := (hc.congr' (he.mono (fun _ heN => heN.symm))).add (tendsto_const_nhds (x := (J.length : ℂ)))
  have hcomplex : Tendsto (fun N => (primeDensityRatio V J N : ℂ)) atTop (nhds (J.length : ℂ)) := by
    simpa only [sub_add_cancel, zero_add] using hd
  have hr : Tendsto (primeDensityRatio V J) atTop (nhds J.length) := by
    simpa [Function.comp_def] using (Complex.continuous_re.tendsto _).comp hcomplex
  exact pointwise_of_centered_selector T P f V J hr hu
    (ae_centered_selector_of_smooth_limits T P f hf V J h)

/-- The paper's smooth logarithmic L¹ estimate at the single exponent
needed for pointwise convergence. Its analytic proof is a separate obligation. -/
def SmoothErgodicLogDecay {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (T : ProbabilitySystem X μ) {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ)
    (V : ℤ → ℝ) : Prop :=
  ∀ (f : Fin ℓ → X → ℂ), (∀ i, MemLp (f i) ∞ μ) →
    ∀ F : Circle → ℂ, (∃ K : ℝ≥0, LipschitzWith K F) →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ H : ℕ, 2 ≤ H →
      (∫ x, ‖mangoldtAverage T P f
        (fun n => F (V n : Circle) - circleMean F) H x‖ ∂μ) ≤
          C / (Real.log (H : ℝ))^6

theorem smoothPrimeLimit_of_log_decay
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    (hPNT : PrimeNumberTheorem) (T : ProbabilitySystem X μ)
    {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ) (V : ℤ → ℝ)
    (h : SmoothErgodicLogDecay T P V) :
    SmoothPrimeLimit T P V := by
  intro f hf F hF
  obtain ⟨K, hK⟩ := hF
  obtain ⟨C, hC, he⟩ := h f hf F ⟨K, hK⟩
  obtain ⟨W, hW⟩ := (isCompact_univ (X := Circle)).exists_bound_of_continuousOn
    ((hK.continuous.sub continuous_const : Continuous (fun x => F x - circleMean F)).continuousOn)
  exact ae_primeAverage_tendsto_zero_of_mangoldt_log_decay hPNT T P f hf
    (fun n => F (V n : Circle) - circleMean F) (le_max_right W 0)
    (fun n => (hW _ (Set.mem_univ _)).trans (le_max_left W 0)) hC he

/-- All deductions in Theorem 1.4 after the manuscript's logarithmic L¹
estimate, with the two literature inputs exposed as propositions. The same
normalization deduction applies to other phases once that estimate is supplied. -/
theorem pointwise_of_smooth_log_decay
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    (hPNT : PrimeNumberTheorem) (hMWW : MirekWanWrightPointwise X)
    (T : ProbabilitySystem X μ) {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ)
    (hP : ErgodicPolynomialFamily P) (f : Fin ℓ → X → ℂ)
    (hf : ∀ i, MemLp (f i) ∞ μ) (V : ℤ → ℝ) (J : OpenArc)
    (h : SmoothErgodicLogDecay T P V) :
    PrimePointwiseConclusion T P f V J :=
  pointwise_of_smooth_limits T P f hf V J (smoothPrimeLimit_of_log_decay hPNT T P V h)
    (ae_unrestrictedPrimeAverage_tendsto hPNT hMWW T P hP f hf)

end NilBohr
