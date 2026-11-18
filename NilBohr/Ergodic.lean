import NilBohr.Counting

/-! Prime averages on an invertible probability system, and the final
normalization deduction. -/

open scoped BigOperators ENNReal NNReal
open Filter MeasureTheory Polynomial

namespace NilBohr

def primesThrough (N : ℕ) : Finset ℕ := (Finset.range (N + 1)).filter Nat.Prime

noncomputable def primesSelectedThrough (V : ℤ → ℝ) (J : OpenArc) (N : ℕ) : Finset ℕ := by
  classical
  exact (primesThrough N).filter (fun p => J.Contains (V ((p : ℤ) - 1)))

noncomputable def primeDensityRatio (V : ℤ → ℝ) (J : OpenArc) (N : ℕ) : ℝ :=
  ((primesSelectedThrough V J N).card : ℝ) / (primesThrough N).card

noncomputable def primeAverage (a : ℕ → ℂ) (N : ℕ) : ℂ :=
  (∑ p ∈ primesThrough N, a p) / ((primesThrough N).card : ℂ)

noncomputable def selectedOverPrimes (V : ℤ → ℝ) (J : OpenArc)
    (a : ℕ → ℂ) (N : ℕ) : ℂ :=
  (∑ p ∈ primesSelectedThrough V J N, a p) / ((primesThrough N).card : ℂ)

noncomputable def selectedPrimeAverage (V : ℤ → ℝ) (J : OpenArc)
    (a : ℕ → ℂ) (N : ℕ) : ℂ :=
  (∑ p ∈ primesSelectedThrough V J N, a p) /
    ((primesSelectedThrough V J N).card : ℂ)

theorem selectedPrimeAverage_eq_div_ratio (V : ℤ → ℝ) (J : OpenArc)
    (a : ℕ → ℂ) (N : ℕ) :
    selectedPrimeAverage V J a N =
      selectedOverPrimes V J a N / (primeDensityRatio V J N : ℂ) := by
  have hsubset : primesSelectedThrough V J N ⊆ primesThrough N := by
    classical
    exact Finset.filter_subset _ _
  by_cases h : (primesThrough N).card = 0
  · have hs : (primesSelectedThrough V J N).card = 0 :=
      Nat.eq_zero_of_le_zero (h ▸ Finset.card_le_card hsubset)
    simp [selectedPrimeAverage, selectedOverPrimes, primeDensityRatio, h, hs]
  · have hc : ((primesThrough N).card : ℂ) ≠ 0 := by exact_mod_cast h
    simp only [selectedPrimeAverage, selectedOverPrimes, primeDensityRatio,
      Complex.ofReal_div, Complex.ofReal_natCast, div_div_div_cancel_right₀ hc]

theorem selectedOverPrimes_eq_weighted (V : ℤ → ℝ) (J : OpenArc)
    (a : ℕ → ℂ) (N : ℕ) :
    selectedOverPrimes V J a N =
      primeAverage (fun p => (J.indicator (V ((p : ℤ) - 1)) : ℂ) * a p) N := by
  classical
  unfold selectedOverPrimes primesSelectedThrough primeAverage
  rw [Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  by_cases h : J.Contains (V ((p : ℤ) - 1)) <;> simp [OpenArc.indicator, h]

theorem selectedOverPrimes_one (V : ℤ → ℝ) (J : OpenArc) (N : ℕ) :
    selectedOverPrimes V J (fun _ => 1) N = (primeDensityRatio V J N : ℂ) := by
  simp [selectedOverPrimes, primeDensityRatio]

/-- The system is specified by the invertible transformation itself.
Preservation for its integer iterates is supplied as a field. -/
structure ProbabilitySystem (X : Type*) [MeasurableSpace X] (μ : Measure X) where
  transform : Equiv.Perm X
  preserves : ∀ n : ℤ, MeasurePreserving (fun x => (transform ^ n) x) μ μ

/-- A measure-preserving measurable equivalence gives the paper's system,
including negative iterates. -/
def ProbabilitySystem.ofMeasurableEquiv {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ) : ProbabilitySystem X μ := by
  have hp (g : Equiv.Perm X) (hg : MeasurePreserving g μ μ) (n : ℕ) :
      MeasurePreserving (fun x => (g ^ n) x) μ μ := by
    induction n with
    | zero => simpa using MeasurePreserving.id μ
    | succ n ih =>
      simpa only [pow_succ, Equiv.Perm.mul_apply, Function.comp_apply] using ih.comp hg
  refine ⟨e.toEquiv, ?_⟩
  intro n
  cases n with
  | ofNat n =>
    simpa only [Int.ofNat_eq_coe, zpow_natCast] using hp e.toEquiv he n
  | negSucc n =>
    rw [zpow_negSucc, ← inv_pow]
    exact hp e.symm.toEquiv (he.symm e) (n + 1)

def ergodicSequence {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (T : ProbabilitySystem X μ) {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ)
    (f : Fin ℓ → X → ℂ) (n : ℤ) (x : X) : ℂ :=
  ∏ i, f i ((T.transform ^ (P i).eval n) x)

def ErgodicPolynomialFamily {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ) : Prop :=
  0 < ℓ ∧ (∀ i, 0 < (P i).natDegree ∧ (P i).coeff 0 = 0) ∧
    StrictMono (fun i => (P i).natDegree)

noncomputable def mangoldtAverage {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (T : ProbabilitySystem X μ) {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ)
    (f : Fin ℓ → X → ℂ) (w : ℤ → ℂ) (H : ℕ) (x : X) : ℂ :=
  (∑ n ∈ positiveInterval H,
    (ArithmeticFunction.vonMangoldt (n + 1).toNat : ℂ) * w n *
      ergodicSequence T P f n x) / (H : ℂ)

noncomputable def circleMean (F : Circle → ℂ) : ℂ :=
  ∫ t, F t ∂AddCircle.haarAddCircle

/-- Exact pointwise conclusion, written for either real-valued phase. -/
def PrimePointwiseConclusion {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (T : ProbabilitySystem X μ) {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ)
    (f : Fin ℓ → X → ℂ) (V : ℤ → ℝ) (J : OpenArc) : Prop :=
  Tendsto (primeDensityRatio V J) atTop (nhds J.length) ∧
  ∀ᵐ x ∂μ, ∃ L : ℂ,
    Tendsto (primeAverage (fun p => ergodicSequence T P f ((p : ℤ) - 1) x))
      atTop (nhds L) ∧
    Tendsto (selectedPrimeAverage V J (fun p => ergodicSequence T P f ((p : ℤ) - 1) x))
      atTop (nhds L)

/-- Theorem 1.4 for any probability space at the current universe. Substituting
the bracket phase specifies Corollary 1.5. -/
def PrimePointwiseFor (X : Type*) [MeasurableSpace X]
    (phaseFamily : ℝ → ℝ → ℤ → ℝ) : Prop :=
  ∀ (μ : Measure X) [IsProbabilityMeasure μ] (T : ProbabilitySystem X μ)
    {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ), ErgodicPolynomialFamily P →
    ∀ (f : Fin ℓ → X → ℂ), (∀ i, MemLp (f i) ∞ μ) →
    ∀ (α β : ℝ), BadlyApproximable α → AdmissibleBeta β → ∀ J : OpenArc,
      PrimePointwiseConclusion T P f (phaseFamily α β) J

/-- Normalization and identification of the limit in Theorem 1.4 and
Corollary 1.5. The centered interval comparison and unrestricted convergence
are the inputs to this deduction. -/
theorem pointwise_of_centered_selector {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (T : ProbabilitySystem X μ) {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ)
    (f : Fin ℓ → X → ℂ) (V : ℤ → ℝ) (J : OpenArc)
    (hr : Tendsto (primeDensityRatio V J) atTop (nhds J.length))
    (hu : ∀ᵐ x ∂μ, ∃ L : ℂ,
      Tendsto (primeAverage (fun p => ergodicSequence T P f ((p : ℤ) - 1) x))
        atTop (nhds L))
    (hc : ∀ᵐ x ∂μ,
      let a := fun p : ℕ => ergodicSequence T P f ((p : ℤ) - 1) x
      Tendsto (fun N => selectedOverPrimes V J a N -
        (J.length : ℂ) * primeAverage a N) atTop (nhds 0)) :
    PrimePointwiseConclusion T P f V J := by
  refine ⟨hr, ?_⟩
  filter_upwards [hu, hc] with x hx hxc
  obtain ⟨L, hL⟩ := hx
  refine ⟨L, hL, ?_⟩
  let a := fun p : ℕ => ergodicSequence T P f ((p : ℤ) - 1) x
  have hsum : Tendsto (selectedOverPrimes V J a) atTop (nhds ((J.length : ℂ) * L)) := by
    have hadd := hxc.add ((tendsto_const_nhds (x := (J.length : ℂ))).mul hL)
    simpa only [sub_add_cancel, zero_add] using hadd
  have hratio : Tendsto (fun N => (primeDensityRatio V J N : ℂ)) atTop
      (nhds (J.length : ℂ)) := (Complex.continuous_ofReal.tendsto J.length).comp hr
  have hj : (J.length : ℂ) ≠ 0 := by exact_mod_cast J.length_pos.ne'
  have hd := hsum.div hratio hj
  convert hd using 1
  · exact funext (selectedPrimeAverage_eq_div_ratio V J a)
  · rw [mul_comm, mul_div_cancel_right₀ _ hj]

/-- Pointwise domination of the average by a uniform bound on the summands. -/
theorem norm_primeAverage_le (a : ℕ → ℂ) (N : ℕ) (B : ℝ)
    (hB : 0 ≤ B) (ha : ∀ p, ‖a p‖ ≤ B) :
    ‖primeAverage a N‖ ≤ B := by
  unfold primeAverage
  have h := norm_weighted_sum_div_le (primesThrough N) a (fun _ => 1) (fun _ => 1)
    ((primesThrough N).card : ℝ) B (Nat.cast_nonneg _) hB (by simp) (fun p _ => ha p)
  by_cases he : (primesThrough N).card = 0
  · simp [he, hB]
  · have hc : ((primesThrough N).card : ℝ) ≠ 0 := by exact_mod_cast he
    simpa [hc] using h

/-- A scalar upper gap controls the error incurred by using a lower
selector. No convergence of the complex test sequence is required. -/
theorem norm_primeAverage_sub_le_gap (a : ℕ → ℂ) (N : ℕ)
    (u l gap : ℕ → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (ha : ∀ p, ‖a p‖ ≤ B)
    (hl : ∀ p, l p ≤ u p) (hg : ∀ p, u p ≤ l p + gap p) :
    ‖primeAverage (fun p => (u p : ℂ) * a p) N -
      primeAverage (fun p => (l p : ℂ) * a p) N‖ ≤
      B * ((∑ p ∈ primesThrough N, gap p) / (primesThrough N).card) := by
  have h := norm_weighted_sum_div_le (primesThrough N) a (fun p => u p - l p) gap
    ((primesThrough N).card : ℝ) B (Nat.cast_nonneg _) hB
    (fun p _ => by rw [abs_of_nonneg (sub_nonneg.mpr (hl p))]; linarith [hg p])
    (fun p _ => ha p)
  simpa [primeAverage, Complex.ofReal_natCast, Complex.ofReal_sub, sub_mul,
    Finset.sum_sub_distrib, sub_div] using h

/-- The smoothing argument for a fixed test sequence. The hypotheses provide
lower weights and nonnegative scalar gaps at arbitrarily small mean error. -/
theorem centered_primeAverage_of_sandwich (a : ℕ → ℂ) (u : ℕ → ℝ) (m B : ℝ)
    (hB : 0 ≤ B) (ha : ∀ p, ‖a p‖ ≤ B)
    (happrox : ∀ ε : ℝ, 0 < ε →
      ∃ (l gap : ℕ → ℝ) (mₗ m₉ : ℝ),
        (∀ p, l p ≤ u p) ∧ (∀ p, u p ≤ l p + gap p) ∧
        |mₗ - m| ≤ ε ∧ m₉ ≤ ε ∧
        Tendsto (fun N => primeAverage (fun p => (l p : ℂ) * a p) N -
          (mₗ : ℂ) * primeAverage a N) atTop (nhds 0) ∧
        Tendsto (fun N => (∑ p ∈ primesThrough N, gap p) /
          ((primesThrough N).card : ℝ)) atTop (nhds m₉)) :
    Tendsto (fun N => primeAverage (fun p => (u p : ℂ) * a p) N -
      (m : ℂ) * primeAverage a N) atTop (nhds 0) := by
  apply Metric.tendsto_atTop.mpr
  intro η hη
  let ε := η / (8 * (B + 1))
  have hε : 0 < ε := div_pos hη (by positivity)
  obtain ⟨l, gap, ml, mg, hl, hg, hm, hmg, ht, hgt⟩ := happrox ε hε
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.mp ht (η / 3) (by positivity)
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp hgt ε hε
  refine ⟨max N₀ N₁, fun N hN => ?_⟩
  have hL := hN₀ N ((le_max_left _ _).trans hN)
  rw [dist_zero_right] at hL ⊢
  have hG := hN₁ N ((le_max_right _ _).trans hN)
  rw [Real.dist_eq] at hG
  have hG' : (∑ p ∈ primesThrough N, gap p) / (primesThrough N).card ≤ 2 * ε := by
    linarith [le_abs_self ((∑ p ∈ primesThrough N, gap p) / (primesThrough N).card - mg)]
  have hscale : B * ε ≤ η / 8 := by
    dsimp [ε]
    rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith
  let U := primeAverage (fun p => (u p : ℂ) * a p) N
  let V := primeAverage (fun p => (l p : ℂ) * a p) N
  let A := primeAverage a N
  change ‖U - (m : ℂ) * A‖ < η
  have hUV : ‖U - V‖ ≤ B * (2 * ε) :=
    (norm_primeAverage_sub_le_gap a N u l gap B hB ha hl hg).trans
      (mul_le_mul_of_nonneg_left hG' hB)
  have hmean : ‖((ml : ℂ) - m) * A‖ ≤ ε * B := by
    have hc : ‖(ml : ℂ) - m‖ = |ml - m| := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [norm_mul, hc]
    exact mul_le_mul hm (norm_primeAverage_le a N B hB ha) (norm_nonneg A) hε.le
  have hsplit : U - (m : ℂ) * A = (U - V) + (V - (ml : ℂ) * A) +
      ((ml : ℂ) - m) * A := by ring
  rw [hsplit]
  have htri := (norm_add_le ((U - V) + (V - (ml : ℂ) * A)) (((ml : ℂ) - m) * A)).trans
    (add_le_add_right (norm_add_le (U - V) (V - (ml : ℂ) * A)) _)
  change ‖V - (ml : ℂ) * A‖ < η / 3 at hL
  nlinarith [htri]

/-- Essential boundedness gives one conull set valid at every iterate of
the transformation and for every member of the finite family. -/
theorem ae_ergodicSequence_bounded {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (T : ProbabilitySystem X μ) {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ)
    (f : Fin ℓ → X → ℂ) (hf : ∀ i, MemLp (f i) ∞ μ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᵐ x ∂μ, ∀ n : ℤ, ‖ergodicSequence T P f n x‖ ≤ B := by
  have he (i : Fin ℓ) : ∃ C : ℝ≥0, ∀ᵐ x ∂μ, ‖f i x‖₊ ≤ C :=
    eLpNormEssSup_lt_top_iff_isBoundedUnder.mp (by simpa [eLpNorm_exponent_top] using (hf i).2)
  choose C hC using he
  refine ⟨∏ i, (C i : ℝ), Finset.prod_nonneg (fun i _ => (C i).coe_nonneg), ?_⟩
  have ht (i : Fin ℓ) (m : ℤ) : ∀ᵐ x ∂μ, ‖f i ((T.transform ^ m) x)‖₊ ≤ C i :=
    (T.preserves m).quasiMeasurePreserving.ae (hC i)
  have hh : ∀ᵐ x ∂μ, ∀ (i : Fin ℓ) (m : ℤ), ‖f i ((T.transform ^ m) x)‖₊ ≤ C i := by
    exact ae_all_iff.mpr (fun i => ae_all_iff.mpr (ht i))
  filter_upwards [hh] with x hx n
  rw [ergodicSequence, norm_prod]
  exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => hx i ((P i).eval n))

end NilBohr
