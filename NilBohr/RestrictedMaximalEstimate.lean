import NilBohr.RestrictedMaximalDomination

/-! The conditional maximal estimate in the introduction. A positive
unrestricted bound transfers to the selected-prime maximal operator
with one constant determined by the selector density. -/

open Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace NilBohr

/-- The supremum of the absolute selected-prime averages over all cutoffs. -/
noncomputable def selectedPrimeMaximal (V : ℤ → ℝ) (J : OpenArc)
    (a : ℕ → ℂ) : ℝ≥0∞ :=
  ⨆ N : ℕ, ‖selectedPrimeAverage V J a N‖ₑ

/-- The unrestricted maximal expression averages the absolute summands. -/
noncomputable def unrestrictedPositivePrimeMaximal (a : ℕ → ℂ) : ℝ≥0∞ :=
  ⨆ N : ℕ, ENNReal.ofReal
    ((∑ p ∈ primesThrough N, ‖a p‖) / ((primesThrough N).card : ℝ))

/-- The maximal domination constant is uniform in the sequence. The
extended nonnegative reals allow either supremum to be infinite. -/
theorem selectedPrimeMaximal_domination (V : ℤ → ℝ) (J : OpenArc)
    (hDensity : Tendsto (primeDensityRatio V J) atTop (𝓝 J.length)) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ a : ℕ → ℂ,
      selectedPrimeMaximal V J a ≤ (C : ℝ≥0∞) * unrestrictedPositivePrimeMaximal a := by
  obtain ⟨C, hC, hDom⟩ := selectedPrimeAverage_domination V J hDensity
  refine ⟨C.toNNReal, Real.toNNReal_pos.mpr hC, fun a => ?_⟩
  rw [selectedPrimeMaximal, unrestrictedPositivePrimeMaximal, ENNReal.mul_iSup]
  apply iSup_mono
  intro N
  rw [← ofReal_norm_eq_enorm,
    show (C.toNNReal : ℝ≥0∞) = ENNReal.ofReal C from rfl, ← ENNReal.ofReal_mul hC.le]
  exact ENNReal.ofReal_le_ofReal (hDom a N)

/-- A.e. measurability of each summand gives a.e. measurability of the
countable selected supremum, regardless of the representatives chosen. -/
theorem aemeasurable_selectedPrimeMaximal {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (V : ℤ → ℝ) (J : OpenArc) (a : X → ℕ → ℂ)
    (ha : ∀ p : ℕ, AEMeasurable (fun x => a x p) μ) :
    AEMeasurable (fun x => selectedPrimeMaximal V J (a x)) μ := by
  apply AEMeasurable.iSup
  intro N
  unfold selectedPrimeAverage
  exact ((Finset.aemeasurable_sum _ fun p _ => ha p).div aemeasurable_const).enorm

/-- The selected maximal norm is controlled by the unrestricted positive
maximal norm at every exponent, including `∞`. Consequently any bound
for the latter transfers with the same exponents. -/
theorem eLpNorm_selectedPrimeMaximal_le {X : Type*} [MeasurableSpace X]
    (V : ℤ → ℝ) (J : OpenArc)
    (hDensity : Tendsto (primeDensityRatio V J) atTop (𝓝 J.length)) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ (μ : Measure X) (p : ℝ≥0∞) (a : X → ℕ → ℂ),
      eLpNorm (fun x => selectedPrimeMaximal V J (a x)) p μ ≤
        (C : ℝ≥0∞) * eLpNorm (fun x => unrestrictedPositivePrimeMaximal (a x)) p μ := by
  obtain ⟨C, hC, hDom⟩ := selectedPrimeMaximal_domination V J hDensity
  refine ⟨C, hC, fun μ p a => ?_⟩
  apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul' (c := C) _ p
  exact Eventually.of_forall (fun x => by simpa only [enorm_eq_self] using hDom (a x))

/-- Finiteness of the unrestricted positive maximal norm gives `MemLp`
for the selected operator on a.e. measurable summands. -/
theorem memLp_selectedPrimeMaximal {X : Type*} [MeasurableSpace X] {μ : Measure X} {p : ℝ≥0∞}
    (V : ℤ → ℝ) (J : OpenArc)
    (hDensity : Tendsto (primeDensityRatio V J) atTop (𝓝 J.length))
    (a : X → ℕ → ℂ) (ha : ∀ n : ℕ, AEMeasurable (fun x => a x n) μ)
    (hUnrestricted : eLpNorm (fun x => unrestrictedPositivePrimeMaximal (a x)) p μ < ∞) :
    MemLp (fun x => selectedPrimeMaximal V J (a x)) p μ := by
  obtain ⟨_, _, hDom⟩ := eLpNorm_selectedPrimeMaximal_le (X := X) V J hDensity
  exact ⟨(aemeasurable_selectedPrimeMaximal V J a ha).aestronglyMeasurable,
    (hDom μ p a).trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hUnrestricted)⟩

/-- The conditional transfer for the polynomial ergodic summands in the
manuscript. The functions may be arbitrary a.e. measurable representatives. -/
theorem memLp_selectedErgodicPrimeMaximal {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {p : ℝ≥0∞} (T : ProbabilitySystem X μ) {ℓ : ℕ}
    (P : Fin ℓ → Polynomial ℤ) (f : Fin ℓ → X → ℂ)
    (hf : ∀ i, AEMeasurable (f i) μ) (V : ℤ → ℝ) (J : OpenArc)
    (hDensity : Tendsto (primeDensityRatio V J) atTop (𝓝 J.length))
    (hUnrestricted : eLpNorm (fun x => unrestrictedPositivePrimeMaximal
      (fun n => ergodicSequence T P f ((n : ℤ) - 1) x)) p μ < ∞) :
    MemLp (fun x => selectedPrimeMaximal V J
      (fun n => ergodicSequence T P f ((n : ℤ) - 1) x)) p μ := by
  apply memLp_selectedPrimeMaximal V J hDensity _ _ hUnrestricted
  intro n
  apply Finset.aemeasurable_prod
  intro i _
  exact (hf i).comp_quasiMeasurePreserving
    (T.preserves ((P i).eval ((n : ℤ) - 1))).quasiMeasurePreserving

/-- Changing the representatives of the inputs changes the selected
maximal function only on a null set. -/
theorem selectedErgodicPrimeMaximal_congr_ae {X : Type*} [MeasurableSpace X]
    {μ : Measure X} (T : ProbabilitySystem X μ) {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ)
    (f g : Fin ℓ → X → ℂ) (hfg : ∀ i, f i =ᵐ[μ] g i)
    (V : ℤ → ℝ) (J : OpenArc) :
    (fun x => selectedPrimeMaximal V J (fun n : ℕ => ergodicSequence T P f ((n : ℤ) - 1) x))
      =ᵐ[μ]
    (fun x => selectedPrimeMaximal V J (fun n : ℕ => ergodicSequence T P g ((n : ℤ) - 1) x)) := by
  have hterms : ∀ᵐ x ∂μ, ∀ (n : ℕ) (i : Fin ℓ),
      f i ((T.transform ^ (P i).eval ((n : ℤ) - 1)) x) =
        g i ((T.transform ^ (P i).eval ((n : ℤ) - 1)) x) :=
    ae_all_iff.mpr (fun n => ae_all_iff.mpr (fun i =>
      (T.preserves ((P i).eval ((n : ℤ) - 1))).quasiMeasurePreserving.ae (hfg i)))
  filter_upwards [hterms] with x hx
  have hx' : (fun n : ℕ => ergodicSequence T P f ((n : ℤ) - 1) x) =
      (fun n : ℕ => ergodicSequence T P g ((n : ℤ) - 1) x) := funext fun n =>
    Finset.prod_congr rfl (fun i _ => hx n i)
  rw [hx']

end NilBohr
