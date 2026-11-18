import NilBohr.GreenTaoObstructions
import NilBohr.CenteredHeisenbergEstimate
import NilBohr.PrimeLocalProof
import NilBohr.GowersDilation
import NilBohr.GowersOrderComparison
import NilBohr.LipschitzFourier
import NilBohr.PrimeCountingNormalization
import NilBohr.PrimeDistributionFromModel
import NilBohr.SeparatingExample
import NilBohr.WeakRegularity

/-! Assemble the recurrence and prime-phase bundles directly from the
literature, with the specialized chart obstructions derived in Lean. -/

namespace NilBohr

open Filter
open scoped Topology BigOperators NNReal

/-- The triangle inequality and the normalized mean bound on integer intervals. -/
theorem NormalizedGowersLaws.checked {S : ℕ} (hS : 1 ≤ S) : NormalizedGowersLaws S :=
  .of_triangle_and_adjacent hS
    (fun L U hLU f g => normalizedGowers_triangle L U S hS hLU f g)
    normalizedGowersAdjacentMonotonicity

/-- Assemble the recurrence inputs from the named source statements, using
the checked scalar specialization of Green–Tao. -/
theorem SelectorLiteratureInputs.of_quantitativeLeibman {c₀ : ℝ}
    (hBanks : BanksRealZeroBound) (hAmbient : KMTTAmbientPrimeModel c₀)
    (hDilation : KMTTNormalizedDilation) (hCramer : KMTTRelativeCramer c₀)
    (hInverse : KMTTLocalInverse) (hWeighted : KMTTWeightedGowers)
    (hAdjacent : NormalizedGowersAdjacentMonotonicity)
    (hTriangle : ∀ (S : ℕ) (L U : ℤ), 2 ≤ S → L ≤ U → ∀ f g : ℤ → ℂ,
      normalizedGowers S L U (fun n => f n + g n) ≤
        normalizedGowers S L U f + normalizedGowers S L U g)
    (hBernstein : BernsteinCircleLipschitzFourier) (hGT : GreenTaoQuantitativeLeibman) :
    SelectorLiteratureInputs c₀ :=
  ⟨hBanks, hAmbient, hDilation, hCramer, hInverse, hWeighted, hAdjacent, hTriangle,
    hBernstein, scalarHeisenbergObstruction_of_greenTao hGT⟩

/-- Assemble the inputs to Proposition 6.2 using the two checked Green–Tao
specializations. -/
theorem PrimePhaseLiteratureInputs.of_quantitativeLeibman {c₀ : ℝ}
    (hBanks : BanksRealZeroBound) (hAmbient : KMTTAmbientPrimeModel c₀)
    (hGowers : ∀ S, 3 ≤ S → NormalizedGowersLaws S)
    (hBernstein : BernsteinCircleLipschitzFourier)
    (hMertens : MertensIntervalProductBound) (hSieve : FundamentalSieveLemma)
    (hGT : GreenTaoQuantitativeLeibman) : PrimePhaseLiteratureInputs c₀ :=
  ⟨hBanks, hAmbient, hGowers, hBernstein, hMertens, hSieve,
    scalarHeisenbergObstruction_of_greenTao hGT, productHeisenbergObstruction_of_greenTao hGT⟩

/-- The recurrence bundle with the interval Gowers and Fourier estimates supplied. -/
theorem SelectorLiteratureInputs.of_analytic_inputs {c₀ : ℝ}
    (hBanks : BanksRealZeroBound) (hAmbient : KMTTAmbientPrimeModel c₀)
    (hCramer : KMTTRelativeCramer c₀) (hInverse : KMTTLocalInverse)
    (hWeighted : KMTTWeightedGowers) (hGT : GreenTaoQuantitativeLeibman) :
    SelectorLiteratureInputs c₀ :=
  .of_quantitativeLeibman hBanks hAmbient kmttNormalizedDilation hCramer hInverse hWeighted
    normalizedGowersAdjacentMonotonicity
    (fun S L U hS hLU f g => normalizedGowers_triangle L U S (by omega) hLU f g)
    bernsteinCircleLipschitzFourier hGT

/-- The prime-phase bundle with the interval Gowers and Fourier estimates supplied. -/
theorem PrimePhaseLiteratureInputs.of_analytic_inputs {c₀ : ℝ}
    (hBanks : BanksRealZeroBound) (hAmbient : KMTTAmbientPrimeModel c₀)
    (hMertens : MertensIntervalProductBound) (hSieve : FundamentalSieveLemma)
    (hGT : GreenTaoQuantitativeLeibman) : PrimePhaseLiteratureInputs c₀ :=
  .of_quantitativeLeibman hBanks hAmbient (fun _ hS => NormalizedGowersLaws.checked (by omega))
    bernsteinCircleLipschitzFourier hMertens hSieve hGT

/-- Proposition 4.1 from the prime-model and zero-exclusion inputs. -/
theorem high_order_relative_prime_of_analytic_inputs {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hc₁ : c₀ < 1 / 11) (hBanks : BanksRealZeroBound)
    (hAmbient : KMTTAmbientPrimeModel c₀) (hRelative : KMTTRelativeCramer c₀)
    {d S : ℕ} (hd : 0 < d) (hS : 2 ≤ S) : HighOrderRelativePrimeUniformity c₀ d S :=
  high_order_relative_prime_of_kmtt hc₀ hc₁ hBanks hAmbient kmttNormalizedDilation hRelative
    hd hS (NormalizedGowersLaws.checked (by omega))

/-- Theorem 1.2 from the prime-model, inverse, weighted count and Leibman inputs. -/
theorem heisenbergRecurrence_of_analytic_inputs {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hc₁ : c₀ < 1/11) (hBanks : BanksRealZeroBound) (hAmbient : KMTTAmbientPrimeModel c₀)
    (hCramer : KMTTRelativeCramer c₀) (hInverse : KMTTLocalInverse)
    (hWeighted : KMTTWeightedGowers) (hGT : GreenTaoQuantitativeLeibman) : HeisenbergRecurrence :=
  heisenbergRecurrence_of_obstructions hc₀ hc₁
    (.of_analytic_inputs hBanks hAmbient hCramer hInverse hWeighted hGT)
    hInverse.toLocalWeakRegularity (productHeisenbergObstruction_of_greenTao hGT)

/-- Corollary 1.3 from the same inputs as Theorem 1.2. -/
theorem bracketRecurrence_of_analytic_inputs {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hc₁ : c₀ < 1/11) (hBanks : BanksRealZeroBound) (hAmbient : KMTTAmbientPrimeModel c₀)
    (hCramer : KMTTRelativeCramer c₀) (hInverse : KMTTLocalInverse)
    (hWeighted : KMTTWeightedGowers) (hGT : GreenTaoQuantitativeLeibman) : BracketRecurrence :=
  bracket_recurrence_of_heisenberg_recurrence
    (heisenbergRecurrence_of_analytic_inputs hc₀ hc₁ hBanks hAmbient hCramer hInverse hWeighted hGT)

/-- Lemma 4.5 under its mathematical hypotheses. -/
theorem localized_vertical_multiplier
    (L U : ℤ) (hLU : L ≤ U) (S : ℕ) (hS : 3 ≤ S)
    (χ : C(Circle, ℂ)) (K : ℝ≥0) (hLip : LipschitzWith K χ)
    (lo hi : ℝ) (hshort : 2*(hi-lo) < 1)
    (hχ : ∀ x : ℝ, x ∈ Set.Ico (0 : ℝ) 1 → χ (x : Circle) ≠ 0 → x ∈ Set.Icc lo hi)
    (α β : ℝ) (a v h : ℤ) (f : ℤ → ℂ) :
    normalizedGowers S L U (fun t =>
      f t * χ ((β*((a+v*t : ℤ) : ℝ) : ℝ) : Circle) *
        phaseExponential ((h : ℝ)*heisenbergPhase α β (a+v*t))) ≤
      (∑' k : ℤ, ‖fourierCoeff χ k‖) * normalizedGowers S L U f :=
  localized_vertical_multiplier_of_bernstein bernsteinCircleLipschitzFourier L U hLU S hS
    (NormalizedGowersLaws.checked (by omega)) χ K hLip lo hi hshort hχ α β a v h f

/-- Proposition A.1 from Green–Tao quantitative Leibman. -/
theorem appendixA_separating_family_of_quantitativeLeibman
    (hGT : GreenTaoQuantitativeLeibman) {α β : ℝ}
    (hα : BadlyApproximable α) (hβ : AdmissibleBeta β)
    (F : Circle → ℂ) {κ : ℝ≥0} (hF : LipschitzWith κ F)
    (hNonconstant : ∃ x y : Circle, F x ≠ F y) :
    ∃ r w q M : ℕ → ℕ, AdmissibleBetaDenominators β r ∧
      SeparatingFamilyClaims α β F r w q M :=
  appendixA_separating_family (productHeisenbergObstruction_of_greenTao hGT)
    (scalarHeisenbergObstruction_of_greenTao hGT) bernsteinCircleLipschitzFourier
    (fun _ hS => NormalizedGowersLaws.checked (by omega)) hα hβ F hF hNonconstant

/-- Theorem 1.4 from the prime-phase literature inputs and the theta asymptotic. -/
theorem heisenberg_pointwise_of_analytic_inputs
    (X : Type*) [MeasurableSpace X] {c₀ : ℝ} (hc₀ : 0 < c₀) (hc₁ : c₀ < 1/11)
    (hBanks : BanksRealZeroBound) (hAmbient : KMTTAmbientPrimeModel c₀)
    (hMertens : MertensIntervalProductBound) (hSieve : FundamentalSieveLemma)
    (hGT : GreenTaoQuantitativeLeibman)
    (hθ : Tendsto (fun n : ℕ => (∑ p ∈ primesThrough n, Real.log (p : ℝ)) /
      (n : ℝ)) atTop (𝓝 1))
    (hMWW : MirekWanWrightPointwise X) (hTer : TeravainenFixedFamily) :
    PrimePointwiseFor X heisenbergPhase :=
  heisenberg_pointwise_of_literature X hc₀ hc₁
    (.of_analytic_inputs hBanks hAmbient hMertens hSieve hGT)
    (PrimeNumberTheorem.of_theta hθ) hMWW hTer

/-- Corollary 1.5 with the same inputs and Vinogradov equidistribution. -/
theorem bracket_pointwise_of_analytic_inputs
    (X : Type*) [MeasurableSpace X] {c₀ : ℝ} (hc₀ : 0 < c₀) (hc₁ : c₀ < 1/11)
    (hBanks : BanksRealZeroBound) (hAmbient : KMTTAmbientPrimeModel c₀)
    (hMertens : MertensIntervalProductBound) (hSieve : FundamentalSieveLemma)
    (hGT : GreenTaoQuantitativeLeibman) (hV : VinogradovPrimeEquidistribution)
    (hθ : Tendsto (fun n : ℕ => (∑ p ∈ primesThrough n, Real.log (p : ℝ)) /
      (n : ℝ)) atTop (𝓝 1))
    (hMWW : MirekWanWrightPointwise X) (hTer : TeravainenFixedFamily) :
    PrimePointwiseFor X bracketPhase :=
  bracket_pointwise_of_literature X hc₀ hc₁
    (.of_analytic_inputs hBanks hAmbient hMertens hSieve hGT) hV
    (PrimeNumberTheorem.of_theta hθ) hMWW hTer

/-- Theorem 1.4 with prime normalization derived from the existing
prime-model and sieve premises. -/
theorem heisenberg_pointwise_of_prime_model
    (X : Type*) [MeasurableSpace X] {c₀ : ℝ} (hc₀ : 0 < c₀) (hc₁ : c₀ < 1/11)
    (hBanks : BanksRealZeroBound) (hAmbient : KMTTAmbientPrimeModel c₀)
    (hMertens : MertensIntervalProductBound) (hSieve : FundamentalSieveLemma)
    (hGT : GreenTaoQuantitativeLeibman)
    (hMWW : MirekWanWrightPointwise X) (hTer : TeravainenFixedFamily) :
    PrimePointwiseFor X heisenbergPhase :=
  heisenberg_pointwise_of_literature X hc₀ hc₁
    (.of_analytic_inputs hBanks hAmbient hMertens hSieve hGT)
    (primeNumberTheorem_of_prime_model hc₀ hc₁ hBanks hAmbient hMertens hSieve) hMWW hTer

/-- Corollary 1.5 from the same premises as Theorem 1.4. The prime model
and sieve yield the additional scalar boundary equidistribution. -/
theorem bracket_pointwise_of_prime_model
    (X : Type*) [MeasurableSpace X] {c₀ : ℝ} (hc₀ : 0 < c₀) (hc₁ : c₀ < 1/11)
    (hBanks : BanksRealZeroBound) (hAmbient : KMTTAmbientPrimeModel c₀)
    (hMertens : MertensIntervalProductBound) (hSieve : FundamentalSieveLemma)
    (hGT : GreenTaoQuantitativeLeibman)
    (hMWW : MirekWanWrightPointwise X) (hTer : TeravainenFixedFamily) :
    PrimePointwiseFor X bracketPhase :=
  bracket_pointwise_of_literature X hc₀ hc₁
    (.of_analytic_inputs hBanks hAmbient hMertens hSieve hGT)
    (vinogradov_of_prime_model hc₀ hc₁ hBanks hAmbient hMertens hSieve)
    (primeNumberTheorem_of_prime_model hc₀ hc₁ hBanks hAmbient hMertens hSieve) hMWW hTer

end NilBohr
