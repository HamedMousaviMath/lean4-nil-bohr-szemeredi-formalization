import NilBohr.BracketPointwise
import NilBohr.ErgodicRate

/-!
# The bracket pointwise corollary from the prime-phase estimate

The bracket comparison uses Vinogradov's horizontal prime equidistribution
together with the same Heisenberg phase estimate used for Theorem 1.4.
-/

open MeasureTheory Polynomial
open scoped NNReal

namespace NilBohr

/-- Corollary 1.5 from the upstream Heisenberg estimate in Proposition 6.2
and the explicitly named literature inputs. -/
theorem bracket_pointwise_of_primeLocalPhase
    (X : Type*) [MeasurableSpace X]
    (hV : VinogradovPrimeEquidistribution) (hPNT : PrimeNumberTheorem)
    (hMWW : MirekWanWrightPointwise X) (hTer : TeravainenFixedFamily)
    (hp : ∀ α β : ℝ, BadlyApproximable α → AdmissibleBeta β →
      ∀ d : ℕ, 0 < d → ∀ F : Circle → ℂ,
        (∃ K : ℝ≥0, LipschitzWith K F) → PrimeLocalPhase d (heisenbergPhase α β) F) :
    PrimePointwiseFor X bracketPhase := by
  apply bracket_pointwise_of_heisenberg_log_decay X hV hPNT hMWW
  intro μ _ S d Q hQ α β hα hβ
  exact smoothErgodicLogDecay_of_primeLocalPhase hTer Q hQ
    (heisenbergPhase α β) (hp α β hα hβ) S

end NilBohr
