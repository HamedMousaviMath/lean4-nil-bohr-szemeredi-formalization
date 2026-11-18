import NilBohr.AmbientPrimeMean
import NilBohr.CramerModelMean
import NilBohr.CramerLinearCancellation
import NilBohr.PrimeLinearEquidistribution

/-! Ordinary prime normalization from the prime model and sieve estimates
used in the manuscript's prime-phase comparison. -/

namespace NilBohr

/-- The ambient prime model and the dimension-one sieve inputs used for the
prime-phase estimate already imply the ordinary prime number theorem. -/
theorem primeNumberTheorem_of_prime_model {c₀ : ℝ} (hc₀ : 0 < c₀) (hc₁ : c₀ < 1/11)
    (hBanks : BanksRealZeroBound) (hAmbient : KMTTAmbientPrimeModel c₀)
    (hMertens : MertensIntervalProductBound) (hSieve : FundamentalSieveLemma) :
    PrimeNumberTheorem :=
  primeNumberTheorem_of_cramer_mean hc₀ hc₁ hBanks hAmbient
    (tendsto_cramerWeight_mean hc₀ (by linarith) hMertens hSieve)

/-- Vinogradov's irrational linear prime equidistribution interface follows
from the same prime-model and sieve estimates used for prime normalization. -/
theorem vinogradov_of_prime_model {c₀ : ℝ} (hc₀ : 0 < c₀) (hc₁ : c₀ < 1/11)
    (hBanks : BanksRealZeroBound) (hAmbient : KMTTAmbientPrimeModel c₀)
    (hMertens : MertensIntervalProductBound) (hSieve : FundamentalSieveLemma) :
    VinogradovPrimeEquidistribution :=
  vinogradov_of_prime_linear_modes fun α hα =>
    prime_linear_mode_tendsto_of_model hc₀ hc₁ hBanks hAmbient
      (primeNumberTheorem_of_prime_model hc₀ hc₁ hBanks hAmbient hMertens hSieve) α
      (tendsto_cramer_linear_mean hc₀ (by linarith) hMertens hSieve hα)

end NilBohr
