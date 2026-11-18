import NilBohr.GowersProgression
import NilBohr.PrimeCountingNormalization
import NilBohr.TwistedOrbit

/-! At the ambient scale, the Gowers prime-model estimate controls means
against polynomial phases of smaller degree. The constant phase yields
the Mangoldt form of the prime number theorem once the model mean is known. -/

namespace NilBohr

open Filter Polynomial
open scoped Topology BigOperators

/-- At every sufficiently large scale, every polynomial test of degree
less than the specified Gowers order has the same logarithmic saving. -/
theorem ambient_prime_polynomial_test_error_tendsto {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hc₁ : c₀ < 1/11) (hBanks : BanksRealZeroBound)
    (hAmbient : KMTTAmbientPrimeModel c₀) {S : ℕ} (hS : 2 ≤ S)
    (P : ℕ → Polynomial ℝ) (hP : ∀ N, (P N).natDegree < S) :
    Tendsto (fun N : ℕ => phaseAverage (positiveInterval N)
      (fun n => mangoldtWeight n - cramerWeight (cramerCutoff c₀ N) n) (P N)) atTop (𝓝 0) := by
  obtain ⟨C, hC, hBound⟩ := phaseNorm_positiveInterval_le_gowers (S := S) (by omega)
  obtain ⟨c, A, hc, hA, hModel⟩ :=
    ambient_cramer_self_scale_of_kmtt hc₀ hc₁ hBanks hAmbient hS
  have hDecay : Tendsto (fun N : ℕ => C * (A * Real.exp (-((Real.log (N : ℝ)) ^ c))))
      atTop (𝓝 0) := by
    have hLogPow := (tendsto_rpow_atTop hc).comp
      (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
    have hExp := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hLogPow)
    simpa only [Function.comp_def, mul_zero] using (hExp.const_mul A).const_mul C
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (.of_forall (fun _ => norm_nonneg _)) _ hDecay
  filter_upwards [hModel, eventually_gt_atTop (0 : ℕ)] with N hN hpos
  exact (norm_phaseAverage_le_phaseNorm _ _ (hP N)).trans
    ((hBound N hpos _).trans (mul_le_mul_of_nonneg_left hN hC.le))

/-- Convert a test multiplicative factor on the integer interval to
the natural-number Mangoldt sum. The inserted endpoint at zero vanishes. -/
theorem mangoldtMean_eq_nat_sum (N : ℕ) (a : ℕ → ℂ) :
    (∑ n ∈ positiveInterval N, mangoldtWeight n * a n.toNat) / (N : ℂ) =
      (N : ℝ)⁻¹ • ∑ n ∈ Finset.range (N + 1), ArithmeticFunction.vonMangoldt n • a n := by
  rw [sum_positiveInterval_eq_zero_prefix, Finset.sum_range_succ']
  have hIndex (i : ℕ) : ((i : ℤ) + 1).toNat = i + 1 := by omega
  simp only [mangoldtWeight, hIndex, ArithmeticFunction.map_zero, Complex.ofReal_zero, zero_mul,
    add_zero, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast, div_eq_inv_mul]

/-- The ambient prime model transfers any proof of its unweighted mean
to both ordinary prime number theorem normalizations. -/
theorem primeNumberTheorem_of_cramer_mean {c₀ : ℝ} (hc₀ : 0 < c₀) (hc₁ : c₀ < 1/11)
    (hBanks : BanksRealZeroBound) (hAmbient : KMTTAmbientPrimeModel c₀)
    (hMean : Tendsto (fun N : ℕ => (∑ n ∈ positiveInterval N,
      cramerWeight (cramerCutoff c₀ N) n) / (N : ℂ)) atTop (𝓝 1)) : PrimeNumberTheorem := by
  have hErr := ambient_prime_polynomial_test_error_tendsto hc₀ hc₁ hBanks hAmbient
    (S := 2) le_rfl (fun _ => 0) (fun _ => by simp)
  simp only [phaseAverage, eval_zero, neg_zero, phase_zero, mul_one,
    Finset.sum_sub_distrib, card_positiveInterval, sub_div] at hErr
  have h := hErr.add hMean
  simp only [Pi.add_apply, sub_add_cancel, zero_add] at h
  have hΨ : Tendsto (fun N : ℕ => (∑ n ∈ positiveInterval N, mangoldtWeight n) / (N : ℂ))
      atTop (𝓝 1) := h
  apply PrimeNumberTheorem.of_psi
  have hNat : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ •
      ∑ n ∈ Finset.range (N + 1), ArithmeticFunction.vonMangoldt n • (1 : ℂ)) atTop (𝓝 1) :=
    hΨ.congr (fun N => by simpa only [mul_one] using mangoldtMean_eq_nat_sum N (fun _ => 1))
  simpa only [Function.comp_def, Complex.smul_re, Complex.re_sum, Complex.one_re,
    smul_eq_mul, mul_one, div_eq_inv_mul] using
    (Complex.continuous_re.tendsto (1 : ℂ)).comp hNat

end NilBohr
