import NilBohr.AmbientPrimeMean
import NilBohr.BracketPointwise

/-! Transfer of linear exponential sums to continuous prime-circle tests. -/

namespace NilBohr

open Filter MeasureTheory Polynomial
open scoped Topology BigOperators

/-- The ambient Gowers estimate transfers a Cramér linear cancellation
limit to the corresponding normalized average over primes. -/
theorem prime_linear_mode_tendsto_of_model {c₀ : ℝ} (hc₀ : 0 < c₀) (hc₁ : c₀ < 1/11)
    (hBanks : BanksRealZeroBound) (hAmbient : KMTTAmbientPrimeModel c₀)
    (hPNT : PrimeNumberTheorem) (α : ℝ)
    (hCramer : Tendsto (fun N : ℕ => (∑ n ∈ positiveInterval N,
       cramerWeight (cramerCutoff c₀ N) n * phase (α * (n : ℝ))) / (N : ℂ)) atTop (𝓝 0)) :
    Tendsto (primeAverage (fun p => phase (α * (p : ℝ)))) atTop (𝓝 0) := by
  have hErr := ambient_prime_polynomial_test_error_tendsto hc₀ hc₁ hBanks hAmbient
    (S := 2) le_rfl (fun _ => C (-α) * X)
    (fun _ => (natDegree_C_mul_le (-α) (X : Polynomial ℝ)).trans_lt (by simp))
  simp only [phaseAverage, eval_mul, eval_C, eval_X, neg_mul, neg_neg, card_positiveInterval,
    sub_mul, Finset.sum_sub_distrib, sub_div] at hErr
  have h := hErr.add hCramer
  simp only [Pi.add_apply, sub_add_cancel, zero_add] at h
  apply tendsto_primeAverage_of_tendsto_mangoldt hPNT (B := 1) (fun n => (norm_phase _).le)
  apply h.congr
  intro N
  rw [← mangoldtMean_eq_nat_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have hnn : 0 ≤ n := (show (0 : ℤ) ≤ 1 by decide).trans (Finset.mem_Icc.mp hn).1
  rw [show (n.toNat : ℝ) = (n : ℝ) by exact_mod_cast Int.toNat_of_nonneg hnn]

/-- Cancellation of the nonzero irrational linear modes gives the exact
continuous-test interface for prime equidistribution. -/
theorem vinogradov_of_prime_linear_modes
    (hMode : ∀ α : ℝ, Irrational α →
      Tendsto (primeAverage (fun p => phase (α * (p : ℝ)))) atTop (𝓝 0)) :
    VinogradovPrimeEquidistribution := by
  intro β hβ F
  let V (n : ℤ) := β * ((n : ℝ) + 1)
  have hV (p : ℕ) : V ((p : ℤ) - 1) = β * (p : ℝ) := by simp [V]
  have hFourier (h : ℤ) (t : ℝ) : fourier (T := 1) h (t : Circle) = phase ((h : ℝ) * t) := by
    simp only [fourier_coe_apply, Complex.ofReal_one, div_one, phase,
      Complex.ofReal_mul, Complex.ofReal_intCast, mul_assoc]
  have hCancel (h : ℤ) (hh : h ≠ 0) :
      Tendsto (primeAverage (fun p => fourier (T := 1) h (V ((p : ℤ) - 1) : Circle) * 1))
        atTop (𝓝 0) := by
    simp only [hV, hFourier, mul_one, ← mul_assoc]
    exact hMode _ (irrational_intCast_mul_iff.mpr ⟨hh, hβ⟩)
  have hCentered := ae_centered_primeAverage_of_fourier_cancellation
    (μ := Measure.dirac ()) V (fun (_ : Unit) (_ : ℕ) => (1 : ℂ)) (B := 1) zero_le_one
    (.of_forall (fun _ _ => by simp)) (fun h hh => .of_forall (fun _ => hCancel h hh)) F
  rw [ae_dirac_eq] at hCentered
  have h' : Tendsto (primeAverage (fun p => F (β * (p : ℝ) : Circle) - circleMean F))
      atTop (𝓝 0) := by
    simpa only [eventually_pure, hV, mul_one] using hCentered
  have hSum := h'.add (tendsto_const_nhds (x := circleMean F) (f := atTop))
  rw [zero_add] at hSum
  apply hSum.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  have hp : 2 ∈ primesThrough N := by simp [primesThrough, Nat.lt_succ_iff, Nat.prime_two, hN]
  have hn : ((primesThrough N).card : ℂ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr ⟨2, hp⟩).ne'
  simp only [primeAverage, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, sub_div,
    mul_div_cancel_left₀ _ hn, sub_add_cancel]

end NilBohr
