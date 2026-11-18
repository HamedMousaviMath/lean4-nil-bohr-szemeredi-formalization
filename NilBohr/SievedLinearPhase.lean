import NilBohr.PrimeLinearPhaseSums
import NilBohr.SieveFourierComparison
import NilBohr.PrimePhaseApproximants

/-! Finite linear phase comparison for the Cramér sieve. -/

open scoped BigOperators

namespace NilBohr

/-- Approximate the phase by a primitive rational phase at the square-root
scale. Over the sieve midpoint, only divisors divisible by the rational
denominator contribute a main term. Its normalized coefficient is compared
with the exact coprime Fourier coefficient over a complete period. -/
theorem exists_norm_coprimeSieve_linearMean_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {W D N q : ℕ}, Squarefree W → 0 < N →
      0 < q → q ≤ N.sqrt → 2 * D ≤ N.sqrt → ∀ {a : ℤ}, a.natAbs.Coprime q → ∀ {α : ℝ},
      |α - (a : ℝ) / (q : ℝ)| ≤ 1 / ((q : ℝ) * (N.sqrt : ℝ)) →
      ∀ {ε : ℝ} {lower upper : ℕ → ℝ}, SieveBracketingWeights W D ε lower upper →
      ‖coprimeSieveWeightedMean W N (Finset.Icc 1 N) (fun n => phase (α * (n : ℝ)))‖ ≤
        Real.sqrt (2 / (q : ℝ)) + ((W : ℝ) / (W.totient : ℝ)) *
          (ε + 2 * (D : ℝ) / (N : ℝ) + C * (D : ℝ) / (N.sqrt : ℝ)) := by
  obtain ⟨L, hL, hBlock⟩ := exists_norm_sum_phase_multiples_sub_full_le
  refine ⟨2 + L, by linarith, ?_⟩
  intro W D N q hW hN hq hqN hDN a ha α hApprox ε lower upper hWeights
  let S := N.sqrt
  let θ := α - (a : ℝ) / (q : ℝ)
  let phaseTest (n : ℕ) : ℂ := phase (α * (n : ℝ))
  let base := ∑ n ∈ Finset.Icc 1 N, phase (θ * (n : ℝ))
  let K : ℝ := 2 * (q : ℝ) + 1 + L * (N : ℝ) / (S : ℝ)
  let H := W * q
  let normalizer : ℝ := (W : ℝ) / (W.totient : ℝ)
  let actual := coprimeSieveWeightedMean W N (Finset.Icc 1 N) phaseTest
  let midpoint := sieveMidpointMean W D N (Finset.Icc 1 N) lower upper phaseTest
  let rationalCoeff := (W : ℂ) / (W.totient : ℂ) * coprimeFourierMean H W a q
  let midpointCoeff := sieveMidpointFourierCoefficient W D q lower upper
  have hWpos : 0 < W := Nat.pos_of_ne_zero hW.ne_zero
  have hHpos : 0 < H := Nat.mul_pos hWpos hq
  have hWH : W ∣ H := ⟨q, rfl⟩
  have hqH : q ∣ H := ⟨W, Nat.mul_comm _ _⟩
  have hS : 0 < S := hq.trans_le hqN
  have hS' : 0 < (S : ℝ) := Nat.cast_pos.mpr hS
  have hN' : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hqOne : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hnormalizer : 0 ≤ normalizer := by dsimp [normalizer]; positivity
  have hθBound : |θ| ≤ 1 / (S : ℝ) :=
    hApprox.trans <| one_div_le_one_div_of_le hS' <| le_mul_of_one_le_left hS'.le hqOne
  have hError (d : ℕ) (hd : d ∈ sieveWeightDivisors W D) :
      ‖(∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n), phaseTest n) -
        (if q ∣ d then base / (d : ℂ) else 0)‖ ≤ K := by
    obtain ⟨hdW, hdLevel⟩ := mem_sieveWeightDivisors hd
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdW hWpos
    by_cases hqd : q ∣ d
    · rw [if_pos hqd]
      dsimp only [phaseTest]
      rw [sum_phase_multiples_sub_rational N d q hq hqd a α]
      apply (hBlock N d hdpos θ).trans
      have hProduct := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hθBound hL) hN'.le
      have hProduct' : L * |θ| * (N : ℝ) ≤ L * (N : ℝ) / (S : ℝ) :=
        hProduct.trans_eq (by ring)
      dsimp only [K]
      linarith only [hProduct', hqOne]
    · rw [if_neg hqd, sub_zero]
      have hdS : 2 * d ≤ S := (Nat.mul_le_mul_left 2 hdLevel).trans hDN
      have hFreq := torusNorm_mul_ge_inv_two_denominator hq hS hdS ha hqd hApprox
      apply (norm_sum_phase_multiples_le_of_frequency N d q hdpos hq α hFreq).trans
      dsimp only [K]
      linarith only [show 0 ≤ L * (N : ℝ) / (S : ℝ) by positivity]
  have hSiftError : ‖actual - midpoint‖ ≤ normalizer * (ε / 2 + (D : ℝ) / (N : ℝ)) :=
    norm_coprimeSieveMean_sub_midpoint_le hWpos hN hWeights phaseTest
      (fun n _ => by simp [phaseTest, norm_phase])
  have hMidError : ‖midpoint - midpointCoeff * (base / (N : ℂ))‖ ≤
      normalizer * ((D : ℝ) * K / (N : ℝ)) :=
    norm_sieveMidpointMean_sub_fourierCoefficient_mul_le hWeights phaseTest base hK hError
  have hRationalBound : ‖rationalCoeff‖ ≤ Real.sqrt (2 / (q : ℝ)) :=
    norm_normalized_coprimeFourierMean_le hHpos hW hq hWH hqH ha
  have hPeriodError : ‖rationalCoeff - midpointCoeff‖ ≤ normalizer * (ε / 2) :=
    norm_coprimeSievePeriod_sub_midpoint_fourier_le hWpos hHpos hq hWH hqH ha hWeights
  have hCoeffBound : ‖midpointCoeff‖ ≤ Real.sqrt (2 / (q : ℝ)) + normalizer * (ε / 2) := by
    calc
      _ = ‖rationalCoeff + (midpointCoeff - rationalCoeff)‖ := by rw [add_sub_cancel]
      _ ≤ ‖rationalCoeff‖ + ‖rationalCoeff - midpointCoeff‖ :=
        (norm_add_le _ _).trans_eq (by rw [norm_sub_rev])
      _ ≤ _ := add_le_add hRationalBound hPeriodError
  have hBase : ‖base / (N : ℂ)‖ ≤ 1 := by
    rw [norm_div, Complex.norm_natCast, div_le_one hN']
    exact (norm_sum_le _ _).trans_eq (by simp [norm_phase, Nat.card_Icc])
  have hSquare : (S : ℝ) * (S : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.sqrt_le N
  have hqS : (q : ℝ) ≤ (S : ℝ) := by exact_mod_cast hqN
  have hqBound : (q : ℝ) ≤ (N : ℝ) / (S : ℝ) :=
    (le_div_iff₀ hS').mpr ((mul_le_mul_of_nonneg_right hqS hS'.le).trans hSquare)
  have hKBound : K ≤ 1 + (2 + L) * (N : ℝ) / (S : ℝ) := calc
    _ ≤ 2 * ((N : ℝ) / (S : ℝ)) + 1 + L * (N : ℝ) / (S : ℝ) := by
      dsimp only [K]
      linarith only [hqBound]
    _ = _ := by ring
  have hMidScale : (D : ℝ) * K / (N : ℝ) ≤
      (D : ℝ) / (N : ℝ) + (2 + L) * (D : ℝ) / (S : ℝ) := calc
    _ ≤ (D : ℝ) * (1 + (2 + L) * (N : ℝ) / (S : ℝ)) / (N : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hKBound (Nat.cast_nonneg D)) hN'.le
    _ = _ := by field_simp; ring
  have hMain : ‖midpointCoeff * (base / (N : ℂ))‖ ≤
      Real.sqrt (2 / (q : ℝ)) + normalizer * (ε / 2) := by
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) hBase).trans hCoeffBound
  calc
    ‖actual‖ = ‖(actual - midpoint) +
        ((midpoint - midpointCoeff * (base / (N : ℂ))) + midpointCoeff * (base / (N : ℂ)))‖ := by
      rw [sub_add_cancel, sub_add_cancel]
    _ ≤ ‖actual - midpoint‖ + ‖midpoint - midpointCoeff * (base / (N : ℂ))‖ +
        ‖midpointCoeff * (base / (N : ℂ))‖ := by
      simpa only [add_assoc] using (norm_add_le _ _).trans
        (add_le_add_left (norm_add_le _ _) _)
    _ ≤ normalizer * (ε / 2 + (D : ℝ) / (N : ℝ)) +
        normalizer * ((D : ℝ) / (N : ℝ) + (2 + L) * (D : ℝ) / (S : ℝ)) +
        (Real.sqrt (2 / (q : ℝ)) + normalizer * (ε / 2)) :=
      add_le_add (add_le_add hSiftError (hMidError.trans
        (mul_le_mul_of_nonneg_left hMidScale hnormalizer))) hMain
    _ = _ := by dsimp only [normalizer, S]; ring

end NilBohr
