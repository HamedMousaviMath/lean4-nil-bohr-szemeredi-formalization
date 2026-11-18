import NilBohr.SieveLiterature
import NilBohr.CoprimeFourier

/-! Finite complex comparison with the midpoint of the sieve bounds. -/

open scoped BigOperators

namespace NilBohr

/-- The midpoint is used as an approximation to the sifting indicator. -/
noncomputable def sieveMidpointCoefficient (lower upper : ℕ → ℝ) (d : ℕ) : ℝ :=
  (lower d + upper d) / 2

/-- The normalized correlation with the sifting indicator in a finite sample. -/
noncomputable def coprimeSieveWeightedMean (W H : ℕ) (samples : Finset ℕ) (test : ℕ → ℂ) : ℂ :=
  (((W : ℝ) / (W.totient : ℝ) : ℝ) : ℂ) *
    ((∑ n ∈ samples, (coprimeSieveIndicator W n : ℂ) * test n) / (H : ℂ))

/-- The same normalization for the midpoint of the two divisor sums. -/
noncomputable def sieveMidpointMean (W D H : ℕ) (samples : Finset ℕ)
    (lower upper : ℕ → ℝ) (test : ℕ → ℂ) : ℂ :=
  (((W : ℝ) / (W.totient : ℝ) : ℝ) : ℂ) *
    ((∑ d ∈ sieveWeightDivisors W D, (sieveMidpointCoefficient lower upper d : ℂ) *
      ∑ n ∈ samples.filter (fun n => d ∣ n), test n) / (H : ℂ))

theorem abs_sieveMidpointCoefficient_le {W D : ℕ} {ε : ℝ} {lower upper : ℕ → ℝ}
    (h : SieveBracketingWeights W D ε lower upper) {d : ℕ} (hd : d ∈ sieveWeightDivisors W D) :
    |sieveMidpointCoefficient lower upper d| ≤ 1 := by
  unfold sieveMidpointCoefficient
  rw [abs_div, abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ)), div_le_iff₀ (by norm_num)]
  exact (abs_add_le _ _).trans (by linarith [h.lowerBound d hd, h.upperBound d hd])

private theorem sieveMidpoint_divisorSum (W D n : ℕ) (lower upper : ℕ → ℝ) :
    sieveDivisorSum (sieveWeightDivisors W D) (· ∣ ·) (sieveMidpointCoefficient lower upper) n =
      (sieveDivisorSum (sieveWeightDivisors W D) (· ∣ ·) lower n +
       sieveDivisorSum (sieveWeightDivisors W D) (· ∣ ·) upper n) / 2 := by
  unfold sieveDivisorSum
  rw [← Finset.sum_add_distrib, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases h : d ∣ n <;> simp [h, sieveMidpointCoefficient, div_eq_mul_inv]

private theorem sieveWeighted_divisorSum (W D : ℕ) (samples : Finset ℕ) (f : ℕ → ℝ)
    (test : ℕ → ℂ) :
    (∑ n ∈ samples, (sieveDivisorSum (sieveWeightDivisors W D) (· ∣ ·) f n : ℂ) * test n) =
    ∑ d ∈ sieveWeightDivisors W D, (f d : ℂ) * ∑ n ∈ samples.filter (fun n => d ∣ n), test n := by
  calc
    _ = ∑ n ∈ samples, ∑ d ∈ sieveWeightDivisors W D, if d ∣ n then (f d : ℂ) * test n else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [sieveDivisorSum, Complex.ofReal_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d hd
      by_cases h : d ∣ n <;> simp [h]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.mul_sum, Finset.sum_filter]

private theorem sieveBracket_all {W D : ℕ} (hW : 0 < W) {ε : ℝ} {lower upper : ℕ → ℝ}
    (h : SieveBracketingWeights W D ε lower upper) (n : ℕ) :
    sieveDivisorSum (sieveWeightDivisors W D) (· ∣ ·) lower n ≤ coprimeSieveIndicator W n ∧
      coprimeSieveIndicator W n ≤ sieveDivisorSum (sieveWeightDivisors W D) (· ∣ ·) upper n := by
  by_cases hn : 0 < n
  · exact h.bracket n hn
  · obtain rfl : n = 0 := by omega
    have hSum (f : ℕ → ℝ) :
        sieveDivisorSum (sieveWeightDivisors W D) (· ∣ ·) f W =
        sieveDivisorSum (sieveWeightDivisors W D) (· ∣ ·) f 0 := by
      unfold sieveDivisorSum
      apply Finset.sum_congr rfl
      intro d hd
      rw [if_pos (mem_sieveWeightDivisors hd).1, if_pos (dvd_zero d)]
    have hCoprime : W.Coprime W ↔ (0 : ℕ).Coprime W := by
      simp only [Nat.Coprime, Nat.gcd_self, Nat.gcd_zero_left]
    simpa only [hSum, coprimeSieveIndicator, hCoprime] using h.bracket W hW

private theorem sum_sieve_gap_eq (W D : ℕ) (samples : Finset ℕ) (lower upper : ℕ → ℝ) :
    (∑ n ∈ samples, (sieveDivisorSum (sieveWeightDivisors W D) (· ∣ ·) upper n -
      sieveDivisorSum (sieveWeightDivisors W D) (· ∣ ·) lower n) / 2) =
    (∑ d ∈ sieveWeightDivisors W D, (upper d - lower d) *
      ((samples.filter (fun n => d ∣ n)).card : ℝ)) / 2 := by
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  congr 1
  have hGap (n : ℕ) : sieveDivisorSum (sieveWeightDivisors W D) (· ∣ ·) upper n -
      sieveDivisorSum (sieveWeightDivisors W D) (· ∣ ·) lower n =
      ∑ d ∈ sieveWeightDivisors W D, if d ∣ n then upper d - lower d else 0 := by
    simp only [sieveDivisorSum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases h : d ∣ n <;> simp [h]
  simp_rw [hGap]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← Finset.sum_filter]
  simp [mul_comm, sub_mul]

/-- A uniform count discrepancy for the sampled divisibility classes controls
the difference between the sifted correlation and the bracketing midpoint. -/
theorem norm_coprimeSieveWeightedMean_sub_midpoint_le {W D H : ℕ}
    {ε δ : ℝ} {lower upper : ℕ → ℝ} (hW : 0 < W) (hH : 0 < H)
    (h : SieveBracketingWeights W D ε lower upper)
    (samples : Finset ℕ) (test : ℕ → ℂ) (hTest : ∀ n ∈ samples, ‖test n‖ ≤ 1)
    (hδ : 0 ≤ δ) (hDiscrepancy : ∀ d ∈ sieveWeightDivisors W D,
      |((samples.filter (fun n => d ∣ n)).card : ℝ) - (H : ℝ) / d| ≤ δ) :
    ‖coprimeSieveWeightedMean W H samples test - sieveMidpointMean W D H samples lower upper test‖ ≤
      ((W : ℝ) / W.totient) * (ε / 2 + (D : ℝ) * δ / (H : ℝ)) := by
  let mid := sieveDivisorSum (sieveWeightDivisors W D) (· ∣ ·) (sieveMidpointCoefficient lower upper)
  let gap := fun n => (sieveDivisorSum (sieveWeightDivisors W D) (· ∣ ·) upper n -
    sieveDivisorSum (sieveWeightDivisors W D) (· ∣ ·) lower n) / 2
  have hPoint (n : ℕ) (hn : n ∈ samples) :
      ‖(coprimeSieveIndicator W n : ℂ) * test n - (mid n : ℂ) * test n‖ ≤ gap n := by
    rw [← sub_mul, ← Complex.ofReal_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    refine (mul_le_of_le_one_right (abs_nonneg _) (hTest n hn)).trans ?_
    obtain ⟨hl, hu⟩ := sieveBracket_all hW h n
    dsimp [mid, gap]
    rw [sieveMidpoint_divisorSum, abs_le]
    constructor <;> linarith
  have hGap : (∑ n ∈ samples, gap n) ≤ (H : ℝ) * (ε / 2) + (D : ℝ) * δ := by
    dsimp [gap]
    rw [sum_sieve_gap_eq]
    let divisors := sieveWeightDivisors W D
    have hBound : (∑ d ∈ divisors, (upper d - lower d) *
        ((samples.filter (fun n => d ∣ n)).card : ℝ)) ≤
        (∑ d ∈ divisors, (upper d - lower d) * ((H : ℝ) / d)) +
          (divisors.card : ℝ) * (2 * δ) := by
      rw [← nsmul_eq_mul, ← Finset.sum_const, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro d hd
      have hCoeff : |upper d - lower d| ≤ 2 :=
        (abs_sub_le (upper d) 0 (lower d)).trans (by
          simp only [sub_zero, zero_sub, abs_neg]
          linarith [h.upperBound d hd, h.lowerBound d hd])
      have hDiff : (upper d - lower d) *
          (((samples.filter (fun n => d ∣ n)).card : ℝ) - (H : ℝ) / d) ≤ 2 * δ := by
        refine (le_abs_self _).trans ?_
        rw [abs_mul]
        exact mul_le_mul hCoeff (hDiscrepancy d hd) (abs_nonneg _) (by norm_num)
      linarith only [hDiff]
    have hFactor : (∑ d ∈ divisors, (upper d - lower d) * ((H : ℝ) / d)) =
        (H : ℝ) * (∑ d ∈ divisors, (upper d - lower d) / (d : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    rw [hFactor] at hBound
    have hCard : (divisors.card : ℝ) ≤ D := by exact_mod_cast card_sieveWeightDivisors_le W D
    have hGapBound := mul_le_mul_of_nonneg_left h.gap (Nat.cast_nonneg H)
    have hCardBound := mul_le_mul_of_nonneg_right hCard hδ
    linarith only [hBound, hGapBound, hCardBound]
  have hHReal : (0 : ℝ) < H := by exact_mod_cast hH
  unfold coprimeSieveWeightedMean sieveMidpointMean
  rw [← sieveWeighted_divisorSum, ← mul_sub, ← sub_div, ← Finset.sum_sub_distrib]
  rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ ((H : ℝ) * (ε / 2) + (D : ℝ) * δ) / (H : ℝ) :=
      div_le_div_of_nonneg_right ((norm_sum_le _ _).trans ((Finset.sum_le_sum hPoint).trans hGap))
        hHReal.le
    _ = _ := by field_simp; ring

private theorem nat_Icc_one_eq_range_succ_image (N : ℕ) :
    Finset.Icc 1 N = (Finset.range N).image (· + 1) := by
  ext n
  simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
  constructor
  · intro hn
    exact ⟨n - 1, by omega, by omega⟩
  · rintro ⟨j,hj,rfl⟩
    omega

private theorem abs_card_dvd_Icc_sub_le_one (N d : ℕ) (hd : 0 < d) :
    |(((Finset.Icc 1 N).filter (fun n => d ∣ n)).card : ℝ) - (N : ℝ) / d| ≤ 1 := by
  rw [nat_Icc_one_eq_range_succ_image, Finset.filter_image, Finset.card_image_of_injective _
    (fun _ _ h => Nat.add_right_cancel h)]
  simpa only [one_mul, add_comm] using abs_card_dvd_affine_sub_le_one 1 1 d N hd (Nat.coprime_one_left d)

/-- The midpoint replaces the sifted correlation over [1,N] with error
bounded by the sieve gap and the total endpoint discrepancy. -/
theorem norm_coprimeSieveMean_sub_midpoint_le {W D N : ℕ} {ε : ℝ} {lower upper : ℕ → ℝ}
    (hW : 0 < W) (hN : 0 < N) (h : SieveBracketingWeights W D ε lower upper)
    (test : ℕ → ℂ) (hTest : ∀ n ∈ Finset.Icc 1 N, ‖test n‖ ≤ 1) :
    ‖coprimeSieveWeightedMean W N (Finset.Icc 1 N) test -
      sieveMidpointMean W D N (Finset.Icc 1 N) lower upper test‖ ≤
      ((W : ℝ) / W.totient) * (ε / 2 + (D : ℝ) / (N : ℝ)) := by
  simpa only [mul_one] using norm_coprimeSieveWeightedMean_sub_midpoint_le (δ := 1) hW hN h
    (Finset.Icc 1 N) test hTest zero_le_one (fun d hd =>
      abs_card_dvd_Icc_sub_le_one N d (Nat.pos_of_dvd_of_pos (mem_sieveWeightDivisors hd).1 hW))

private theorem card_dvd_range_eq {H d : ℕ} (hd : 0 < d) (hdH : d ∣ H) :
    ((Finset.range H).filter (fun n => d ∣ n)).card = H / d := by
  simp_rw [← Nat.modEq_zero_iff_dvd]
  rw [← Nat.count_eq_card_filter_range, Nat.count_modEq_card _ hd, Nat.mod_eq_zero_of_dvd hdH]
  simp

/-- There is no endpoint discrepancy over the complete sifting period. -/
theorem norm_coprimeSievePeriod_sub_midpoint_le {W D H : ℕ} {ε : ℝ} {lower upper : ℕ → ℝ}
    (hW : 0 < W) (hH : 0 < H) (hWH : W ∣ H) (h : SieveBracketingWeights W D ε lower upper)
    (test : ℕ → ℂ) (hTest : ∀ n ∈ Finset.range H, ‖test n‖ ≤ 1) :
    ‖coprimeSieveWeightedMean W H (Finset.range H) test -
      sieveMidpointMean W D H (Finset.range H) lower upper test‖ ≤
      ((W : ℝ) / W.totient) * (ε / 2) := by
  simpa only [mul_zero, zero_div, add_zero] using norm_coprimeSieveWeightedMean_sub_midpoint_le
    (δ := 0) hW hH h (Finset.range H) test hTest le_rfl (fun d hd => by
      have hdW := (mem_sieveWeightDivisors hd).1
      have hdH := hdW.trans hWH
      have hdpos := Nat.pos_of_dvd_of_pos hdW hW
      rw [card_dvd_range_eq hdpos hdH, Nat.cast_div_charZero hdH, sub_self, abs_zero])

/-- The main term selected by the rational character in the sieve divisor sum. -/
noncomputable def sieveMidpointFourierCoefficient (W D q : ℕ) (lower upper : ℕ → ℝ) : ℂ :=
  (((W : ℝ) / (W.totient : ℝ) : ℝ) : ℂ) *
    ∑ d ∈ (sieveWeightDivisors W D).filter (fun d => q ∣ d),
      (sieveMidpointCoefficient lower upper d : ℂ) / (d : ℂ)

private theorem sieveMidpointMean_period_eq_of_divisor_sum {W D H q : ℕ}
    (hW : 0 < W) (hH : 0 < H) (hWH : W ∣ H) (lower upper : ℕ → ℝ) (test : ℕ → ℂ)
    (hSum : ∀ d ∈ sieveWeightDivisors W D,
      (∑ n ∈ (Finset.range H).filter (fun n => d ∣ n), test n) =
        if q ∣ d then ((H / d : ℕ) : ℂ) else 0) :
    sieveMidpointMean W D H (Finset.range H) lower upper test =
      sieveMidpointFourierCoefficient W D q lower upper := by
  unfold sieveMidpointMean sieveMidpointFourierCoefficient
  rw [Finset.sum_div, Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  rw [hSum d hd]
  by_cases hqd : q ∣ d
  · have hdW := (mem_sieveWeightDivisors hd).1
    have hdH := hdW.trans hWH
    have hdpos := Nat.pos_of_dvd_of_pos hdW hW
    have hHne : (H : ℂ) ≠ 0 := by exact_mod_cast hH.ne'
    have hdne : (d : ℂ) ≠ 0 := by exact_mod_cast hdpos.ne'
    rw [if_pos hqd, Nat.cast_div_charZero hdH, if_pos hqd]
    field_simp
    ring
  · simp [hqd]

/-- Exact Fourier coefficient of the midpoint over a common period. -/
theorem sieveMidpointMean_period_fourier_eq {W D H q : ℕ}
    (hW : 0 < W) (hH : 0 < H) (hq : 0 < q) (hWH : W ∣ H) (hqH : q ∣ H)
    {a : ℤ} (ha : a.natAbs.Coprime q) (lower upper : ℕ → ℝ) :
    sieveMidpointMean W D H (Finset.range H) lower upper
        (fun n => phaseExponential (((a : ℝ) / q) * n)) =
      sieveMidpointFourierCoefficient W D q lower upper := by
  apply sieveMidpointMean_period_eq_of_divisor_sum hW hH hWH
  intro d hd
  have hdW := (mem_sieveWeightDivisors hd).1
  rw [Finset.sum_filter]
  exact sum_phaseExponential_dvd_full_period hq (Nat.pos_of_dvd_of_pos hdW hW)
    hqH (hdW.trans hWH) ha

/-- The endpoint-free sieve comparison for a complete rational Fourier period. -/
theorem norm_coprimeSievePeriod_sub_midpoint_fourier_le
    {W D H q : ℕ} {ε : ℝ} {lower upper : ℕ → ℝ}
    (hW : 0 < W) (hH : 0 < H) (hq : 0 < q) (hWH : W ∣ H) (hqH : q ∣ H)
    {a : ℤ} (ha : a.natAbs.Coprime q) (h : SieveBracketingWeights W D ε lower upper) :
    ‖(W : ℂ) / (W.totient : ℂ) * coprimeFourierMean H W a q -
      sieveMidpointFourierCoefficient W D q lower upper‖ ≤
      ((W : ℝ) / W.totient) * (ε / 2) := by
  rw [← sieveMidpointMean_period_fourier_eq hW hH hq hWH hqH ha lower upper]
  have hSame : coprimeSieveWeightedMean W H (Finset.range H)
      (fun n => phaseExponential (((a : ℝ) / q) * n)) =
      (W : ℂ) / (W.totient : ℂ) * coprimeFourierMean H W a q := by
    unfold coprimeSieveWeightedMean coprimeFourierMean
    rw [Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_natCast]
    congr 2
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hc : n.Coprime W
    · rw [coprimeSieveIndicator, if_pos hc, if_pos hc, Complex.ofReal_one, one_mul]
    · rw [coprimeSieveIndicator, if_neg hc, if_neg hc, Complex.ofReal_zero, zero_mul]
  rw [← hSame]
  exact norm_coprimeSievePeriod_sub_midpoint_le hW hH hWH h _ (fun n _ => by
    simp [phaseExponential, Complex.norm_exp])

/-- A pointwise error bound for each divisor phase sum extends to the sieve
midpoint using only the level bound and the coefficient bound. -/
theorem norm_sieveMidpointMean_sub_fourierCoefficient_mul_le
    {W D N q : ℕ} {ε K : ℝ} {lower upper : ℕ → ℝ}
    (h : SieveBracketingWeights W D ε lower upper)
    (test : ℕ → ℂ) (base : ℂ) (hK : 0 ≤ K)
    (hError : ∀ d ∈ sieveWeightDivisors W D,
      ‖(∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n), test n) -
        (if q ∣ d then base / (d : ℂ) else 0)‖ ≤ K) :
    ‖sieveMidpointMean W D N (Finset.Icc 1 N) lower upper test -
      sieveMidpointFourierCoefficient W D q lower upper * (base / (N : ℂ))‖ ≤
      ((W : ℝ) / W.totient) * ((D : ℝ) * K / (N : ℝ)) := by
  let mid := sieveMidpointCoefficient lower upper
  let main (d : ℕ) : ℂ := if q ∣ d then base / (d : ℂ) else 0
  let observed (d : ℕ) : ℂ := ∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n), test n
  let divisors := sieveWeightDivisors W D
  have hMain : (∑ d ∈ divisors.filter (fun d => q ∣ d), (mid d : ℂ) / (d : ℂ)) * base =
      ∑ d ∈ divisors, (mid d : ℂ) * main d := by
    rw [Finset.sum_filter, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hqd : q ∣ d <;> simp [main, hqd, div_eq_mul_inv, mul_assoc, mul_comm]
  have hMainDen : (∑ d ∈ divisors.filter (fun d => q ∣ d), (mid d : ℂ) / (d : ℂ)) *
      (base / (N : ℂ)) = (∑ d ∈ divisors, (mid d : ℂ) * main d) / (N : ℂ) := by
    rw [← mul_div_assoc, hMain]
  change ‖_ * ((∑ d ∈ divisors, (mid d : ℂ) * observed d) / (N : ℂ)) -
    (_ * (∑ d ∈ divisors.filter (fun d => q ∣ d), (mid d : ℂ) / (d : ℂ))) *
      (base / (N : ℂ))‖ ≤ _
  rw [mul_assoc, hMainDen, ← mul_sub, ← sub_div, ← Finset.sum_sub_distrib,
    norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  calc
    _ ≤ ∑ _d ∈ divisors, K := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro d hd
      rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact (mul_le_of_le_one_left (norm_nonneg _) (abs_sieveMidpointCoefficient_le h hd)).trans
        (hError d hd)
    _ = (divisors.card : ℝ) * K := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast card_sieveWeightDivisors_le W D) hK

end NilBohr
