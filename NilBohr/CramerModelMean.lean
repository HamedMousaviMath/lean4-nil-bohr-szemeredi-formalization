import NilBohr.CoprimeFourier
import NilBohr.SieveLiterature
import NilBohr.PrimeSiftedAverage
import NilBohr.TwistedOrbit

/-! Unweighted means of the Cramér model from the fundamental sieve lemma. -/

open Filter
open scoped Topology BigOperators

namespace NilBohr

private theorem sum_sieveDivisorSum_eq (samples divisors : Finset ℕ)
    (hits : ℕ → ℕ → Prop) [DecidableRel hits] (coeff : ℕ → ℝ) :
    (∑ t ∈ samples, sieveDivisorSum divisors hits coeff t) =
      ∑ l ∈ divisors, coeff l * ((samples.filter (hits l)).card : ℝ) := by
  unfold sieveDivisorSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]

private theorem sum_coprimeSieveIndicator_period (W : ℕ) :
    (∑ n ∈ Finset.Ioc 0 W, coprimeSieveIndicator W n) = (W.totient : ℝ) := by
  have hI : Finset.Ioc 0 W = Finset.Ico 1 (1 + W) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  have hcard := Nat.filter_coprime_Ico_eq_totient W 1
  rw [hI]
  simp_rw [coprimeSieveIndicator, show ∀ n : ℕ, n.Coprime W ↔ W.Coprime n from
    fun _ => Nat.coprime_comm]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, hcard]

private theorem sieveMain_brackets_totientRatio {W D : ℕ} {ε : ℝ}
    {lower upper : ℕ → ℝ} (hW : 0 < W) (hWeights : SieveBracketingWeights W D ε lower upper) :
    (∑ l ∈ sieveWeightDivisors W D, lower l / (l : ℝ)) ≤ (W.totient : ℝ) / (W : ℝ) ∧
      (W.totient : ℝ) / (W : ℝ) ≤ ∑ l ∈ sieveWeightDivisors W D, upper l / (l : ℝ) := by
  let ds := sieveWeightDivisors W D
  have hWr : 0 < (W : ℝ) := by exact_mod_cast hW
  have hExact (coeff : ℕ → ℝ) :
      (∑ n ∈ Finset.Ioc 0 W, sieveDivisorSum ds (fun l n => l ∣ n) coeff n) / (W : ℝ) =
        ∑ l ∈ ds, coeff l / (l : ℝ) := by
    rw [sum_sieveDivisorSum_eq, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro l hl
    have hlW := (mem_sieveWeightDivisors hl).1
    have hlr : 0 < (l : ℝ) := by exact_mod_cast Nat.pos_of_dvd_of_pos hlW hW
    rw [Nat.Ioc_filter_dvd_card_eq_div]
    have hCast : ((W / l : ℕ) : ℝ) = (W : ℝ) / (l : ℝ) := by
      apply (eq_div_iff hlr.ne').2
      exact_mod_cast Nat.div_mul_cancel hlW
    rw [hCast]
    field_simp [hlr.ne', hWr.ne']
    ring
  have hLo := Finset.sum_le_sum (s := Finset.Ioc 0 W) (fun n hn =>
    (hWeights.bracket n (Finset.mem_Ioc.mp hn).1).1)
  have hHi := Finset.sum_le_sum (s := Finset.Ioc 0 W) (fun n hn =>
    (hWeights.bracket n (Finset.mem_Ioc.mp hn).1).2)
  have hLo' := div_le_div_of_nonneg_right hLo hWr.le
  have hHi' := div_le_div_of_nonneg_right hHi hWr.le
  rw [sum_coprimeSieveIndicator_period, hExact lower] at hLo'
  rw [sum_coprimeSieveIndicator_period, hExact upper] at hHi'
  exact ⟨hLo', hHi'⟩

/-- The mean of the sifted indicator on a positive affine progression
differs from its Euler density by at most the sieve gap and one error per divisor.
The two expected bracketing sums bound the Euler density by averaging on a
complete positive period. -/
theorem abs_coprimeSieveProgressionMean_sub_totientRatio_le {W D H offset step : ℕ}
    {ε : ℝ} {lower upper : ℕ → ℝ} (hW : 0 < W) (hH : 0 < H) (hOff : 0 < offset)
    (hStep : step.Coprime W) (hWeights : SieveBracketingWeights W D ε lower upper) :
    |(∑ t ∈ Finset.range H, coprimeSieveIndicator W (offset + step*t)) / (H : ℝ) -
      (W.totient : ℝ) / (W : ℝ)| ≤ ε + ((sieveWeightDivisors W D).card : ℝ) / (H : ℝ) := by
  let ds := sieveWeightDivisors W D
  let hits (l t : ℕ) := l ∣ offset + step*t
  let main (coeff : ℕ → ℝ) := ∑ l ∈ ds, coeff l / (l : ℝ)
  let average (coeff : ℕ → ℝ) :=
    (∑ t ∈ Finset.range H, sieveDivisorSum ds hits coeff t) / (H : ℝ)
  have hHr : 0 < (H : ℝ) := by exact_mod_cast hH
  have hError (coeff : ℕ → ℝ) (hcoeff : ∀ l ∈ ds, |coeff l| ≤ 1) :
      |average coeff - main coeff| ≤ (ds.card : ℝ) / (H : ℝ) := by
    unfold average main
    rw [sum_sieveDivisorSum_eq, Finset.sum_div, ← Finset.sum_sub_distrib]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    rw [show (ds.card : ℝ) / (H : ℝ) = ∑ _l ∈ ds, (1 : ℝ) / (H : ℝ) by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring]
    apply Finset.sum_le_sum
    intro l hl
    have hlW := (mem_sieveWeightDivisors hl).1
    have hlPos := Nat.pos_of_dvd_of_pos hlW hW
    have hlr : 0 < (l : ℝ) := by exact_mod_cast hlPos
    have hCard := abs_card_dvd_affine_sub_le_one offset step l H hlPos (hStep.coprime_dvd_right hlW)
    rw [show coeff l * (((Finset.range H).filter (hits l)).card : ℝ) / (H : ℝ) -
        coeff l / (l : ℝ) =
        coeff l * ((((Finset.range H).filter (hits l)).card : ℝ) - (H : ℝ) / l) / (H : ℝ) by
      field_simp [hlr.ne', hHr.ne']
      ring, abs_div, abs_mul, abs_of_pos hHr]
    exact div_le_div_of_nonneg_right
      (mul_le_one₀ (hcoeff l hl) (abs_nonneg _) hCard) hHr.le
  obtain ⟨hLMain, hUMain⟩ := sieveMain_brackets_totientRatio hW hWeights
  have hLMain : main lower ≤ (W.totient : ℝ) / (W : ℝ) := hLMain
  have hUMain : (W.totient : ℝ) / (W : ℝ) ≤ main upper := hUMain
  have hLo := div_le_div_of_nonneg_right
    (Finset.sum_le_sum (s := Finset.range H) (fun t _ =>
      (hWeights.bracket (offset + step*t) (by omega)).1)) hHr.le
  have hHi := div_le_div_of_nonneg_right
    (Finset.sum_le_sum (s := Finset.range H) (fun t _ =>
      (hWeights.bracket (offset + step*t) (by omega)).2)) hHr.le
  change average lower ≤ _ at hLo
  change _ ≤ average upper at hHi
  have hGap : main upper - main lower ≤ ε := by
    unfold main
    rw [← Finset.sum_sub_distrib]
    simpa only [sub_div] using hWeights.gap
  have hLErr := (abs_le.mp (hError lower hWeights.lowerBound)).1
  have hUErr := (abs_le.mp (hError upper hWeights.upperBound)).2
  rw [abs_le]
  constructor <;> linarith only [hLMain, hUMain, hLo, hHi, hGap, hLErr, hUErr]

/-- The reduced sieve modulus has no repeated prime factors. -/
theorem squarefree_cramerSieveModulus (Q q : ℕ) : Squarefree (cramerSieveModulus Q q) := by
  exact squarefree_prod_primes _ (fun _ hp => (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2)

private theorem cramerEuler_times_sieveRatio (Q q : ℕ) :
    (∏ p ∈ primesThrough Q, (1 - (p : ℝ)⁻¹)⁻¹) *
        ((cramerSieveModulus Q q).totient : ℝ) / (cramerSieveModulus Q q : ℝ) =
      ∏ p ∈ (primesThrough Q).filter (fun p => p ∣ q), (1 - (p : ℝ)⁻¹)⁻¹ := by
  let W := cramerSieveModulus Q q
  let S := (primesThrough Q).filter (fun p => ¬p ∣ q)
  let f (p : ℕ) : ℝ := 1 - (p : ℝ)⁻¹
  have hpos (p : ℕ) (hp : p ∈ primesThrough Q) : 0 < f p := by
    have hp₂ : (2 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.mp hp).2.two_le
    exact sub_pos.mpr (inv_lt_one_of_one_lt₀ (by linarith))
  have hS : W.primeFactors = S :=
    Nat.primeFactors_prod fun p hp => (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
  have hEuler : (W.totient : ℝ) = (W : ℝ) * ∏ p ∈ S, f p := by
    have h := congrArg (fun x : ℚ => (x : ℝ)) (Nat.totient_eq_mul_prod_factors W)
    push_cast at h
    simpa only [hS, f] using h
  have hposW : (0 : ℝ) < W := by exact_mod_cast cramerSieveModulus_pos Q q
  have hposS : 0 < ∏ p ∈ S, f p := Finset.prod_pos fun p hp => hpos _ (Finset.mem_filter.mp hp).1
  have hposD : 0 < ∏ p ∈ (primesThrough Q).filter (fun p => p ∣ q), f p :=
    Finset.prod_pos fun p hp => hpos _ (Finset.mem_filter.mp hp).1
  have hSplit : (∏ p ∈ primesThrough Q, (f p)⁻¹) =
      (∏ p ∈ (primesThrough Q).filter (fun p => p ∣ q), (f p)⁻¹) *
        (∏ p ∈ S, (f p)⁻¹) :=
    (Finset.prod_filter_mul_prod_filter_not (primesThrough Q) (fun p => p ∣ q) (fun p => (f p)⁻¹)).symm
  change (∏ p ∈ primesThrough Q, (f p)⁻¹) * (W.totient : ℝ) / (W : ℝ) = _
  rw [hEuler, hSplit, Finset.prod_inv_distrib]
  field_simp [hposW.ne', hposS.ne', hposD.ne']
  ring

private theorem primesThrough_filter_dvd_one (Q : ℕ) :
    (primesThrough Q).filter (fun p => p ∣ 1) = ∅ := by
  apply Finset.filter_eq_empty_iff.mpr
  intro p hp hp₁
  exact (Finset.mem_filter.mp hp).2.ne_one (Nat.dvd_one.mp hp₁)

/-- The ordinary Cramér Euler normalization is the ratio of the
squarefree sieve modulus to its totient. -/
theorem cramerSieveRatio_one (Q : ℕ) :
    (cramerSieveModulus Q 1 : ℝ) / (cramerSieveModulus Q 1).totient =
      ∏ p ∈ primesThrough Q, (1 - (p : ℝ)⁻¹)⁻¹ := by
  have hW := cramerSieveModulus_pos Q 1
  have hWr : 0 < (cramerSieveModulus Q 1 : ℝ) := by exact_mod_cast hW
  have hTot : 0 < ((cramerSieveModulus Q 1).totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hW
  have h := cramerEuler_times_sieveRatio Q 1
  rw [primesThrough_filter_dvd_one, Finset.prod_empty] at h
  apply (div_eq_iff hTot.ne').2
  simpa only [one_mul] using ((div_eq_iff hWr.ne').mp h).symm

/-- A Cramér progression average is close to the Euler multiplier associated
to the primes dividing its step. The cutoff and progression length are independent. -/
theorem norm_cramerWeight_progressionMean_sub_eulerProduct_le {Q q D H offset : ℕ}
    {ε : ℝ} {lower upper : ℕ → ℝ} (hQ : 2 ≤ Q) (hH : 0 < H) (hOff : 0 < offset)
    (hOffset : offset.Coprime q)
    (hWeights : SieveBracketingWeights (cramerSieveModulus Q q) D ε lower upper) :
    ‖(∑ t ∈ Finset.range H, cramerWeight Q ((offset+q*t : ℕ) : ℤ)) / (H : ℂ) -
      ((∏ p ∈ (primesThrough Q).filter (fun p => p ∣ q), (1 - (p : ℝ)⁻¹)⁻¹ : ℝ) : ℂ)‖ ≤
      (∏ p ∈ primesThrough Q, (1 - (p : ℝ)⁻¹)⁻¹) * (ε + (D : ℝ) / (H : ℝ)) := by
  let W := cramerSieveModulus Q q
  let A : ℝ := ∏ p ∈ primesThrough Q, (1 - (p : ℝ)⁻¹)⁻¹
  let g (t : ℕ) := coprimeSieveIndicator W (offset+q*t)
  have hA : 0 ≤ A := by
    dsimp only [A]
    rw [← cramerModulus_div_totient hQ]
    positivity
  have hPoint (t : ℕ) : cramerWeight Q ((offset+q*t : ℕ) : ℤ) = (A : ℂ)*(g t : ℂ) := by
    have ht : (offset+q*t).Coprime q := (Nat.coprime_add_mul_left_left _ _ _).mpr hOffset
    simpa only [Int.toNat_natCast] using cramerWeight_eq_sieveIndicator hQ ((offset+q*t : ℕ) : ℤ)
      (Int.toNat_natCast (offset+q*t) ▸ ht)
  have hMean : (∑ t ∈ Finset.range H, cramerWeight Q ((offset+q*t : ℕ) : ℤ)) / (H : ℂ) =
      ((A*((∑ t ∈ Finset.range H, g t)/(H : ℝ)) : ℝ) : ℂ) := by
    simp_rw [hPoint]
    rw [← Finset.mul_sum]
    push_cast
    ring
  have hFactor : A * ((W.totient : ℝ) / (W : ℝ)) =
      ∏ p ∈ (primesThrough Q).filter (fun p => p ∣ q), (1 - (p : ℝ)⁻¹)⁻¹ := by
    rw [← mul_div_assoc]
    exact cramerEuler_times_sieveRatio Q q
  have hBounds := abs_coprimeSieveProgressionMean_sub_totientRatio_le
    (cramerSieveModulus_pos Q q) hH hOff (by simpa using primeStep_coprime_cramerSieveModulus Q q 1)
    hWeights
  have hCard : (((sieveWeightDivisors W D).card : ℕ) : ℝ) ≤ (D : ℝ) := by
    exact_mod_cast card_sieveWeightDivisors_le W D
  rw [hMean, ← hFactor, ← Complex.ofReal_sub, ← mul_sub, Complex.norm_real,
    Real.norm_eq_abs, abs_mul, abs_of_nonneg hA]
  exact mul_le_mul_of_nonneg_left (hBounds.trans
    (add_le_add_left (div_le_div_of_nonneg_right hCard (Nat.cast_nonneg _)) _)) hA

/-- The logarithmic Euler factor times the sieve gap and counting error
tends to zero at the floored level used in Proposition 6.2. -/
theorem tendsto_cramerSieveLogError :
    Tendsto (fun N : ℕ => Real.log (N : ℝ) * ((Real.log (N : ℝ))^(-2 : ℝ) +
      ((⌊(N : ℝ)^(1/20000 : ℝ)⌋₊ : ℕ) : ℝ)/(N : ℝ))) atTop (𝓝 0) := by
  let α : ℝ := 1/20000
  have hT : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hInv : Tendsto (fun N : ℕ => (Real.log (N : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hT
  have hPow : Tendsto (fun N : ℕ => Real.log (N : ℝ)/(N : ℝ)^(1-α)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num [α] : 0 < 1-α)).tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop
  refine squeeze_zero' (Eventually.of_forall fun N => by positivity) ?_ (by simpa using hInv.add hPow)
  filter_upwards [hT.eventually_ge_atTop 1, eventually_gt_atTop (0 : ℕ)] with N hLog hN
  let t := Real.log (N : ℝ)
  have ht : 0 < t := zero_lt_one.trans_le hLog
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hFirst : t*t^(-2 : ℝ) = t⁻¹ := by
    calc
      _ = t^(1 : ℝ)*t^(-2 : ℝ) := by rw [Real.rpow_one]
      _ = t^(-1 : ℝ) := by rw [← Real.rpow_add ht]; norm_num
      _ = _ := Real.rpow_neg_one _
  have hSecond : (N : ℝ)^α / (N : ℝ) = ((N : ℝ)^(1-α))⁻¹ := by
    rw [← Real.rpow_sub_one hn.ne', ← Real.rpow_neg hn.le]
    congr 1
    ring
  change t*(t^(-2 : ℝ) + ((⌊(N : ℝ)^α⌋₊ : ℕ) : ℝ)/(N : ℝ)) ≤
    t⁻¹ + t/(N : ℝ)^(1-α)
  rw [mul_add, hFirst]
  apply add_le_add_left
  calc
    _ ≤ t*((N : ℝ)^α/(N : ℝ)) := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (Nat.floor_le (by positivity)) hn.le) ht.le
    _ = _ := by rw [hSecond, div_eq_mul_inv]

/-- The ordinary mean of the Cramér model is one in the limit for
the subexponential cutoff. This uses the same two sieve inputs as the
phase comparison. -/
theorem tendsto_cramerWeight_mean {c₀ : ℝ} (hc₀ : 0 < c₀) (hc₁ : c₀ < 1)
    (hMertens : MertensIntervalProductBound) (hSieve : FundamentalSieveLemma) :
    Tendsto (fun N : ℕ => (∑ n ∈ positiveInterval N, cramerWeight (cramerCutoff c₀ N) n) /
      (N : ℂ)) atTop (𝓝 1) := by
  let m (N : ℕ) := (∑ n ∈ positiveInterval N, cramerWeight (cramerCutoff c₀ N) n) / (N : ℂ)
  obtain ⟨C, hC, hEuler⟩ := hMertens.eulerProduct_le_log
  have hT : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have he : Tendsto (fun N : ℕ => m N - 1) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
      (by simpa only [mul_zero] using tendsto_cramerSieveLogError.const_mul (2*C))
    filter_upwards [eventually_cramerSieve_coefficients hMertens hSieve hc₀ hc₁
        (A := 2) (by norm_num), hT.eventually_ge_atTop 1, eventually_gt_atTop (0 : ℕ)]
      with N hWeights hLog hN
    let t := Real.log (N : ℝ)
    let Q := cramerCutoff c₀ N
    let D := ⌊(N : ℝ)^(1/20000 : ℝ)⌋₊
    obtain ⟨hQpos, hQlo, hQhi⟩ := cramerCutoff_log_bounds hc₀.le hLog
    have hQ : 2 ≤ Q := by
      by_contra! h
      have hQ₁ : Q = 1 := by
        have hQnat : 0 < Q := by exact_mod_cast hQpos
        omega
      have hl := (Real.one_le_rpow hLog hc₀.le).trans hQlo
      change 1 ≤ Real.log (Q : ℝ) at hl
      rw [hQ₁, Nat.cast_one, Real.log_one] at hl
      norm_num at hl
    have hE : (∏ p ∈ primesThrough Q, (1 - (p : ℝ)⁻¹)⁻¹) ≤ 2*C*t := by
      calc
        _ ≤ C * Real.log (Q : ℝ) := hEuler Q hQ
        _ ≤ C * (2*t^c₀) := mul_le_mul_of_nonneg_left hQhi hC.le
        _ ≤ C * (2*t) := by
          gcongr
          simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hLog hc₁.le
        _ = _ := by ring
    obtain ⟨lo, hi, hW⟩ := hWeights 1
    have hFin := norm_cramerWeight_progressionMean_sub_eulerProduct_le hQ hN
      (offset := 1) (by decide) (by simp) hW
    have hMean : m N = (∑ j ∈ Finset.range N,
        cramerWeight Q ((1+1*j : ℕ) : ℤ)) / (N : ℂ) := by
      dsimp only [m]
      rw [sum_positiveInterval_eq_zero_prefix]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      push_cast
      simp only [one_mul, add_comm, Q]
    rw [primesThrough_filter_dvd_one, Finset.prod_empty, Complex.ofReal_one, ← hMean] at hFin
    change ‖m N - 1‖ ≤ (2*C)*(t*(t^(-2 : ℝ)+(D : ℝ)/(N : ℝ)))
    rw [← mul_assoc]
    exact hFin.trans (mul_le_mul_of_nonneg_right hE (by positivity))
  simpa only [sub_add_cancel, zero_add] using he.add_const (1 : ℂ)

end NilBohr
