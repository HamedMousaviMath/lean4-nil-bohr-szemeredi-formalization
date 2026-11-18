import NilBohr.CramerModelMean
import NilBohr.PrimePhaseApproximants
import NilBohr.SievedLinearPhase

/-! The Cramér model at a subexponential cutoff has zero limiting
correlation with every fixed irrational linear phase. -/

namespace NilBohr

open Filter
open scoped Topology BigOperators

private theorem cramer_linear_mean_eq_sieve (Q N : ℕ) (hQ : 2 ≤ Q) (α : ℝ) :
    (∑ n ∈ positiveInterval N, cramerWeight Q n * phase (α * (n : ℝ))) / (N : ℂ) =
      coprimeSieveWeightedMean (cramerSieveModulus Q 1) N (Finset.Icc 1 N)
        (fun n => phase (α * (n : ℝ))) := by
  rw [coprimeSieveWeightedMean, ← mul_div_assoc, Finset.mul_sum]
  congr 1
  apply Finset.sum_bij (fun (n : ℤ) _ => n.toNat)
  · intro n hn
    obtain ⟨hl, hu⟩ := Finset.mem_Icc.mp hn
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro n hn m hm he
    obtain ⟨hl, _⟩ := Finset.mem_Icc.mp hn
    obtain ⟨hl', _⟩ := Finset.mem_Icc.mp hm
    omega
  · intro m hm
    obtain ⟨hl, hu⟩ := Finset.mem_Icc.mp hm
    exact ⟨(m : ℤ), Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by simp⟩
  · intro n hn
    have hnn : 0 ≤ n := (show (0 : ℤ) ≤ 1 by decide).trans (Finset.mem_Icc.mp hn).1
    have hncast : (n.toNat : ℝ) = (n : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hnn
    rw [cramerWeight_eq_sieveIndicator hQ n (Nat.coprime_one_right _), ← cramerSieveRatio_one,
      hncast, mul_assoc]

/-- Irrational linear phase cancellation for the Cramér model, with
the exact cutoff used in the ambient Mangoldt comparison. -/
theorem tendsto_cramer_linear_mean {c₀ : ℝ} (hc₀ : 0 < c₀) (hc₁ : c₀ < 1)
    (hMertens : MertensIntervalProductBound) (hSieve : FundamentalSieveLemma)
    {α : ℝ} (hα : Irrational α) :
    Tendsto (fun N : ℕ => (∑ n ∈ positiveInterval N,
      cramerWeight (cramerCutoff c₀ N) n * phase (α * (n : ℝ))) / (N : ℂ)) atTop (𝓝 0) := by
  obtain ⟨C, hC, hFinite⟩ := exists_norm_coprimeSieve_linearMean_le
  obtain ⟨K, hK, hEuler⟩ := hMertens.eulerProduct_le_log
  let D (N : ℕ) := ⌊(N : ℝ) ^ (1 / 20000 : ℝ)⌋₊
  let e (N : ℕ) := (2*K) * (Real.log (N : ℝ) * ((Real.log (N : ℝ)) ^ (-2 : ℝ) +
    (D N : ℝ)/(N : ℝ)) + Real.log (N : ℝ) * (D N : ℝ)/(N : ℝ) +
    C * (Real.log (N : ℝ) * (D N : ℝ)/(N.sqrt : ℝ)))
  have hError : Tendsto e atTop (𝓝 0) := by
    have h := ((tendsto_cramerSieveLogError.add tendsto_log_mul_sieveLevel_div_cutoff).add
      (tendsto_log_mul_sieveLevel_div_natSqrt.const_mul C)).const_mul (2*K)
    simpa only [e, D, Pi.add_apply, zero_add, mul_zero] using h
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hqRate : Tendsto (fun q : ℕ => Real.sqrt (2/(q : ℝ))) atTop (𝓝 0) := by
    have hi : Tendsto (fun q : ℕ => (q : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have hi₂ : Tendsto (fun q : ℕ => 2/(q : ℝ)) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, mul_zero] using hi.const_mul 2
    simpa only [Function.comp_def, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp hi₂
  apply Metric.tendsto_nhds.2
  intro δ hδ
  obtain ⟨B, hB⟩ := eventually_atTop.1 (hqRate.eventually_lt_const (half_pos hδ))
  filter_upwards [eventually_irrational_dirichlet_approximation hα B,
    eventually_cramerSieve_coefficients hMertens hSieve hc₀ hc₁ (A := 2) (by norm_num),
    eventually_twice_sieveLevel_le_natSqrt, hError.eventually_lt_const (half_pos hδ),
    hlog.eventually_ge_atTop 1, eventually_gt_atTop (0 : ℕ)] with N hApprox hSift hD hE hLog hN
  obtain ⟨a, q, hq, hqB, hqN, ha, hApprox⟩ := hApprox
  let Q := cramerCutoff c₀ N
  let W := cramerSieveModulus Q 1
  obtain ⟨hQpos, hQlow, hQhigh⟩ := cramerCutoff_log_bounds hc₀.le hLog
  have hQ : 2 ≤ Q := by
    by_contra! h
    change 0 < (Q : ℝ) at hQpos
    have hQnat : 0 < Q := by exact_mod_cast hQpos
    have hQone : Q = 1 := by omega
    have hLow := (Real.one_le_rpow hLog hc₀.le).trans hQlow
    change 1 ≤ Real.log (Q : ℝ) at hLow
    rw [hQone, Nat.cast_one, Real.log_one] at hLow
    norm_num at hLow
  have hRatio : (W : ℝ) / W.totient ≤ (2*K)*Real.log (N : ℝ) := by
    change ((cramerSieveModulus Q 1 : ℕ) : ℝ) / _ ≤ _
    rw [cramerSieveRatio_one]
    calc
      _ ≤ K * Real.log (Q : ℝ) := hEuler Q hQ
      _ ≤ K * (2 * (Real.log (N : ℝ))^c₀) := mul_le_mul_of_nonneg_left hQhigh hK.le
      _ ≤ K * (2 * Real.log (N : ℝ)) := by
        gcongr
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hLog hc₁.le
      _ = _ := by ring
  obtain ⟨lower, upper, hWeights⟩ := hSift 1
  have hTest := hFinite (squarefree_cramerSieveModulus Q 1) hN hq hqN hD ha hApprox hWeights
  rw [dist_zero_right, cramer_linear_mean_eq_sieve Q N hQ α]
  have hq' := hB q hqB.le
  have hNormErr : (W : ℝ) / W.totient * ((Real.log (N : ℝ)) ^ (-2 : ℝ) +
      2 * (D N : ℝ)/(N : ℝ) + C * (D N : ℝ)/(N.sqrt : ℝ)) ≤ e N := calc
    _ ≤ (2*K) * Real.log (N : ℝ) * _ := mul_le_mul_of_nonneg_right hRatio (by positivity)
    _ = e N := by dsimp only [e]; ring
  exact (hTest.trans (add_le_add le_rfl hNormErr)).trans_lt (by linarith only [hq', hE])

end NilBohr
