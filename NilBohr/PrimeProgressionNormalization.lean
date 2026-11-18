import NilBohr.BohrPeriodic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! The logarithmic-integral and elementary normalizations of the
fixed-modulus prime number theorem give the same limiting ratio. -/

namespace NilBohr

open Filter MeasureTheory Set intervalIntegral
open scoped Topology

/-- The logarithmic integral starting at two. The constant lower endpoint
does not affect the prime count asymptotic. -/
noncomputable def logarithmicIntegral (x : ℝ) : ℝ :=
  ∫ t in (2 : ℝ)..x, (Real.log t)⁻¹

private theorem intervalIntegrable_inv_log {u v : ℝ} (h₂ : 2 ≤ u) (huv : u ≤ v) :
    IntervalIntegrable (fun t => (Real.log t)⁻¹) volume u v := by
  apply ContinuousOn.intervalIntegrable_of_Icc huv
  apply (Real.continuousOn_log.mono ?_).inv₀
  · intro t ht
    exact (Real.log_pos (by linarith [ht.1])).ne'
  · intro t ht
    simp only [mem_compl_iff, mem_singleton_iff]
    linarith [ht.1]

/-- At infinity, the integral of (1/\log t) from two to the cutoff is
asymptotic to the cutoff divided by its logarithm. -/
theorem logarithmicIntegral_normalization_tendsto :
    Tendsto (fun x : ℝ => logarithmicIntegral x * (Real.log x / x)) atTop (𝓝 1) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    have ht : Tendsto (fun x : ℝ => 1 - 2 / x) atTop (𝓝 1) := by
      simpa only [div_eq_mul_inv, mul_zero, sub_zero] using
        (tendsto_inv_atTop_zero.const_mul (2 : ℝ)).const_sub 1
    filter_upwards [eventually_ge_atTop (2 : ℝ), ht.eventually_const_lt hb] with x hx hbx
    have hlx : 0 < Real.log x := Real.log_pos (by linarith)
    have hx0 : 0 < x := by linarith
    have hLow : (x - 2) * (Real.log x)⁻¹ ≤ logarithmicIntegral x := by
      unfold logarithmicIntegral
      rw [← smul_eq_mul, ← intervalIntegral.integral_const]
      apply intervalIntegral.integral_mono_on hx intervalIntegrable_const
        (intervalIntegrable_inv_log le_rfl hx)
      intro t ht
      exact (inv_le_inv₀ hlx (Real.log_pos (by linarith [ht.1]))).mpr
        (Real.log_le_log (by linarith [ht.1]) ht.2)
    apply hbx.trans_le
    calc
      1 - 2 / x = ((x - 2) * (Real.log x)⁻¹) * (Real.log x / x) := by
        field_simp [hx0.ne', hlx.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_right hLow (by positivity)
  · intro b hb
    let a : ℝ := 2 / (1 + b)
    have hden : 0 < 1 + b := by linarith
    have ha : 0 < a := div_pos (by norm_num) hden
    have ha' : a < 1 := (div_lt_one hden).mpr (by linarith)
    have hib : a⁻¹ < b := by
      rw [show a⁻¹ = (1+b) / 2 by dsimp [a]; rw [inv_div]]
      linarith
    have ht₀ := (isLittleO_log_rpow_atTop (sub_pos.mpr ha')).tendsto_div_nhds_zero
    have ht : Tendsto (fun x : ℝ => (Real.log 2)⁻¹ * (Real.log x / x^(1-a)) + a⁻¹)
        atTop (𝓝 (a⁻¹)) := by
      simpa only [mul_zero, zero_add] using (ht₀.const_mul (Real.log 2)⁻¹).add_const a⁻¹
    filter_upwards [eventually_ge_atTop (2 : ℝ),
        (tendsto_rpow_atTop ha).eventually_ge_atTop (2 : ℝ), ht.eventually_lt_const hib]
      with x hx hxa hlim
    have hlx : 0 < Real.log x := Real.log_pos (by linarith)
    have hx0 : 0 < x := by linarith
    have hmid : x^a ≤ x := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le (show 1 ≤ x by linarith) ha'.le
    have h₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hLeft : (∫ t in (2 : ℝ)..x^a, (Real.log t)⁻¹) ≤ (x^a - 2) * (Real.log 2)⁻¹ := by
      rw [← smul_eq_mul, ← intervalIntegral.integral_const]
      apply intervalIntegral.integral_mono_on hxa (intervalIntegrable_inv_log le_rfl hxa)
        intervalIntegrable_const
      intro t ht
      exact (inv_le_inv₀ (Real.log_pos (by linarith [ht.1])) h₂).mpr
        (Real.log_le_log (by norm_num) ht.1)
    have hRight : (∫ t in x^a..x, (Real.log t)⁻¹) ≤ (x - x^a) * (a * Real.log x)⁻¹ := by
      rw [← smul_eq_mul, ← intervalIntegral.integral_const]
      apply intervalIntegral.integral_mono_on hmid (intervalIntegrable_inv_log hxa hmid)
        intervalIntegrable_const
      intro t ht
      apply (inv_le_inv₀ (Real.log_pos (by linarith [hxa, ht.1])) (mul_pos ha hlx)).mpr
      rw [← Real.log_rpow hx0]
      exact Real.log_le_log (Real.rpow_pos_of_pos hx0 _) ht.1
    have hUp : logarithmicIntegral x ≤ x^a * (Real.log 2)⁻¹ + x * (a * Real.log x)⁻¹ := by
      unfold logarithmicIntegral
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_inv_log le_rfl hxa) (intervalIntegrable_inv_log hxa hmid)]
      apply (add_le_add hLeft hRight).trans
      gcongr
      · linarith
      · exact sub_le_self _ (Real.rpow_nonneg hx0.le _)
    apply lt_of_le_of_lt (mul_le_mul_of_nonneg_right hUp (by positivity))
    convert hlim using 1
    have hp : x ^ a / x = (x ^ (1-a))⁻¹ := by
      rw [← Real.rpow_sub_one hx0.ne', ← Real.rpow_neg hx0.le]
      congr 1
      ring
    rw [add_mul, show x^a * (Real.log 2)⁻¹ * (Real.log x / x) =
      (Real.log 2)⁻¹ * Real.log x * (x^a / x) by ring, hp]
    rw [show x * (a * Real.log x)⁻¹ * (Real.log x / x) = a⁻¹ by
      field_simp [ha.ne', hx0.ne', hlx.ne']
      ring]
    rw [div_eq_mul_inv]
    ring

/-- The fixed-progression prime number theorem in logarithmic-integral
normalization implies the project's equivalent count normalization. -/
theorem PrimeNumberTheoremInProgressions.of_logarithmicIntegral
    (h : ∀ (q a : ℕ), 0 < q → Nat.Coprime a q →
      Tendsto (fun N : ℕ => ((primesSatisfyingThrough (fun p => p ≡ a [MOD q]) N).card : ℝ) /
        logarithmicIntegral (N : ℝ)) atTop (𝓝 ((q.totient : ℝ)⁻¹))) :
    PrimeNumberTheoremInProgressions := by
  intro q a hq ha
  have hl := logarithmicIntegral_normalization_tendsto.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have ht := (h q a hq ha).mul hl
  rw [mul_one] at ht
  apply ht.congr'
  filter_upwards [hl.eventually_const_lt (by norm_num : (0 : ℝ) < 1)] with N hpos
  change 0 < logarithmicIntegral (N : ℝ) * (Real.log (N : ℝ) / (N : ℝ)) at hpos
  have hne : logarithmicIntegral (N : ℝ) ≠ 0 := by
    intro he
    simp [he] at hpos
  change (_ / logarithmicIntegral (N : ℝ)) *
    (logarithmicIntegral (N : ℝ) * (Real.log (N : ℝ) / (N : ℝ))) = _
  rw [← mul_assoc, div_mul_cancel₀ _ hne]
  ring

end NilBohr
