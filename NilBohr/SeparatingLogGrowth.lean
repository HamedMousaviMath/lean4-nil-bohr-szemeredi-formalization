import NilBohr.SeparatingScaleConstruction

/-! Logarithmic comparisons for the particular scales in Appendix A. -/

open Filter
open scoped Topology

namespace NilBohr

/-- In the same construction the logarithm of the denominator is
little-oh of the logarithm of the modulus. -/
theorem tendsto_logDenominator_div_logSeparatingModulus {β : ℝ} {r : ℕ → ℕ}
    (hr : AdmissibleBetaDenominators β r) :
    Tendsto (fun j : ℕ => Real.log (r j : ℝ) / Real.log (separatingModulus (r j) : ℝ))
      atTop (𝓝 0) := by
  have ht : Tendsto (fun j => Real.log (r j : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hr.1.tendsto_atTop)
  have hzero : Tendsto (fun j => 8 / Real.log (r j : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using
      (tendsto_inv_atTop_zero.comp ht).const_mul 8
  apply squeeze_zero' _ _ hzero
  · filter_upwards [eventually_separatingScale hr, ht.eventually_ge_atTop 1] with j hj ht₁
    have hlogq : 0 ≤ Real.log (separatingModulus (r j) : ℝ) :=
      (by positivity : 0 ≤ (Real.log (r j : ℝ))^2/8).trans hj.log_q_lower
    exact div_nonneg (zero_le_one.trans ht₁) hlogq
  · filter_upwards [eventually_separatingScale hr, ht.eventually_ge_atTop 1] with j hj ht₁
    let t := Real.log (r j : ℝ)
    have ht' : 0 < t := zero_lt_one.trans_le ht₁
    calc
      _ ≤ t/(t^2/8) := div_le_div_of_nonneg_left ht'.le (by positivity) hj.log_q_lower
      _ = 8/t := by field_simp; ring

/-- The maximal power of the smooth modulus fills the logarithmic budget
up to a relative error tending to zero. -/
theorem tendsto_logSeparatingModulus_div_w_sq {β : ℝ} {r : ℕ → ℕ}
    (hr : AdmissibleBetaDenominators β r) :
    Tendsto (fun j : ℕ => Real.log (separatingModulus (r j) : ℝ) /
      (separatingW (r j) : ℝ)^2) atTop (𝓝 1) := by
  let w (j : ℕ) := separatingW (r j)
  let q (j : ℕ) := separatingModulus (r j)
  have ht : Tendsto (fun j => Real.log (r j : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hr.1.tendsto_atTop)
  have hwTop : Tendsto (fun j => (w j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_nat_floor_atTop.comp ht)
  have he : Tendsto (fun j => Real.log (w j : ℝ)/(w j : ℝ)) atTop (𝓝 0) := by
    simpa only [pow_one, one_mul, add_zero, Function.comp_apply] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hwTop
  have hZero : Tendsto (fun j => 1-Real.log (q j : ℝ)/(w j : ℝ)^2) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ he
    · filter_upwards [eventually_separatingScale hr] with j hj
      have hw' : (0 : ℝ) < w j := by exact_mod_cast (show 0 < w j by have := hj.w_large; dsimp [w]; omega)
      exact sub_nonneg.mpr ((div_le_one (pow_pos hw' _)).mpr hj.log_q_upper)
    · filter_upwards [eventually_separatingScale hr] with j hj
      let m := initialModulus (w j)
      let e := separatingExponent (r j)
      have hm : 16 ∣ m := Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr ⟨by decide, hj.w_large⟩)
      have hm' : (1 : ℝ) < m := by
        have h := Nat.le_of_dvd (initialModulus_pos _) hm
        exact_mod_cast (show 1 < m by omega)
      have hlogm := Real.log_pos hm'
      have hw' : (0 : ℝ) < w j := by exact_mod_cast (show 0 < w j by have := hj.w_large; dsimp [w]; omega)
      have hlogq : Real.log (q j : ℝ) = (e : ℝ)*Real.log (m : ℝ) := by
        rw [show (q j : ℝ) = (m : ℝ)^e by simp [q, m, e, w, separatingModulus],
          Real.log_pow]
      have hfloor : (w j : ℝ)^2/Real.log (m : ℝ) < (e : ℝ)+1 := Nat.lt_floor_add_one _
      have hbudget : (w j : ℝ)^2 - Real.log (q j : ℝ) ≤ Real.log (m : ℝ) := by
        have h := (div_lt_iff₀ hlogm).mp hfloor
        rw [hlogq]
        linarith only [h]
      calc
        1-Real.log (q j : ℝ)/(w j : ℝ)^2 =
            ((w j : ℝ)^2-Real.log (q j : ℝ))/(w j : ℝ)^2 := by
          rw [sub_div, div_self (pow_ne_zero _ hw'.ne')]
        _ ≤ Real.log (m : ℝ)/(w j : ℝ)^2 :=
          div_le_div_of_nonneg_right hbudget (sq_nonneg _)
        _ ≤ ((w j : ℝ)*Real.log (w j : ℝ))/(w j : ℝ)^2 :=
          div_le_div_of_nonneg_right (log_initialModulus_le _) (sq_nonneg _)
        _ = Real.log (w j : ℝ)/(w j : ℝ) := by field_simp; ring
  simpa only [sub_sub_cancel, sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub hZero

/-- The rounded length is asymptotic to the prescribed fourth root. -/
theorem tendsto_separatingLength_div_next_fourth_root {β : ℝ} {r : ℕ → ℕ}
    (hr : AdmissibleBetaDenominators β r) :
    Tendsto (fun j : ℕ =>
      (separatingLength (r j) (r (j+1)) : ℝ) / (r (j+1) : ℝ)^(1/4 : ℝ))
      atTop (𝓝 1) := by
  let s (j : ℕ) := (r (j+1) : ℝ)^(1/4 : ℝ)/(r j : ℝ)
  have hH : Tendsto (fun j => (separatingLengthQuotient (r j) (r (j+1)) : ℝ))
      atTop atTop := tendsto_natCast_atTop_atTop.comp (tendsto_separatingLengthQuotient hr)
  have hS : Tendsto s atTop atTop := by
    apply tendsto_atTop_mono' atTop ?_ hH
    apply Eventually.of_forall
    intro j
    exact Nat.floor_le (by positivity)
  refine (tendsto_nat_floor_div_atTop.comp hS).congr' (Eventually.of_forall fun j => ?_)
  change (separatingLengthQuotient (r j) (r (j+1)) : ℝ) / s j =
    (separatingLength (r j) (r (j+1)) : ℝ) / (r (j+1) : ℝ)^(1/4 : ℝ)
  rw [show (separatingLength (r j) (r (j+1)) : ℝ) =
    (r j : ℝ)*(separatingLengthQuotient (r j) (r (j+1)) : ℝ) by simp [separatingLength]]
  dsimp only [s]
  rw [div_div_eq_mul_div, mul_comm]

end NilBohr
