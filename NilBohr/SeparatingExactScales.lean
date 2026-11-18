import NilBohr.SeparatingLogGrowth

/-! The precise logarithmic asymptotics of the Appendix A scales. -/

open Filter
open scoped Topology

namespace NilBohr

private theorem separating_log_current_atTop {β : ℝ} {r : ℕ → ℕ}
    (hr : AdmissibleBetaDenominators β r) :
    Tendsto (fun j => Real.log (r j : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hr.1.tendsto_atTop)

private theorem separating_log_next_atTop {β : ℝ} {r : ℕ → ℕ}
    (hr : AdmissibleBetaDenominators β r) :
    Tendsto (fun j => Real.log (r (j+1) : ℝ)) atTop atTop :=
  (separating_log_current_atTop hr).comp (tendsto_add_atTop_nat 1)

/-- Taking a logarithm of both of the denominator growth bounds leaves
an additive bounded error in the logarithmic growth scale. -/
theorem tendsto_logNextDenominator_div_exp_sqrt_log {β : ℝ} {r : ℕ → ℕ}
    (hr : AdmissibleBetaDenominators β r) :
    Tendsto (fun j => Real.log (r (j+1) : ℝ) / Real.exp (Real.sqrt (Real.log (r j : ℝ))))
      atTop (𝓝 1) := by
  let E (j : ℕ) := Real.exp (Real.sqrt (Real.log (r j : ℝ)))
  have hE : Tendsto E atTop atTop := by
    have hS : Tendsto (fun j => Real.sqrt (Real.log (r j : ℝ))) atTop atTop := by
      simpa only [Real.sqrt_eq_rpow, Function.comp_apply] using
        (tendsto_rpow_atTop (show 0 < (1/2 : ℝ) by norm_num)).comp
          (separating_log_current_atTop hr)
    exact Real.tendsto_exp_atTop.comp hS
  let u (j : ℕ) := Real.log (r (j+1) : ℝ)
  change Tendsto (fun j => u j / E j) atTop (𝓝 1)
  obtain ⟨_, _, _, hp, c, C, _, hc, hC, _, hG⟩ := hr
  have hb (j : ℕ) : Real.log c + E j ≤ u j ∧ u j ≤ Real.log C + E j := by
    have hj : 0 < (r (j+1) : ℝ) := by exact_mod_cast (hp (j+1)).1.pos
    constructor
    · have h := Real.log_le_log (mul_pos hc (Real.exp_pos (E j))) (hG j).1
      change Real.log (c * Real.exp (E j)) ≤ u j at h
      simpa only [Real.log_mul hc.ne' (Real.exp_pos (E j)).ne', Real.log_exp] using h
    · have h := Real.log_le_log hj (hG j).2.1
      change u j ≤ Real.log (C * Real.exp (E j)) at h
      simpa only [Real.log_mul hC.ne' (Real.exp_pos (E j)).ne', Real.log_exp] using h
  have ht (a : ℝ) : Tendsto (fun j => a/E j + 1) atTop (𝓝 1) := by
    have ha := (tendsto_const_nhds (x := a)).div_atTop hE
    simpa only [zero_add] using ha.add_const 1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (ht (Real.log c)) (ht (Real.log C)) ?_ ?_
  · apply Eventually.of_forall
    intro j
    have h₀ : 0 < E j := Real.exp_pos _
    simpa only [add_div, div_self h₀.ne'] using div_le_div_of_nonneg_right (hb j).1 h₀.le
  · apply Eventually.of_forall
    intro j
    have h₀ : 0 < E j := Real.exp_pos _
    simpa only [add_div, div_self h₀.ne'] using div_le_div_of_nonneg_right (hb j).2 h₀.le

/-- The logarithm of the rounded parameter length has exactly one fourth
the leading growth of the logarithm of the next denominator. -/
theorem tendsto_separatingLogLength_div_logNextDenominator {β : ℝ} {r : ℕ → ℕ}
    (hr : AdmissibleBetaDenominators β r) :
    Tendsto (fun j => Real.log (separatingLength (r j) (r (j+1)) : ℝ) /
      Real.log (r (j+1) : ℝ)) atTop (𝓝 (1/4)) := by
  let M (j : ℕ) := (separatingLength (r j) (r (j+1)) : ℝ)
  let R (j : ℕ) := (r (j+1) : ℝ)
  have ht := tendsto_separatingLength_div_next_fourth_root hr
  have hlog : Tendsto (fun j => Real.log (M j/(R j)^(1/4 : ℝ))) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, Real.log_one] using
      (Real.continuousAt_log one_ne_zero).tendsto.comp ht
  have herror := (hlog.div_atTop (separating_log_next_atTop hr)).add_const (1/4 : ℝ)
  have hS := eventually_separatingScale hr
  rw [zero_add] at herror
  refine herror.congr' ?_
  obtain ⟨_, _, _, hp, _⟩ := hr
  filter_upwards [hS] with j hj
  have hM : 0 < M j := by dsimp only [M]; exact_mod_cast hj.M_pos
  have hR : 1 < R j := by dsimp only [R]; exact_mod_cast (hp (j+1)).1.one_lt
  have hRpos : 0 < R j := zero_lt_one.trans hR
  change Real.log (M j/(R j)^(1/4 : ℝ))/Real.log (R j) + 1/4 = Real.log (M j)/Real.log (R j)
  rw [Real.log_div hM.ne' (Real.rpow_pos_of_pos hRpos _).ne', Real.log_rpow hRpos]
  field_simp [(Real.log_pos hR).ne']
  ring

/-- The constant in the asymptotic logarithmic parameter length is one
fourth on the exact sequence of Appendix A. -/
theorem tendsto_separatingLogLength_div_exp_sqrt_log {β : ℝ} {r : ℕ → ℕ}
    (hr : AdmissibleBetaDenominators β r) :
    Tendsto (fun j => Real.log (separatingLength (r j) (r (j+1)) : ℝ) /
      Real.exp (Real.sqrt (Real.log (r j : ℝ)))) atTop (𝓝 (1/4)) := by
  have h := (tendsto_separatingLogLength_div_logNextDenominator hr).mul
    (tendsto_logNextDenominator_div_exp_sqrt_log hr)
  rw [mul_one] at h
  refine h.congr fun j => ?_
  obtain ⟨_, _, _, hp, _⟩ := hr
  have hR : (1 : ℝ) < (r (j+1) : ℝ) := by exact_mod_cast (hp (j+1)).1.one_lt
  exact div_mul_div_cancel₀ (Real.log_pos hR).ne'

/-- Every fixed power of the logarithm of the current denominator is
negligible relative to the logarithm of the next denominator. -/
theorem tendsto_logDenominator_pow_div_logNext {β : ℝ} {r : ℕ → ℕ}
    (hr : AdmissibleBetaDenominators β r) (p : ℝ) :
    Tendsto (fun j => (Real.log (r j : ℝ))^p / Real.log (r (j+1) : ℝ)) atTop (𝓝 0) := by
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  filter_upwards [(separating_log_current_atTop hr).eventually_ge_atTop 1,
    (separating_log_next_atTop hr).eventually_ge_atTop 1,
    eventually_separatingLogPower hr p (2/ε) (by positivity)] with j hj hR hg
  let t := Real.log (r j : ℝ)
  let u := Real.log (r (j+1) : ℝ)
  have h₀ : 0 < u := zero_lt_one.trans_le hR
  have ht : 0 ≤ t^p := Real.rpow_nonneg (zero_le_one.trans hj) _
  change dist (t^p/u) 0 < ε
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg ht h₀.le)]
  have hle : t^p/u ≤ ε/2 := by
    change (2/ε)*t^p ≤ u at hg
    apply (div_le_iff₀ h₀).2
    calc
      t^p = (ε/2)*((2/ε)*t^p) := by field_simp; ring
      _ ≤ (ε/2)*u := mul_le_mul_of_nonneg_left hg (by positivity)
  linarith

/-- The logarithm of the modulus is negligible on the next-denominator
logarithmic scale. -/
theorem tendsto_logSeparatingModulus_div_logNext {β : ℝ} {r : ℕ → ℕ}
    (hr : AdmissibleBetaDenominators β r) :
    Tendsto (fun j => Real.log (separatingModulus (r j) : ℝ) /
      Real.log (r (j+1) : ℝ)) atTop (𝓝 0) := by
  have hUpper := tendsto_logDenominator_pow_div_logNext hr 2
  rw [show (2 : ℝ) = (2 : ℕ) by norm_num] at hUpper
  simp only [Real.rpow_natCast] at hUpper
  refine squeeze_zero' ?_ ?_ hUpper
  · filter_upwards [eventually_separatingScale hr, (separating_log_next_atTop hr).eventually_ge_atTop 1]
      with j hj hR
    exact div_nonneg ((by positivity : 0 ≤ (Real.log (r j : ℝ))^2/8).trans hj.log_q_lower)
      (zero_le_one.trans hR)
  · filter_upwards [eventually_separatingScale hr,
      (separating_log_current_atTop hr).eventually_ge_atTop 1,
      (separating_log_next_atTop hr).eventually_ge_atTop 1] with j hj ht hR
    have hW : (separatingW (r j) : ℝ) ≤ Real.log (r j : ℝ) :=
      Nat.floor_le (zero_le_one.trans ht)
    exact div_le_div_of_nonneg_right
      (hj.log_q_upper.trans (pow_le_pow_left₀ (Nat.cast_nonneg _) hW 2)) (zero_le_one.trans hR)

/-- The exact logarithmic meaning of `q M = r_{j+1}^{1/4+o(1)}`. -/
theorem tendsto_logSeparatingScaleX_div_logNext {β : ℝ} {r : ℕ → ℕ}
    (hr : AdmissibleBetaDenominators β r) :
    Tendsto (fun j => Real.log (separatingScaleX (r j) (r (j+1)) : ℝ) /
      Real.log (r (j+1) : ℝ)) atTop (𝓝 (1/4)) := by
  have h := (tendsto_logSeparatingModulus_div_logNext hr).add
    (tendsto_separatingLogLength_div_logNextDenominator hr)
  rw [zero_add] at h
  refine h.congr' ?_
  filter_upwards [eventually_separatingScale hr] with j hj
  have hq : (0 : ℝ) < separatingModulus (r j) := by exact_mod_cast hj.q_pos
  have hM : (0 : ℝ) < separatingLength (r j) (r (j+1)) := by exact_mod_cast hj.M_pos
  dsimp only [separatingScaleX]
  rw [Nat.cast_mul, Real.log_mul hq.ne' hM.ne', add_div]

/-- At the separating scales the original least-common-multiple modulus
divides its chosen power once the power budget is positive. -/
theorem eventually_initialModulus_dvd_separatingModulus {β : ℝ} {r : ℕ → ℕ}
    (hr : AdmissibleBetaDenominators β r) :
    ∀ᶠ j : ℕ in atTop, initialModulus (separatingW (r j)) ∣ separatingModulus (r j) := by
  filter_upwards [eventually_separatingScale hr, (separating_log_current_atTop hr).eventually_ge_atTop 1]
    with j hj ht
  have he : separatingExponent (r j) ≠ 0 := by
    intro he
    have hq : separatingModulus (r j) = 1 := by simp only [separatingModulus, he, pow_zero]
    have h := hj.log_q_lower
    rw [hq, Nat.cast_one, Real.log_one] at h
    nlinarith only [h, ht, sq_nonneg (Real.log (r j : ℝ) - 1)]
  exact dvd_pow_self _ he

private theorem separating_log_spatialScale_atTop {β : ℝ} {r : ℕ → ℕ}
    (hr : AdmissibleBetaDenominators β r) :
    Tendsto (fun j => Real.log (separatingSpatialScale (r j) (r (j+1)) : ℝ)) atTop atTop :=
  tendsto_atTop_mono' _ ((eventually_separatingScale hr).mono fun _ h =>
    h.log_length_le_spatialScale) (Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_separatingLength hr)))

private theorem eventually_logDenominator_sq_le_logSpatialScale_pow {β : ℝ} {r : ℕ → ℕ}
    (hr : AdmissibleBetaDenominators β r) {p : ℝ} (hp : 0 < p) :
    ∀ᶠ j : ℕ in atTop, (Real.log (r j : ℝ))^2 ≤
      (Real.log (separatingSpatialScale (r j) (r (j+1)) : ℝ))^p := by
  have hS := eventually_separatingScale hr
  have hL := eventually_separatingLogPower hr (2/p) 5 (by norm_num)
  have ht := (separating_log_current_atTop hr).eventually_ge_atTop 1
  obtain ⟨_, _, _, hPrime, _⟩ := hr
  filter_upwards [hS,hL,ht] with j hj hL ht
  let t := Real.log (r j : ℝ)
  let u := Real.log (separatingSpatialScale (r j) (r (j+1)) : ℝ)
  have ht₀ : 0 ≤ t := zero_le_one.trans ht
  have hL' : t^(2/p) ≤ Real.log (r (j+1) : ℝ)/5 :=
    (le_div_iff₀ (by norm_num : 0 < (5:ℝ))).2 (by simpa only [mul_comm] using hL)
  have he : t^(2/p) ≤ u := (hL'.trans (hj.log_length_lower (hPrime (j+1)).1.pos)).trans
    hj.log_length_le_spatialScale
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg ht₀ _) he hp.le
  rwa [← Real.rpow_mul ht₀, div_mul_cancel₀ _ hp.ne', Real.rpow_two] at hpow

private theorem tendsto_logDenominator_sq_div_logSpatialScale_pow {β : ℝ} {r : ℕ → ℕ}
    (hr : AdmissibleBetaDenominators β r) {p : ℝ} (hp : 0 < p) :
    Tendsto (fun j => (Real.log (r j : ℝ))^2 /
      (Real.log (separatingSpatialScale (r j) (r (j+1)) : ℝ))^p) atTop (𝓝 0) := by
  let u (j : ℕ) := Real.log (separatingSpatialScale (r j) (r (j+1)) : ℝ)
  have hu : Tendsto u atTop atTop := separating_log_spatialScale_atTop hr
  have hp₂ : 0 < p/2 := by positivity
  refine squeeze_zero' (Eventually.of_forall fun _ => div_nonneg (sq_nonneg _)
    (Real.rpow_nonneg (Real.log_natCast_nonneg _) _)) ?_ ((tendsto_rpow_neg_atTop hp₂).comp hu)
  filter_upwards [eventually_logDenominator_sq_le_logSpatialScale_pow hr hp₂,
    hu.eventually_ge_atTop 1] with j hj h₁
  have hu' : 0 < u j := zero_lt_one.trans_le h₁
  change (Real.log (r j : ℝ))^2/(u j)^p ≤ (u j)^(-(p/2))
  calc
    _ ≤ (u j)^(p/2)/(u j)^p := div_le_div_of_nonneg_right hj (Real.rpow_nonneg hu'.le _)
    _ = _ := by rw [← Real.rpow_sub hu']; congr 1; ring

/-- The scale cutoff `w` is smaller than every positive power of the
logarithm of the spatial scale. -/
theorem tendsto_separatingW_div_logSpatialScale_pow {β : ℝ} {r : ℕ → ℕ}
    (hr : AdmissibleBetaDenominators β r) {p : ℝ} (hp : 0 < p) :
    Tendsto (fun j => (separatingW (r j) : ℝ) /
      (Real.log (separatingSpatialScale (r j) (r (j+1)) : ℝ))^p) atTop (𝓝 0) := by
  refine squeeze_zero' (Eventually.of_forall fun _ => div_nonneg (Nat.cast_nonneg _)
    (Real.rpow_nonneg (Real.log_natCast_nonneg _) _)) ?_
      (tendsto_logDenominator_sq_div_logSpatialScale_pow hr hp)
  filter_upwards [(separating_log_current_atTop hr).eventually_ge_atTop 1] with j ht
  have ht₀ := zero_le_one.trans ht
  have hw : (separatingW (r j) : ℝ) ≤ Real.log (r j : ℝ) := Nat.floor_le ht₀
  have hsq : Real.log (r j : ℝ) ≤ (Real.log (r j : ℝ))^2 := by
    nlinarith only [mul_nonneg ht₀ (sub_nonneg.mpr ht)]
  exact div_le_div_of_nonneg_right (hw.trans hsq)
    (Real.rpow_nonneg (Real.log_natCast_nonneg _) _)

/-- In particular `log q` is little-oh of the square root of `log N` as
required by the smooth-modulus argument. -/
theorem tendsto_logSeparatingModulus_div_sqrt_logSpatialScale {β : ℝ} {r : ℕ → ℕ}
    (hr : AdmissibleBetaDenominators β r) :
    Tendsto (fun j => Real.log (separatingModulus (r j) : ℝ) /
      Real.sqrt (Real.log (separatingSpatialScale (r j) (r (j+1)) : ℝ))) atTop (𝓝 0) := by
  simp_rw [Real.sqrt_eq_rpow]
  refine squeeze_zero' (Eventually.of_forall fun _ => div_nonneg (Real.log_natCast_nonneg _)
    (Real.rpow_nonneg (Real.log_natCast_nonneg _) _)) ?_
      (tendsto_logDenominator_sq_div_logSpatialScale_pow hr (p := 1/2) (by norm_num))
  filter_upwards [eventually_separatingScale hr,
    (separating_log_current_atTop hr).eventually_ge_atTop 1] with j hj ht
  have hw : (separatingW (r j) : ℝ) ≤ Real.log (r j : ℝ) := Nat.floor_le (zero_le_one.trans ht)
  exact div_le_div_of_nonneg_right
    (hj.log_q_upper.trans (pow_le_pow_left₀ (Nat.cast_nonneg _) hw 2))
    (Real.rpow_nonneg (Real.log_natCast_nonneg _) _)

/-- The coefficient factor in the quadratic Weyl bound is negligible
against every fixed positive power of the length on the residue class. -/
theorem tendsto_separatingCoefficient_div_lengthQuotient_pow {β : ℝ} {r : ℕ → ℕ}
    (hr : AdmissibleBetaDenominators β r) (a : ℕ → ℕ) (ha : ∀ j, a j ≤ r j)
    {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun j => (a j : ℝ)*(separatingModulus (r j) : ℝ)^2*(r j : ℝ) /
      (separatingLengthQuotient (r j) (r (j+1)) : ℝ)^γ) atTop (𝓝 0) := by
  let H (j : ℕ) : ℝ := separatingLengthQuotient (r j) (r (j+1))
  have hH : Tendsto H atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_separatingLengthQuotient hr)
  have hγ₂ : 0 < γ/2 := by positivity
  refine squeeze_zero' (Eventually.of_forall fun _ => by positivity) ?_
    ((tendsto_rpow_neg_atTop hγ₂).comp hH)
  filter_upwards [eventually_separatingLengthQuotient_subpower hr 2 2 hγ₂,
    hH.eventually_gt_atTop 0] with j hj hpos
  change (a j : ℝ)*(separatingModulus (r j) : ℝ)^2*(r j : ℝ)/(H j)^γ ≤ (H j)^(-(γ/2))
  have ha' : (a j : ℝ) ≤ r j := by exact_mod_cast ha j
  calc
    _ ≤ ((separatingModulus (r j) : ℝ)^2*(r j : ℝ)^2)/(H j)^γ := by
      apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg hpos.le _)
      calc
        _ ≤ (r j : ℝ)*(separatingModulus (r j) : ℝ)^2*(r j : ℝ) := by gcongr
        _ = _ := by ring
    _ ≤ (H j)^(γ/2)/(H j)^γ := div_le_div_of_nonneg_right hj (Real.rpow_nonneg hpos.le _)
    _ = _ := by rw [← Real.rpow_sub hpos]; congr 1; ring

end NilBohr
