import NilBohr.Definitions

/-! Lipschitz bounds for the indicator of any proper open arc. -/

open MeasureTheory Set Metric
open scoped NNReal ENNReal

namespace NilBohr

noncomputable def OpenArc.center (J : OpenArc) : Circle :=
  ((J.start + J.length / 2 : ℝ) : Circle)

noncomputable def OpenArc.circleIndicator (J : OpenArc) : Circle → ℝ :=
  J.carrier.indicator 1

theorem OpenArc.circleIndicator_coe (J : OpenArc) (t : ℝ) :
    J.circleIndicator (t : Circle) = J.indicator t := by
  classical
  simp [OpenArc.circleIndicator, OpenArc.indicator, OpenArc.Contains, Set.indicator]

/-- The quotient description of an open arc agrees with its metric ball,
even for an arc crossing the chosen fundamental interval. -/
theorem OpenArc.carrier_eq_ball (J : OpenArc) :
    J.carrier = ball J.center (J.length / 2) := by
  ext u
  constructor
  · rintro ⟨t, ht, rfl⟩
    rw [mem_ball, OpenArc.center, dist_eq_norm, ← AddCircle.coe_sub]
    apply (torusNorm_le_abs _).trans_lt
    rw [abs_lt]
    have h₁ : J.start < t := ht.1
    have h₂ : t < J.start + J.length := ht.2
    constructor <;> linarith
  · obtain ⟨t⟩ := u
    intro hu
    change dist (t : Circle) J.center < J.length / 2 at hu
    rw [OpenArc.center, dist_eq_norm, ← AddCircle.coe_sub] at hu
    let m : ℤ := round (t - (J.start + J.length / 2))
    have hnear : |t - (J.start + J.length / 2) - (m : ℝ)| < J.length / 2 :=
      (torusNorm_eq _).symm ▸ hu
    obtain ⟨h₁, h₂⟩ := abs_lt.1 hnear
    have hm : ((m : ℝ) : Circle) = 0 :=
      (AddCircle.coe_eq_zero_iff (1 : ℝ)).2 ⟨m, by simp⟩
    refine ⟨t - (m : ℝ), ⟨by linarith, by linarith⟩, ?_⟩
    change (((t - (m : ℝ) : ℝ)) : Circle) = (t : Circle)
    simp [AddCircle.coe_sub, hm]

private theorem haar_eq_volume :
    (AddCircle.haarAddCircle : Measure Circle) = volume := by
  symm
  rw [AddCircle.volume_eq_smul_haarAddCircle]
  simp

private theorem haar_ball (c : Circle) {r : ℝ} (hr : 2 * r ≤ 1) :
    (AddCircle.haarAddCircle : Measure Circle) (ball c r) = ENNReal.ofReal (2 * r) := by
  rw [haar_eq_volume, ← measure_congr AddCircle.closedBall_ae_eq_ball,
    AddCircle.volume_closedBall, min_eq_right hr]

theorem OpenArc.haar_carrier (J : OpenArc) :
    (AddCircle.haarAddCircle : Measure Circle) J.carrier = ENNReal.ofReal J.length := by
  rw [J.carrier_eq_ball, haar_ball J.center (by linarith [J.length_lt_one])]
  congr 1
  ring

theorem OpenArc.integral_circleIndicator (J : OpenArc) :
    (∫ x, J.circleIndicator x ∂AddCircle.haarAddCircle) = J.length := by
  rw [OpenArc.circleIndicator, integral_indicator_one
    (J.carrier_eq_ball.symm ▸ measurableSet_ball),
    measureReal_def, J.haar_carrier, ENNReal.toReal_ofReal J.length_pos.le]

private noncomputable def distanceCutoff (c : Circle) (r τ : ℝ) (x : Circle) : ℝ :=
  min 1 (max 0 ((r - dist x c) / τ))

private theorem distanceCutoff_lipschitz (c : Circle) (r τ : ℝ) (hτ : 0 < τ) :
    LipschitzWith (Real.toNNReal (1 / τ)) (distanceCutoff c r τ) := by
  have hbase : LipschitzWith (Real.toNNReal (1 / τ)) (fun x : Circle => (r - dist x c) / τ) := by
    apply lipschitzWith_iff_dist_le_mul.2
    intro x y
    rw [Real.dist_eq, ← sub_div, abs_div, abs_of_pos hτ, Real.coe_toNNReal _ (by positivity)]
    have heq : r - dist x c - (r - dist y c) = dist y c - dist x c := by ring
    rw [heq, one_div_mul_eq_div]
    exact div_le_div_of_nonneg_right (abs_dist_sub_le y x c |>.trans (by rw [dist_comm])) hτ.le
  exact (hbase.const_max 0).const_min 1

private theorem distanceCutoff_nonneg (c : Circle) (r τ : ℝ) (x : Circle) :
    0 ≤ distanceCutoff c r τ x :=
  le_min (by norm_num) (le_max_left _ _)

private theorem distanceCutoff_le_one (c : Circle) (r τ : ℝ) (x : Circle) :
    distanceCutoff c r τ x ≤ 1 :=
  min_le_left _ _

private theorem distanceCutoff_eq_one (c : Circle) (r τ : ℝ) {x : Circle} (hτ : 0 < τ)
    (h : dist x c ≤ r - τ) : distanceCutoff c r τ x = 1 := by
  unfold distanceCutoff
  apply min_eq_left
  apply (le_div_iff₀ hτ).2 (by linarith) |>.trans (le_max_right _ _)

private theorem distanceCutoff_eq_zero (c : Circle) (r τ : ℝ) {x : Circle} (hτ : 0 < τ)
    (h : r ≤ dist x c) : distanceCutoff c r τ x = 0 := by
  unfold distanceCutoff
  rw [max_eq_left (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 h) hτ.le)]
  norm_num

private theorem ballIndicator_le_distanceCutoff (c : Circle) {r τ : ℝ} (hτ : 0 < τ)
    (x : Circle) : (ball c (r - τ)).indicator (1 : Circle → ℝ) x ≤ distanceCutoff c r τ x := by
  by_cases h : x ∈ ball c (r - τ)
  · rw [Set.indicator_of_mem h, distanceCutoff_eq_one c r τ hτ (mem_ball.1 h).le]
    rfl
  · rw [Set.indicator_of_not_mem h]
    exact distanceCutoff_nonneg c r τ x

private theorem distanceCutoff_le_ballIndicator (c : Circle) {r τ : ℝ} (hτ : 0 < τ)
    (x : Circle) : distanceCutoff c r τ x ≤ (ball c r).indicator (1 : Circle → ℝ) x := by
  by_cases h : x ∈ ball c r
  · rw [Set.indicator_of_mem h]
    exact distanceCutoff_le_one c r τ x
  · rw [Set.indicator_of_not_mem h, distanceCutoff_eq_zero c r τ hτ (le_of_not_gt h)]

private theorem distanceCutoff_integrable (c : Circle) (r τ : ℝ) (hτ : 0 < τ) :
    Integrable (distanceCutoff c r τ) AddCircle.haarAddCircle :=
  (distanceCutoff_lipschitz c r τ hτ).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

private theorem integral_ballIndicator (c : Circle) {r : ℝ} (hr : 0 ≤ r) (hr' : 2 * r ≤ 1) :
    (∫ x, (ball c r).indicator (1 : Circle → ℝ) x ∂AddCircle.haarAddCircle) = 2 * r := by
  rw [integral_indicator_one measurableSet_ball, measureReal_def, haar_ball c hr',
    ENNReal.toReal_ofReal (by positivity)]

/-- Lipschitz minorants and majorants with arbitrarily small integral gap.
Pointwise bounds and the mean estimate use normalized Haar measure. -/
theorem OpenArc.exists_lipschitz_sandwich (J : OpenArc) {ε : ℝ} (hε : 0 < ε) :
    ∃ (lower upper : Circle → ℝ) (K : ℝ≥0),
      LipschitzWith K lower ∧ LipschitzWith K upper ∧
      (∀ x, 0 ≤ lower x ∧ lower x ≤ J.circleIndicator x ∧
        J.circleIndicator x ≤ upper x ∧ upper x ≤ 1) ∧
      |(∫ x, lower x ∂AddCircle.haarAddCircle) - J.length| < ε ∧
      (∫ x, upper x - lower x ∂AddCircle.haarAddCircle) < ε := by
  let r := J.length / 2
  let τ := min (r / 2) (min ((1 / 2 - r) / 2) (ε / 8))
  have hr : 0 < r := by dsimp [r]; linarith [J.length_pos]
  have hr' : r < 1 / 2 := by dsimp [r]; linarith [J.length_lt_one]
  have hτ : 0 < τ := lt_min (by positivity) (lt_min (by linarith) (by positivity))
  have hτr : τ ≤ r / 2 := min_le_left _ _
  have hτr' : τ ≤ (1 / 2 - r) / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hτε : τ ≤ ε / 8 := (min_le_right _ _).trans (min_le_right _ _)
  let lower := distanceCutoff J.center r τ
  let upper := distanceCutoff J.center (r + τ) τ
  have hlo := distanceCutoff_integrable J.center r τ hτ
  have hup := distanceCutoff_integrable J.center (r + τ) τ hτ
  have hind (s : ℝ) :
      Integrable (ball J.center s |>.indicator (1 : Circle → ℝ)) AddCircle.haarAddCircle :=
    (integrable_const (1 : ℝ)).indicator measurableSet_ball
  have hlow x : lower x ≤ J.circleIndicator x := by
    rw [OpenArc.circleIndicator, J.carrier_eq_ball]
    exact distanceCutoff_le_ballIndicator J.center hτ x
  have hupper x : J.circleIndicator x ≤ upper x := by
    rw [OpenArc.circleIndicator, J.carrier_eq_ball]
    simpa only [add_sub_cancel_right] using
      (ballIndicator_le_distanceCutoff J.center (r := r + τ) hτ x)
  have hlowInt : 2 * (r - τ) ≤ ∫ x, lower x ∂AddCircle.haarAddCircle := by
    rw [← integral_ballIndicator J.center (by linarith) (by linarith)]
    exact integral_mono (hind (r - τ)) hlo (ballIndicator_le_distanceCutoff J.center hτ)
  have hupperInt : (∫ x, upper x ∂AddCircle.haarAddCircle) ≤ 2 * (r + τ) := by
    rw [← integral_ballIndicator J.center (by linarith) (by linarith)]
    exact integral_mono hup (hind (r + τ)) (distanceCutoff_le_ballIndicator J.center hτ)
  refine ⟨lower, upper, _, distanceCutoff_lipschitz _ _ _ hτ, distanceCutoff_lipschitz _ _ _ hτ,
    fun x => ⟨distanceCutoff_nonneg _ _ _ _, hlow x, hupper x, distanceCutoff_le_one _ _ _ _⟩,
    ?_, ?_⟩
  · have hJint : Integrable J.circleIndicator AddCircle.haarAddCircle := by
      rw [OpenArc.circleIndicator, J.carrier_eq_ball]
      exact hind r
    have hle := integral_mono hlo hJint hlow
    rw [J.integral_circleIndicator] at hle
    rw [abs_lt]
    dsimp only [r] at hlowInt
    constructor <;> linarith
  · rw [integral_sub hup hlo]
    linarith


/-- The density-increment minorant can have topological support strictly
inside the arc and still have positive Haar mean. -/
theorem OpenArc.exists_supported_lipschitz_minorant (J : OpenArc) :
    ∃ (F : Circle → ℝ) (K : ℝ≥0), LipschitzWith K F ∧
      tsupport F ⊆ J.carrier ∧
      (∀ x, 0 ≤ F x ∧ F x ≤ 1) ∧
      0 < (∫ x, F x ∂AddCircle.haarAddCircle) := by
  let τ := J.length / 8
  let r := J.length / 2 - τ
  let F := distanceCutoff J.center r τ
  have hτ : 0 < τ := by dsimp [τ]; linarith [J.length_pos]
  have hsmall : 0 < r - τ := by dsimp [r, τ]; linarith [J.length_pos]
  have hlip := distanceCutoff_lipschitz J.center r τ hτ
  have hF := distanceCutoff_integrable J.center r τ hτ
  refine ⟨F, _, hlip, ?_,
    fun x => ⟨distanceCutoff_nonneg _ _ _ _, distanceCutoff_le_one _ _ _ _⟩, ?_⟩
  · have hsupp : tsupport F ⊆ closedBall J.center r := by
      apply closure_minimal _ isClosed_closedBall
      intro x hx
      change F x ≠ 0 at hx
      by_contra h
      exact hx (distanceCutoff_eq_zero J.center r τ hτ (le_of_lt (lt_of_not_ge h)))
    rw [J.carrier_eq_ball]
    exact hsupp.trans (closedBall_subset_ball (by dsimp [r]; linarith))
  · have hind :
        Integrable ((ball J.center (r - τ)).indicator (1 : Circle → ℝ))
          AddCircle.haarAddCircle :=
      (integrable_const (1 : ℝ)).indicator measurableSet_ball
    have hmean := integral_mono hind hF (ballIndicator_le_distanceCutoff J.center hτ)
    rw [integral_ballIndicator J.center hsmall.le
      (by dsimp [r, τ]; linarith [J.length_lt_one])] at hmean
    linarith

end NilBohr
