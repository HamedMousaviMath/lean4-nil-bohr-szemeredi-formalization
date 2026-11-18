import NilBohr.GreenTaoObstructions
import NilBohr.HeisenbergCutoff
import NilBohr.SeparatingFourier
import NilBohr.GowersOrderComparison
import NilBohr.GowersTriangle
import NilBohr.LipschitzFourier

/-! The quantitative ambient Gowers obstruction for a prescribed vertical
frequency and a prescribed short horizontal cutoff. -/

open AddCircle Filter MeasureTheory
open scoped Topology NNReal BigOperators

namespace NilBohr

private theorem ambientChartAverage_tendsto
    (hScalar : ScalarHeisenbergObstruction) (α β : ℝ) (hα : BadlyApproximable α)
    {r : ℕ → ℕ} (hr : AdmissibleBetaDenominators β r)
    (Φ : HeisenbergPoint → ℂ) (U : ℝ) (hΦ : HeisenbergLipschitzNormLE Φ U) :
    Tendsto (fun M : ℕ => heisenbergOrbitAverage α β 0 1 1 M Φ) atTop
      (𝓝 (heisenbergChartMean Φ)) := by
  have hbracket := (heisenberg_horizontal_for_denominators α β hα hr).1
  have hscalar := scalar_heisenberg_equidistribution_for_denominators hScalar α β hα hr
    1 0 one_pos
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht : Tendsto (fun M : ℕ => Real.log (M : ℝ) ^ (-(1 : ℝ)) * U) atTop (𝓝 0) := by
    have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [Function.comp_apply, zero_mul] using
      ((tendsto_rpow_neg_atTop one_pos).comp hlog).mul_const U
  refine squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ ht
  filter_upwards [tendsto_natCast_atTop_atTop.eventually (hbracket.and hscalar),
    eventually_ge_atTop (1 : ℕ)] with M ⟨hbr, hsc⟩ hM
  obtain ⟨j, hjlo, hjhi⟩ := hbr
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hprime : (r j).Prime := by
    obtain ⟨_, _, _, hp, _⟩ := hr
    exact (hp j).1
  have hnot : ¬ r j ∣ 1 := fun hd => hprime.ne_one (Nat.dvd_one.mp hd)
  have hv : (1 : ℝ) ≤ (M : ℝ) ^ (1 / 5000 : ℝ) :=
    Real.one_le_rpow hM' (by norm_num)
  have hK : (M : ℝ) ^ (1 / 3 : ℝ) ≤ (M : ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hM' (show (1 / 3 : ℝ) ≤ 1 by norm_num)
  exact hsc j hjlo hjhi 0 1 1 M one_pos (by simpa only [Nat.cast_one] using hv)
    hnot one_pos (by simp) hK Φ U hΦ

private theorem heisenbergLipschitzNormLE_mul {Φ Ψ : HeisenbergPoint → ℂ} {U V : ℝ}
    (hΦ : HeisenbergLipschitzNormLE Φ U) (hΨ : HeisenbergLipschitzNormLE Ψ V) :
    ∃ B : ℝ, HeisenbergLipschitzNormLE (fun g => Φ g * Ψ g) B := by
  obtain ⟨hΦinv, S, L, hS, hL, _, hΦsup, hΦdist⟩ := hΦ
  obtain ⟨hΨinv, T, K, hT, hK, _, hΨsup, hΨdist⟩ := hΨ
  refine ⟨S*T+(L*T+S*K), ?_, S*T, L*T+S*K, by positivity, by positivity, le_rfl, ?_, ?_⟩
  · intro g u v w
    dsimp only
    rw [hΦinv, hΨinv]
  · intro g
    rw [norm_mul]
    exact mul_le_mul (hΦsup g) (hΨsup g) (norm_nonneg _) hS
  · intro g h
    rw [show Φ g * Ψ g - Φ h * Ψ h = (Φ g - Φ h) * Ψ g + Φ h * (Ψ g - Ψ h) by ring]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    exact (add_le_add (mul_le_mul (hΦdist g h) (hΨsup g) (norm_nonneg _)
      ((norm_nonneg _).trans (hΦdist g h)))
      (mul_le_mul (hΦsup h) (hΨdist g h) (norm_nonneg _) hS)).trans_eq (by ring)

private theorem prescribedCutoff_mul_seam (χ : C(Circle, ℝ)) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : hi < 1)
    (hχ : ∀ x ∈ Set.Ico (0 : ℝ) 1, χ (x : Circle) ≠ 0 → x ∈ Set.Icc lo hi)
    (x : ℝ) : χ (x : Circle) * heisenbergSeamCutoff (min lo (1-hi)/2) (x : Circle) =
      χ (x : Circle) := by
  by_cases hz : χ (x : Circle) = 0
  · simp [hz]
  have hco : ((Int.fract x : ℝ) : Circle) = (x : Circle) := AddCircle.coe_fract x
  have hx := hχ (Int.fract x) ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
    (fun h => hz (by simpa only [hco] using h))
  have hdist : min lo (1-hi) ≤ ‖(x : Circle)‖ := by
    rw [← hco]
    change min lo (1-hi) ≤ torusNorm (Int.fract x)
    rw [torusNorm_eq]
    by_cases hround : (round (Int.fract x) : ℤ) ≤ 0
    · have hround' : ((round (Int.fract x) : ℤ) : ℝ) ≤ 0 := by exact_mod_cast hround
      exact (min_le_left _ _).trans (hx.1.trans (by
        linarith only [hround', le_abs_self (Int.fract x - round (Int.fract x))]))
    · have hround' : (1 : ℝ) ≤ ((round (Int.fract x) : ℤ) : ℝ) := by
        exact_mod_cast (show (1 : ℤ) ≤ round (Int.fract x) by omega)
      exact (min_le_right _ _).trans ((sub_le_sub hround' hx.2).trans
        (by simpa only [neg_sub] using neg_le_abs (Int.fract x - round (Int.fract x))))
  have hε : 0 < min lo (1-hi)/2 := half_pos (lt_min hlo (sub_pos.mpr hhi))
  rw [heisenbergSeamCutoff_eq_one hε (by linarith only [hdist]), mul_one]

private theorem lipschitzWith_mul_circle_fourier (G : C(Circle, ℂ)) {κ : ℝ≥0}
    (hG : LipschitzWith κ G) (k : ℤ) :
    ∃ L : ℝ≥0, LipschitzWith L (G * fourier (T := 1) k : C(Circle, ℂ)) := by
  obtain ⟨κk, hk⟩ := exists_lipschitzWith_fourier k
  refine ⟨κ + ‖G‖₊ * κk, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  let c := fourier (T := 1) k
  change dist (G x * c x) (G y * c y) ≤ _ * dist x y
  have hg := hG.dist_le_mul x y
  have hc := hk.dist_le_mul x y
  have hcx : ‖c x‖ = 1 := by
    rw [show c x = fourier (T := 1) k x from rfl, fourier_apply]
    exact _root_.Circle.norm_coe _
  simp only [dist_eq_norm] at hg hc ⊢
  rw [show G x * c x - G y * c y = (G x - G y) * c x + G y * (c x - c y) by ring]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, hcx, mul_one]
  exact (add_le_add hg (mul_le_mul (G.norm_coe_le_norm y) hc (norm_nonneg _)
    (norm_nonneg _))).trans_eq (by push_cast; ring)

/-- A prescribed interior cutoff and prescribed nonzero vertical mode have
the expected correlation with the centered selector along every large
ambient interval. -/
theorem tendsto_ambient_centered_localized_mode
    (hScalar : ScalarHeisenbergObstruction) (α β : ℝ) (hα : BadlyApproximable α)
    (hβ : AdmissibleBeta β) (F : C(Circle, ℂ)) {κF : ℝ≥0} (hF : LipschitzWith κF F)
    (h : ℤ) (hh : h ≠ 0) (χ : C(Circle, ℝ)) {κχ : ℝ≥0} (hχLip : LipschitzWith κχ χ)
    {lo hi : ℝ} (hlo : 0 < lo) (hhi : hi < 1)
    (hχ : ∀ x ∈ Set.Ico (0 : ℝ) 1, χ (x : Circle) ≠ 0 → x ∈ Set.Icc lo hi) :
    Tendsto (fun M : ℕ => (∑ n ∈ positiveInterval M,
      (F (heisenbergPhase α β n : Circle) - circleMean F) *
      (χ ((β * (n : ℝ) : ℝ) : Circle) : ℂ) *
      phaseExponential (((-h : ℤ) : ℝ) * heisenbergPhase α β n)) / (M : ℂ))
      atTop (𝓝 (fourierCoeff F h * ((∫ x, χ x ∂haarAddCircle : ℝ) : ℂ))) := by
  obtain ⟨_, _, r, hr⟩ := (admissibleBeta_iff_exists_denominators β).mp hβ
  let ε := min lo (1-hi)/2
  have hε : 0 < ε := half_pos (lt_min hlo (sub_pos.mpr hhi))
  let G : C(Circle, ℂ) := F - ContinuousMap.const Circle (circleMean F)
  let H : C(Circle, ℂ) := G * fourier (T := 1) (-h)
  have hG : LipschitzWith κF G := by
    simpa [G] using hF.sub (LipschitzWith.const (α := Circle) (circleMean F))
  obtain ⟨L, hH⟩ := lipschitzWith_mul_circle_fourier G hG (-h)
  have hH' : LipschitzWith L H := hH
  let z := fourierCoeff F h
  have hz : circleMean H = z := circleMean_centered_mul_fourier F hh
  let Ψ : HeisenbergPoint → ℂ := fun g => χ (g.2.1 : Circle)
  let Φ : HeisenbergPoint → ℂ := fun g => Ψ g * heisenbergCenteredTest H ε g
  have hΨlip : HeisenbergLipschitzNormLE Ψ _ := horizontalCircle_lipschitzNorm χ hχLip
  obtain ⟨U, _, hTest⟩ := heisenbergCenteredTest_lipschitz H hH'
  obtain ⟨B, hΦlip⟩ := heisenbergLipschitzNormLE_mul hΨlip (hTest ε hε)
  have hΦmean : heisenbergChartMean Φ = 0 := by
    simp only [heisenbergChartMean, Φ, Ψ, intervalIntegral.integral_const_mul,
      heisenbergCenteredTest_verticalMean_zero H hH' ε, mul_zero, intervalIntegral.integral_zero]
  have hΨmean : heisenbergChartMean Ψ = (((∫ x, χ x ∂haarAddCircle) : ℝ) : ℂ) :=
    horizontalCircle_chartMean χ
  have hΦlim := ambientChartAverage_tendsto hScalar α β hα hr Φ B hΦlip
  have hΨlim := ambientChartAverage_tendsto hScalar α β hα hr Ψ _ hΨlip
  rw [hΦmean] at hΦlim
  rw [hΨmean] at hΨlim
  have hsum := hΦlim.add (hΨlim.const_mul z)
  simp only [zero_add] at hsum
  refine hsum.congr ?_
  intro M
  let W (n : ℤ) := (F (heisenbergPhase α β n : Circle) - circleMean F) *
    (χ ((β * (n : ℝ) : ℝ) : Circle) : ℂ) *
    phaseExponential (((-h : ℤ) : ℝ) * heisenbergPhase α β n)
  have hw (n : ℤ) : Φ (heisenbergOrbit α β n) + z * Ψ (heisenbergOrbit α β n) = W n := by
    have hχseam := congrArg (fun x : ℝ => (x : ℂ))
      (prescribedCutoff_mul_seam χ hlo hhi hχ (β * (n : ℝ)))
    push_cast at hχseam
    change (χ ((β * (n : ℝ) : ℝ) : Circle) : ℂ) *
      (heisenbergSeamCutoff ε ((β * (n : ℝ) : ℝ) : Circle) : ℂ) = _ at hχseam
    unfold Φ
    rw [heisenbergCenteredTest_orbit, hz]
    simp only [Ψ, heisenbergOrbit, mul_comm (n : ℝ) β, ← mul_assoc, hχseam, W,
      H, G, ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.const_apply]
    simp only [fourier_coe_apply, Complex.ofReal_one, div_one, phaseExponential,
      Complex.ofReal_mul, Complex.ofReal_intCast, mul_assoc]
    ring
  have hdil (n : ℤ) : dilatedHeisenbergOrbit α β 1 n = heisenbergOrbit α β n := by
    rcases he : heisenbergOrbit α β n with ⟨x, y, w⟩
    simp [dilatedHeisenbergOrbit, he]
  change heisenbergOrbitAverage α β 0 1 1 M Φ + z * heisenbergOrbitAverage α β 0 1 1 M Ψ =
    (∑ n ∈ positiveInterval M, W n) / (M : ℂ)
  simp only [heisenbergOrbitAverage, zero_add, Nat.cast_one, one_mul, hdil,
    ← mul_div_assoc, Finset.mul_sum, ← add_div, ← Finset.sum_add_distrib, hw]

/-- The introduction's quantitative obstruction with both the mode and the
nonnegative short cutoff prescribed. The multiplicative constant is chosen
from the order-three mean inequality, before the selector data and cutoff. -/
theorem ambient_centered_gowers_prescribed_cutoff :
    ∃ D : ℝ, 0 < D ∧ ∀ (_ : GreenTaoQuantitativeLeibman) (α β : ℝ),
      BadlyApproximable α → AdmissibleBeta β →
      ∀ (F : C(Circle, ℂ)) {κF : ℝ≥0}, LipschitzWith κF F →
      ∀ h : ℤ, h ≠ 0 → fourierCoeff F h ≠ 0 →
      ∀ (χ : C(Circle, ℝ)) {κχ : ℝ≥0}, LipschitzWith κχ χ →
      (∀ x, 0 ≤ χ x) → (∃ x, χ x ≠ 0) →
      ∀ {lo hi : ℝ}, 0 < lo → hi < 1 → 2*(hi-lo) < 1 →
      (∀ x ∈ Set.Ico (0 : ℝ) 1, χ (x : Circle) ≠ 0 → x ∈ Set.Icc lo hi) →
      0 < ‖fourierCoeff F h‖ * (∫ x, χ x ∂haarAddCircle) ∧
      ∀ᶠ M : ℕ in atTop,
        ‖fourierCoeff F h‖ * (∫ x, χ x ∂haarAddCircle) / 2 ≤
          D * (∑' k : ℤ, ‖fourierCoeff (fun x : Circle => (χ x : ℂ)) k‖) *
            normalizedGowers 3 1 (M : ℤ)
              (fun n => F (heisenbergPhase α β n : Circle) - circleMean F) := by
  have hG : NormalizedGowersLaws 3 := .of_triangle_and_adjacent (by decide)
    (fun L U hLU f g => normalizedGowers_triangle L U 3 (by decide) hLU f g)
    normalizedGowersAdjacentMonotonicity
  obtain ⟨D, hD, hMean⟩ := hG.meanBound
  refine ⟨D, hD, ?_⟩
  intro hGT α β hα hβ F κF hF h hh hFourier χ κχ hχLip hχnonneg hχne lo hi hlo hhi hshort hχ
  let m := ∫ x, χ x ∂haarAddCircle
  obtain ⟨x, hx⟩ := hχne
  have hm : 0 < m := integral_pos_of_integrable_nonneg_nonzero χ.continuous
    (χ.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) hχnonneg hx
  let p := ‖fourierCoeff F h‖ * m
  have hp : 0 < p := mul_pos (norm_pos_iff.mpr hFourier) hm
  refine ⟨hp, ?_⟩
  let χC : C(Circle, ℂ) := ⟨fun x => (χ x : ℂ), Complex.continuous_ofReal.comp χ.continuous⟩
  have hχClip : LipschitzWith κχ χC := by
    simpa [χC] using (RCLike.lipschitzWith_ofReal (K := ℂ)).comp hχLip
  have hχC : ∀ x ∈ Set.Ico (0 : ℝ) 1, χC (x : Circle) ≠ 0 → x ∈ Set.Icc lo hi := by
    intro x hxm hxne
    exact hχ x hxm (fun hz => hxne (by simp [χC, hz]))
  let f (n : ℤ) := F (heisenbergPhase α β n : Circle) - circleMean F
  let W (n : ℤ) := f n * χC ((β * (n : ℝ) : ℝ) : Circle) *
    phaseExponential (((-h : ℤ) : ℝ) * heisenbergPhase α β n)
  have hlim : Tendsto (fun M : ℕ => (∑ n ∈ positiveInterval M, W n) / (M : ℂ)) atTop
      (𝓝 (fourierCoeff F h * (m : ℂ))) :=
    tendsto_ambient_centered_localized_mode (scalarHeisenbergObstruction_of_greenTao hGT)
      α β hα hβ F hF h hh χ hχLip hlo hhi hχ
  have hnorm := hlim.norm
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hm.le] at hnorm
  have hlarge : ∀ᶠ M : ℕ in atTop, p/2 < ‖(∑ n ∈ positiveInterval M, W n) / (M : ℂ)‖ :=
    hnorm.eventually (Ioi_mem_nhds (show p/2 < p by linarith only [hp]))
  filter_upwards [hlarge, eventually_gt_atTop (0 : ℕ)] with M hlarge hM
  have hI : (1 : ℤ) ≤ M := by exact_mod_cast hM
  have hW : normalizedGowers 3 1 (M : ℤ) W ≤
      (∑' k : ℤ, ‖fourierCoeff χC k‖) * normalizedGowers 3 1 (M : ℤ) f := by
    simpa only [zero_add, one_mul, W] using localized_vertical_multiplier_of_bernstein
      bernsteinCircleLipschitzFourier 1 (M : ℤ) hI 3 (by decide) hG χC κχ hχClip lo hi hshort
      hχC α β 0 1 (-h) f
  calc
    p/2 ≤ ‖(∑ n ∈ positiveInterval M, W n) / (M : ℂ)‖ := hlarge.le
    _ ≤ D * normalizedGowers 3 1 (M : ℤ) W := hMean M hM W
    _ ≤ D * ((∑' k : ℤ, ‖fourierCoeff χC k‖) * normalizedGowers 3 1 (M : ℤ) f) :=
      mul_le_mul_of_nonneg_left hW hD.le
    _ = _ := by rw [mul_assoc]; rfl

end NilBohr
