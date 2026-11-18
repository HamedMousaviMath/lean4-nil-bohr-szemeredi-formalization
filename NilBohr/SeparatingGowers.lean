import NilBohr.SeparatingScales
import NilBohr.SeparatingFourier
import NilBohr.HeisenbergCutoff

/-! The uniform lower bound for the full Gowers norms in Appendix A. -/

open AddCircle Filter MeasureTheory
open scoped Topology NNReal BigOperators

namespace NilBohr

private noncomputable def separatingCutoff : C(Circle, ℝ) :=
  ⟨heisenbergSeamCutoff (1 / 3), (heisenbergSeamCutoff_lipschitz (by norm_num :
    (0 : ℝ) < 1 / 3)).continuous⟩

private theorem separatingCutoff_lipschitz :
    LipschitzWith (Real.toNNReal (1 / (1 / 3))) separatingCutoff :=
  heisenbergSeamCutoff_lipschitz (by norm_num)

private theorem separatingCutoff_mean_pos :
    0 < ∫ y, separatingCutoff y ∂haarAddCircle := by
  apply integral_pos_of_integrable_nonneg_nonzero (x := ((1 / 2 : ℝ) : Circle))
    separatingCutoff.continuous
    (separatingCutoff.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (fun y => (heisenbergSeamCutoff_bounds (1 / 3) y).1)
  have hh : ‖((1 / 2 : ℝ) : Circle)‖ = 1 / 2 := by
    simpa using AddCircle.norm_half_period_eq (1 : ℝ)
  change heisenbergSeamCutoff (1 / 3) ((1 / 2 : ℝ) : Circle) ≠ 0
  rw [heisenbergSeamCutoff, hh]
  norm_num

private theorem separatingCutoff_support (x : ℝ) (hx : x ∈ Set.Ico (0 : ℝ) 1)
    (hnz : separatingCutoff (x : Circle) ≠ 0) :
    x ∈ Set.Icc (1 / 3 : ℝ) (2 / 3) := by
  have hn : (1 / 3 : ℝ) < torusNorm x :=
    lt_of_not_ge fun hle => hnz (heisenbergSeamCutoff_eq_zero (by norm_num) hle)
  have hleft := torusNorm_le_abs x
  rw [abs_of_nonneg hx.1] at hleft
  have hshift : torusNorm x = torusNorm (x - 1) := by
    simpa only [Int.cast_one, sub_add_cancel] using torusNorm_add_int (x - 1) 1
  have hright := torusNorm_le_abs (x - 1)
  rw [abs_of_neg (sub_neg.mpr hx.2)] at hright
  constructor <;> linarith

private theorem separatingFourier_eq_phase (k : ℤ) (x : ℝ) :
    fourier (T := 1) k (x : Circle) = phaseExponential ((k : ℝ) * x) := by
  simp only [fourier_coe_apply, Complex.ofReal_one, div_one, phaseExponential,
    Complex.ofReal_mul, Complex.ofReal_intCast, mul_assoc]

private theorem lipschitzWith_mul_fourier (G : C(Circle, ℂ)) {κ : ℝ≥0}
    (hG : LipschitzWith κ G) (k : ℤ) :
    ∃ L : ℝ≥0, LipschitzWith L (G * fourier (T := 1) k : C(Circle, ℂ)) := by
  obtain ⟨κk, hk⟩ := exists_lipschitzWith_fourier k
  refine ⟨κ + ‖G‖₊ * κk, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  let c := fourier (T := 1) k
  change dist (G x * c x) (G y * c y) ≤ _ * dist x y
  have hgxy := hG.dist_le_mul x y
  have hcxy := hk.dist_le_mul x y
  change dist (c x) (c y) ≤ _ at hcxy
  have hcx : ‖c x‖ = 1 := by
    rw [show c x = fourier (T := 1) k x from rfl, fourier_apply]
    exact _root_.Circle.norm_coe _
  simp only [dist_eq_norm] at hgxy hcxy ⊢
  calc
    _ = ‖(G x - G y) * c x + G y * (c x - c y)‖ := by congr 1; ring
    _ ≤ ‖G x - G y‖ * ‖c x‖ + ‖G y‖ * ‖c x - c y‖ := by
      simpa only [norm_mul] using norm_add_le ((G x-G y)*c x) (G y*(c x-c y))
    _ ≤ ((κ : ℝ) * ‖x - y‖) * 1 + ‖G‖ * ((κk : ℝ) * ‖x - y‖) :=
      add_le_add (mul_le_mul hgxy hcx.le (norm_nonneg _) (by positivity))
        (mul_le_mul (G.norm_coe_le_norm y) hcxy (norm_nonneg _) (norm_nonneg _))
    _ = _ := by push_cast; ring

private theorem dilatedHeisenbergOrbit_one (α β : ℝ) (n : ℤ) :
    dilatedHeisenbergOrbit α β 1 n = heisenbergOrbit α β n := by
  rcases he : heisenbergOrbit α β n with ⟨x, y, z⟩
  simp [dilatedHeisenbergOrbit, he]

/-- For any admissible cutoff scale and the corresponding long progression,
the centered Heisenberg selector has a full Gowers norm bounded below.
The threshold and positive constant are independent of the progression. -/
theorem separating_gowers_lower_bound
    (hGT : ScalarHeisenbergObstruction) (hBernstein : BernsteinCircleLipschitzFourier)
    (α β : ℝ) (hα : BadlyApproximable α) {r : ℕ → ℕ} (hr : AdmissibleBetaDenominators β r)
    (F : C(Circle, ℂ)) {κF : ℝ≥0} (hF : LipschitzWith κF F)
    (hFnonconstant : ∃ x y : Circle, F x ≠ F y)
    (S : ℕ) (hS : 3 ≤ S) (hG : NormalizedGowersLaws S) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℝ in atTop, ∀ j q M : ℕ,
      (r j : ℝ) ≤ X^(1/100 : ℝ) → X^(1/100 : ℝ) < (r (j+1) : ℝ) →
      0 < q → (q : ℝ) ≤ X^(1/10000 : ℝ) → ¬ r j ∣ q →
      X^(1/2 : ℝ) ≤ (M : ℝ) →
      c ≤ normalizedGowers S 1 (M : ℤ) (separatingWeight α β F q) := by
  obtain ⟨h, hh, hmode⟩ := exists_nonzero_fourierCoeff_of_nonconstant F hFnonconstant
  let ε : ℝ := 1 / 3
  have hε : 0 < ε := by norm_num [ε]
  let L := Real.toNNReal (1/ε)
  let ψ := separatingCutoff
  let χ : C(Circle, ℂ) := ⟨fun x => (ψ x : ℂ), Complex.continuous_ofReal.comp ψ.continuous⟩
  have hψ : LipschitzWith L ψ := separatingCutoff_lipschitz
  have hχ : LipschitzWith L χ := by
    simpa [χ] using (RCLike.lipschitzWith_ofReal (K := ℂ)).comp hψ
  let m := ∫ y, ψ y ∂haarAddCircle
  have hm : 0 < m := separatingCutoff_mean_pos
  let G : C(Circle, ℂ) := F - ContinuousMap.const Circle (circleMean F)
  let H : C(Circle, ℂ) := G * fourier (T := 1) (-h)
  have hG_lip : LipschitzWith κF G := by
    simpa [G] using hF.sub (LipschitzWith.const (α := Circle) (circleMean F))
  obtain ⟨Lh, hH⟩ := lipschitzWith_mul_fourier G hG_lip (-h)
  have hMeanH : circleMean H = fourierCoeff F h := circleMean_centered_mul_fourier F hh
  let z := fourierCoeff F h
  let Ψ : HeisenbergPoint → ℂ := fun g => ψ (g.2.1 : Circle)
  let Φ := heisenbergCenteredTest H ε
  obtain ⟨U, hU, hΦbound⟩ := heisenbergCenteredTest_lipschitz H hH
  let V := U * (1 + ε⁻¹)
  have hΦlip : HeisenbergLipschitzNormLE Φ V := hΦbound ε hε
  have hΨlip : HeisenbergLipschitzNormLE Ψ (‖ψ‖ + (L : ℝ)) :=
    horizontalCircle_lipschitzNorm ψ hψ
  have hΦmean : heisenbergChartMean Φ = 0 := by
    simp only [heisenbergChartMean, Φ, heisenbergCenteredTest_verticalMean_zero H hH ε,
      intervalIntegral.integral_zero]
  have hΨmean : heisenbergChartMean Ψ = (m : ℂ) := horizontalCircle_chartMean ψ
  have hz : 0 < ‖z‖ := norm_pos_iff.mpr hmode
  let pos := ‖z‖ * m
  have hpos : 0 < pos := mul_pos hz hm
  let E := V + ‖z‖ * (‖ψ‖ + (L : ℝ))
  have hsmall : ∀ᶠ X : ℝ in atTop, Real.log X ^ (-(1 : ℝ)) * E < pos/2 := by
    have ht := ((tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 from one_pos)).comp
      Real.tendsto_log_atTop).mul_const E
    have ht' : Tendsto (fun X : ℝ => Real.log X ^ (-(1 : ℝ)) * E) atTop (𝓝 0) := by
      simpa only [Function.comp_apply, zero_mul] using ht
    exact ht'.eventually (gt_mem_nhds (half_pos hpos))
  obtain ⟨D, hD, hDbound⟩ := hG.meanBound
  let A := ∑' k : ℤ, ‖fourierCoeff χ k‖
  have hA : 0 ≤ A := tsum_nonneg fun _ => norm_nonneg _
  let C := D * (1 + A)
  have hC : 0 < C := mul_pos hD (by linarith)
  refine ⟨(pos/2)/C, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℝ), hsmall,
    scalar_heisenberg_equidistribution_for_denominators hGT α β hα hr 1 0 one_pos] with X hX hsmall hscalar
  intro j q M hlo hhi hq hqX hqcop hMX
  have hXone : 1 ≤ X := by linarith
  have hqX' := hqX.trans (Real.rpow_le_rpow_of_exponent_le hXone
    (by norm_num : (1/10000 : ℝ) ≤ 1/5000))
  have hMX' := (Real.rpow_le_rpow_of_exponent_le hXone
    (by norm_num : (1/3 : ℝ) ≤ 1/2)).trans hMX
  have hM : 0 < M := by
    have hxpos := Real.rpow_pos_of_pos (show 0 < X by linarith) (1/2 : ℝ)
    exact_mod_cast hxpos.trans_le hMX
  have hΦerr := hscalar j hlo hhi 0 q 1 M hq hqX' hqcop (by decide) (by simp) hMX' Φ V hΦlip
  have hΨerr := hscalar j hlo hhi 0 q 1 M hq hqX' hqcop (by decide) (by simp) hMX' Ψ _ hΨlip
  rw [hΦmean, sub_zero] at hΦerr
  rw [hΨmean] at hΨerr
  let f := separatingWeight α β F q
  let W : ℤ → ℂ := fun y =>
    f y * χ ((β*(((q : ℤ)*y : ℤ) : ℝ) : ℝ) : Circle) *
      phaseExponential (((-h : ℤ) : ℝ) * heisenbergPhase α β ((q : ℤ)*y))
  have hW (y : ℤ) : W y =
      Φ (heisenbergOrbit α β ((q : ℤ)*y)) + z * Ψ (heisenbergOrbit α β ((q : ℤ)*y)) := by
    unfold Φ
    rw [heisenbergCenteredTest_orbit, hMeanH]
    have heval : H (heisenbergPhase α β ((q : ℤ)*y) : Circle) =
        f y * phaseExponential (((-h : ℤ) : ℝ) * heisenbergPhase α β ((q : ℤ)*y)) := by
      change G _ * fourier (T := 1) (-h) _ = _
      rw [separatingFourier_eq_phase]
      rfl
    rw [heval]
    simp only [W, χ, Ψ, heisenbergOrbit, Int.cast_mul]
    change _ * (ψ _ : ℂ) * _ = (ψ _ : ℂ) * (_ * _ - _) + z * (ψ _ : ℂ)
    rw [mul_comm (((q : ℤ) : ℝ) * (y : ℝ)) β]
    ring
  let avg := (∑ y ∈ positiveInterval M, W y) / (M : ℂ)
  have havg : avg = heisenbergOrbitAverage α β 0 q 1 M Φ +
      z * heisenbergOrbitAverage α β 0 q 1 M Ψ := by
    simp only [avg, heisenbergOrbitAverage, zero_add, dilatedHeisenbergOrbit_one,
      hW, Finset.sum_add_distrib, ← Finset.mul_sum, add_div, mul_div_assoc]
  have herror : ‖avg - z*(m : ℂ)‖ ≤ Real.log X ^ (-(1 : ℝ)) * E := by
    rw [havg, show _ + z * heisenbergOrbitAverage α β 0 q 1 M Ψ - z * (m : ℂ) =
      heisenbergOrbitAverage α β 0 q 1 M Φ +
        z * (heisenbergOrbitAverage α β 0 q 1 M Ψ - (m : ℂ)) by ring]
    calc
      _ ≤ ‖heisenbergOrbitAverage α β 0 q 1 M Φ‖ +
          ‖z * (heisenbergOrbitAverage α β 0 q 1 M Ψ - (m : ℂ))‖ := norm_add_le _ _
      _ ≤ _ := by
        rw [norm_mul]
        refine (add_le_add hΦerr (mul_le_mul_of_nonneg_left hΨerr (norm_nonneg _))).trans_eq ?_
        dsimp [E]
        ring
  have hnormz : ‖z*(m : ℂ)‖ = pos := by
    dsimp [pos]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hm.le]
  have hLower : pos/2 ≤ ‖avg‖ := by
    have h := norm_sub_le avg (avg - z*(m : ℂ))
    rw [sub_sub_cancel, hnormz] at h
    linarith [herror.trans hsmall.le]
  have hI : (1 : ℤ) ≤ M := by exact_mod_cast hM
  have hχsup (x : ℝ) (hx : x ∈ Set.Ico (0 : ℝ) 1) (hnz : χ (x : Circle) ≠ 0) :
      x ∈ Set.Icc (1 / 3 : ℝ) (2 / 3) :=
    separatingCutoff_support x hx (fun he => hnz (by change (ψ (x : Circle) : ℂ) = 0; simp [ψ, he]))
  have hUpper := localized_vertical_multiplier_of_bernstein hBernstein 1 (M : ℤ) hI S hS hG χ L hχ
    (1/3 : ℝ) (2/3 : ℝ) (by norm_num) hχsup α β 0 q (-h) f
  have hWnorm : normalizedGowers S 1 (M : ℤ) W ≤ A * normalizedGowers S 1 (M : ℤ) f := by
    simpa only [zero_add, W, A] using hUpper
  have hfnorm : 0 ≤ normalizedGowers S 1 (M : ℤ) f :=
    normalizedGowers_nonnegative 1 (M : ℤ) S (by omega) f
  apply (div_le_iff₀ hC).mpr
  calc
    pos/2 ≤ ‖avg‖ := hLower
    _ ≤ D * normalizedGowers S 1 (M : ℤ) W := hDbound M hM W
    _ ≤ D * (A * normalizedGowers S 1 (M : ℤ) f) :=
      mul_le_mul_of_nonneg_left hWnorm hD.le
    _ ≤ D * ((1+A) * normalizedGowers S 1 (M : ℤ) f) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) hfnorm) hD.le
    _ = _ := by dsimp [C, f]; ring

end NilBohr
