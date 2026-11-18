import NilBohr.TwistedEstimates
import NilBohr.Ergodic
import NilBohr.HorizontalCircleEstimate

/-! Chart cutoffs and horizontal seam bounds for the vertical test. -/

open MeasureTheory
open scoped NNReal

namespace NilBohr

noncomputable def heisenbergSeamCutoff (ε : ℝ) (y : Circle) : ℝ :=
  min 1 (max 0 ((‖y‖-ε)/ε))

theorem heisenbergSeamCutoff_bounds (ε : ℝ) (y : Circle) :
    0 ≤ heisenbergSeamCutoff ε y ∧ heisenbergSeamCutoff ε y ≤ 1 :=
  ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩

theorem heisenbergSeamCutoff_eq_one {ε : ℝ} {y : Circle} (hε : 0 < ε)
    (hy : 2*ε ≤ ‖y‖) : heisenbergSeamCutoff ε y = 1 := by
  apply min_eq_left
  apply (le_div_iff₀ hε).mpr (by linarith) |>.trans (le_max_right _ _)

theorem heisenbergSeamCutoff_eq_zero {ε : ℝ} {y : Circle} (hε : 0 < ε)
    (hy : ‖y‖ ≤ ε) : heisenbergSeamCutoff ε y = 0 := by
  unfold heisenbergSeamCutoff
  rw [max_eq_left (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hy) hε.le), min_eq_right zero_le_one]

theorem heisenbergSeamCutoff_lipschitz {ε : ℝ} (hε : 0 < ε) :
    LipschitzWith (Real.toNNReal (1/ε)) (heisenbergSeamCutoff ε) := by
  have hbase : LipschitzWith (Real.toNNReal (1/ε)) (fun y : Circle => (‖y‖-ε)/ε) := by
    apply lipschitzWith_iff_dist_le_mul.2
    intro x y
    rw [Real.dist_eq, ← sub_div, abs_div, abs_of_pos hε, Real.coe_toNNReal _ (by positivity),
      one_div_mul_eq_div, sub_sub_sub_cancel_right]
    exact div_le_div_of_nonneg_right (by simpa only [dist_eq_norm] using abs_norm_sub_norm_le x y) hε.le
  exact (hbase.const_max 0).const_min 1

/-- The vertical chart observable after subtracting its circle average,
with a cutoff that vanishes on a neighbourhood of the seam. -/
noncomputable def heisenbergCenteredTest (F : Circle → ℂ) (ε : ℝ) (g : HeisenbergPoint) : ℂ :=
  (heisenbergSeamCutoff ε (g.2.1 : Circle) : ℂ) * (F (reducedVertical g : Circle)-circleMean F)

theorem heisenbergCenteredTest_orbit (F : Circle → ℂ) (ε α β : ℝ) (n : ℤ) :
    heisenbergCenteredTest F ε (heisenbergOrbit α β n) =
      (heisenbergSeamCutoff ε ((β*(n : ℝ) : ℝ) : Circle) : ℂ) *
        (F (heisenbergPhase α β n : Circle)-circleMean F) := by
  rw [heisenbergCenteredTest, reducedVertical_orbit]
  simp only [heisenbergOrbit, mul_comm (n : ℝ) β]

private theorem heisenbergCenteredTest_right_lattice (F : Circle → ℂ) (ε : ℝ)
    (g : HeisenbergPoint) (u v w : ℤ) :
    heisenbergCenteredTest F ε (heisenbergMul g ((u : ℝ), (v : ℝ), (w : ℝ))) =
      heisenbergCenteredTest F ε g := by
  obtain ⟨hy, hz⟩ := heisenberg_chart_right_lattice g u v w
  unfold heisenbergCenteredTest
  rw [← AddCircle.coe_fract ((heisenbergMul g ((u : ℝ), (v : ℝ), (w : ℝ))).2.1), hy,
    AddCircle.coe_fract, ← AddCircle.coe_fract (reducedVertical (heisenbergMul g ((u : ℝ), (v : ℝ), (w : ℝ)))),
    hz, AddCircle.coe_fract]

theorem heisenbergCenteredTest_verticalMean_zero (F : Circle → ℂ) {L : ℝ≥0}
    (hF : LipschitzWith L F) (ε x y : ℝ) :
    (∫ z in (0 : ℝ)..1, heisenbergCenteredTest F ε (x,y,z)) = 0 := by
  unfold heisenbergCenteredTest reducedVertical
  simp only [intervalIntegral.integral_const_mul]
  let G : Circle → ℂ := fun z => F z - circleMean F
  change (heisenbergSeamCutoff ε (y : Circle) : ℂ) *
    (∫ z in (0 : ℝ)..1, G ((z-x*⌊y⌋ : ℝ) : Circle)) = 0
  rw [intervalIntegral.integral_comp_sub_right (f := fun z : ℝ => G (z : Circle))]
  have h := AddCircle.intervalIntegral_preimage (1:ℝ) (0-x*⌊y⌋) G
  rw [AddCircle.volume_eq_smul_haarAddCircle] at h
  simp only [ENNReal.ofReal_one, one_smul] at h
  rw [show (1:ℝ)-x*⌊y⌋ = 0-x*⌊y⌋+1 by ring, h]
  have hi : Integrable F (AddCircle.haarAddCircle : Measure Circle) :=
    hF.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp [G, integral_sub hi (integrable_const _), circleMean]

private theorem heisenberg_relativeCoordinates (g h : HeisenbergPoint) :
    heisenbergMalcevNorm (heisenbergMul g (heisenbergInv h)) =
      max |g.1-h.1| (max |g.2.1-h.2.1| |g.2.2-h.2.2-(g.1-h.1)*g.2.1|) := by
  simp only [heisenbergMalcevNorm, heisenbergMul, heisenbergInv, sub_eq_add_neg]
  have hz : g.2.2 + (-h.2.2 + h.1*h.2.1) + g.1*(-h.2.1) +
      -((g.1 + -h.1)*(g.2.1 + -h.2.1)) =
      g.2.2 + -h.2.2 + -((g.1 + -h.1)*g.2.1) := by ring
  rw [hz]

private theorem heisenberg_relativeCoordinates_yshift (g h : HeisenbergPoint) (s : ℤ) :
    heisenbergMalcevNorm (heisenbergMul (heisenbergMul g (0,(s:ℝ),0))
      (heisenbergInv (heisenbergMul h (0,(s:ℝ),0)))) =
        heisenbergMalcevNorm (heisenbergMul g (heisenbergInv h)) := by
  rw [heisenberg_relativeCoordinates, heisenberg_relativeCoordinates]
  simp only [heisenbergMul, add_zero]
  have hy : g.2.1 + (s:ℝ) - (h.2.1 + (s:ℝ)) = g.2.1-h.2.1 := by ring
  have hz : g.2.2 + g.1*(s:ℝ) - (h.2.2 + h.1*(s:ℝ)) -
      (g.1-h.1)*(g.2.1+(s:ℝ)) = g.2.2-h.2.2-(g.1-h.1)*g.2.1 := by ring
  rw [hy, hz]

private theorem heisenbergCenteredTest_relative (F : Circle → ℂ) {L : ℝ≥0}
    (hF : LipschitzWith L F) {S ε : ℝ} (hS : 0 ≤ S) (hε : 0 < ε)
    (hsup : ∀ z, ‖F z-circleMean F‖ ≤ S) (g h : HeisenbergPoint) :
    ‖heisenbergCenteredTest F ε g - heisenbergCenteredTest F ε h‖ ≤
      (3*S*(1/ε)+2*(L:ℝ)+1)*heisenbergMalcevNorm (heisenbergMul g (heisenbergInv h)) := by
  let δ := heisenbergMalcevNorm (heisenbergMul g (heisenbergInv h))
  let M := 3*S*(1/ε)+2*(L:ℝ)+1
  have hδ : 0 ≤ δ := by rw [show δ = _ from heisenberg_relativeCoordinates g h]; positivity
  have hb (p : HeisenbergPoint) : ‖heisenbergCenteredTest F ε p‖ ≤ S := by
    rw [heisenbergCenteredTest, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (heisenbergSeamCutoff_bounds ε _).1]
    exact (mul_le_mul (heisenbergSeamCutoff_bounds ε _).2 (hsup _)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  by_cases hlarge : ε ≤ δ
  · calc
      _ ≤ 2*S := (norm_sub_le _ _).trans (by linarith [hb g, hb h])
      _ = (2*S*(1/ε))*ε := by field_simp
      _ ≤ (2*S*(1/ε))*δ := mul_le_mul_of_nonneg_left hlarge (by positivity)
      _ ≤ M*δ := by
        apply mul_le_mul_of_nonneg_right _ hδ
        dsimp [M]
        nlinarith [mul_nonneg hS (one_div_pos.mpr hε).le, L.coe_nonneg]
  let n : ℤ := -⌊g.2.1⌋
  let g' := heisenbergMul g (0,(n:ℝ),0)
  let h' := heisenbergMul h (0,(n:ℝ),0)
  have hshift : heisenbergMalcevNorm (heisenbergMul g' (heisenbergInv h')) = δ :=
    heisenberg_relativeCoordinates_yshift g h n
  have hg : heisenbergCenteredTest F ε g' = heisenbergCenteredTest F ε g := by
    simpa only [g', Int.cast_zero] using heisenbergCenteredTest_right_lattice F ε g 0 n 0
  have hh : heisenbergCenteredTest F ε h' = heisenbergCenteredTest F ε h := by
    simpa only [h', Int.cast_zero] using heisenbergCenteredTest_right_lattice F ε h 0 n 0
  have hfract : g'.2.1 = Int.fract g.2.1 := by simp [g', n, heisenbergMul, Int.fract, sub_eq_add_neg]
  have hy₀ : 0 ≤ g'.2.1 := hfract ▸ Int.fract_nonneg _
  have hy₁ : g'.2.1 < 1 := hfract ▸ Int.fract_lt_one _
  have hnorms := heisenberg_relativeCoordinates g' h'
  rw [hshift] at hnorms
  have hxδ : |g'.1-h'.1| ≤ δ := hnorms.symm ▸ le_max_left _ _
  have hyδ : |g'.2.1-h'.2.1| ≤ δ := hnorms.symm ▸ (le_max_left _ _).trans (le_max_right _ _)
  have hzδ : |g'.2.2-h'.2.2-(g'.1-h'.1)*g'.2.1| ≤ δ :=
    hnorms.symm ▸ (le_max_right _ _).trans (le_max_right _ _)
  rw [← hg, ← hh]
  let cg := heisenbergSeamCutoff ε (g'.2.1 : Circle)
  let ch := heisenbergSeamCutoff ε (h'.2.1 : Circle)
  let Gg := F (reducedVertical g' : Circle)-circleMean F
  let Gh := F (reducedVertical h' : Circle)-circleMean F
  have hcg := heisenbergSeamCutoff_bounds ε (g'.2.1 : Circle)
  have hcut : |cg-ch| ≤ (1/ε)*δ := by
    have hz := (heisenbergSeamCutoff_lipschitz hε).dist_le_mul (g'.2.1 : Circle) (h'.2.1 : Circle)
    rw [Real.dist_eq, Real.coe_toNNReal _ (by positivity), dist_eq_norm, ← AddCircle.coe_sub] at hz
    exact hz.trans (mul_le_mul_of_nonneg_left ((torusNorm_le_abs _).trans hyδ) (by positivity))
  have hvert : ‖(cg : ℂ)*(Gg-Gh)‖ ≤ 2*(L:ℝ)*δ := by
    by_cases hcg₀ : cg = 0
    · rw [hcg₀, Complex.ofReal_zero, zero_mul, norm_zero]
      positivity
    have hthin : ε < ‖(g'.2.1 : Circle)‖ := lt_of_not_ge
      (fun h => hcg₀ (heisenbergSeamCutoff_eq_zero hε h))
    have hylo : ε < g'.2.1 := hthin.trans_le ((torusNorm_le_abs _).trans_eq (abs_of_nonneg hy₀))
    have hone : torusNorm g'.2.1 = torusNorm (g'.2.1-1) := by
      simpa only [Int.cast_one, sub_add_cancel] using torusNorm_add_int (g'.2.1-1) 1
    have hyhi : g'.2.1 < 1-ε := by
      change ε < torusNorm g'.2.1 at hthin
      rw [hone] at hthin
      have hbound := torusNorm_le_abs (g'.2.1-1)
      rw [abs_of_neg (by linarith)] at hbound
      linarith
    have hhlo : 0 ≤ h'.2.1 := by linarith [(abs_le.mp hyδ).2]
    have hhhi : h'.2.1 < 1 := by linarith [(abs_le.mp hyδ).1]
    have hgfloor : ⌊g'.2.1⌋ = 0 := Int.floor_eq_iff.mpr (by simpa using ⟨hy₀,hy₁⟩)
    have hhfloor : ⌊h'.2.1⌋ = 0 := Int.floor_eq_iff.mpr (by simpa using ⟨hhlo,hhhi⟩)
    have hzdiff : |g'.2.2-h'.2.2| ≤ 2*δ := by
      have heq : g'.2.2-h'.2.2 =
          (g'.2.2-h'.2.2-(g'.1-h'.1)*g'.2.1)+(g'.1-h'.1)*g'.2.1 := by ring
      rw [heq]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_nonneg hy₀]
      have hb' := mul_le_mul hxδ hy₁.le hy₀ hδ
      linarith
    have hl := hF.dist_le_mul (g'.2.2 : Circle) (h'.2.2 : Circle)
    rw [dist_eq_norm, dist_eq_norm, ← AddCircle.coe_sub] at hl
    have hG : ‖Gg-Gh‖ ≤ (L:ℝ)*(2*δ) := by
      dsimp [Gg, Gh, reducedVertical]
      rw [hgfloor, hhfloor]
      simp only [Int.cast_zero, mul_zero, AddCircle.coe_zero, sub_zero, sub_sub_sub_cancel_right]
      exact hl.trans (mul_le_mul_of_nonneg_left ((torusNorm_le_abs _).trans hzdiff) L.coe_nonneg)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hcg.1]
    calc
      _ ≤ 1*((L:ℝ)*(2*δ)) := mul_le_mul hcg.2 hG (norm_nonneg _) zero_le_one
      _ = _ := by ring
  have hhor : ‖((cg-ch : ℝ) : ℂ)*Gh‖ ≤ S*(1/ε)*δ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_mul hcut (hsup _) (norm_nonneg _) (by positivity)).trans_eq (by ring)
  change ‖(cg : ℂ)*Gg-(ch : ℂ)*Gh‖ ≤ M*δ
  rw [show (cg : ℂ)*Gg-(ch : ℂ)*Gh = (cg : ℂ)*(Gg-Gh)+((cg-ch : ℝ) : ℂ)*Gh by push_cast; ring]
  refine (norm_add_le _ _).trans ((add_le_add hvert hhor).trans ?_)
  rw [← add_mul]
  apply mul_le_mul_of_nonneg_right _ hδ
  dsimp [M]
  nlinarith [mul_nonneg hS (one_div_pos.mpr hε).le]

/-- A Lipschitz test on the vertical circle gives a test on the right
lattice quotient with a reciprocal-width Lipschitz loss. -/
theorem heisenbergCenteredTest_lipschitz (F : Circle → ℂ) {L : ℝ≥0}
    (hF : LipschitzWith L F) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε →
      HeisenbergLipschitzNormLE (heisenbergCenteredTest F ε) (C*(1+ε⁻¹)) := by
  obtain ⟨S, hS⟩ := isCompact_univ.exists_bound_of_continuousOn
    (f := fun z : Circle => F z-circleMean F) (hF.continuous.sub continuous_const).continuousOn
  have hSup (z : Circle) : ‖F z-circleMean F‖ ≤ S := hS z (Set.mem_univ _)
  have hS₀ : 0 ≤ S := (norm_nonneg _).trans (hSup 0)
  let C := 4*S+2*(L:ℝ)+1
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro ε hε
  let M := 3*S*(1/ε)+2*(L:ℝ)+1
  have hM : 0 < M := by dsimp [M]; positivity
  have hs (g : HeisenbergPoint) : ‖heisenbergCenteredTest F ε g‖ ≤ S := by
    rw [heisenbergCenteredTest, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (heisenbergSeamCutoff_bounds ε _).1]
    exact (mul_le_mul (heisenbergSeamCutoff_bounds ε _).2 (hSup _)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  obtain ⟨hInv, S', M', hS', hM', hsum, hsup, hLip⟩ :=
    heisenbergLipschitzNormLE_of_relative _ hS₀ hM
      (heisenbergCenteredTest_right_lattice F ε) hs (heisenbergCenteredTest_relative F hF hS₀ hε hSup)
  refine ⟨hInv, S', M', hS', hM', hsum.trans ?_, hsup, hLip⟩
  dsimp [M,C]
  rw [← one_div]
  nlinarith [mul_nonneg hS₀ (one_div_pos.mpr hε).le,
    mul_nonneg L.coe_nonneg (one_div_pos.mpr hε).le, (one_div_pos.mpr hε).le]

section SeamAverage

open Filter AddCircle Metric Set
open scoped BigOperators Topology

private noncomputable def seamRemainder (ε : ℝ) (x : Circle) : ℝ :=
  1 - heisenbergSeamCutoff ε x

private theorem seamRemainder_bounds (ε : ℝ) (x : Circle) :
    0 ≤ seamRemainder ε x ∧ seamRemainder ε x ≤ 1 := by
  unfold seamRemainder
  exact ⟨sub_nonneg.mpr (heisenbergSeamCutoff_bounds ε x).2,
    sub_le_self _ (heisenbergSeamCutoff_bounds ε x).1⟩

private theorem seamRemainder_eq_zero {ε : ℝ} (hε : 0 < ε) {x : Circle} (hx : 2*ε ≤ ‖x‖) :
    seamRemainder ε x = 0 := by
  unfold seamRemainder
  rw [heisenbergSeamCutoff_eq_one hε hx, sub_self]

private theorem seamRemainder_lipschitz {ε : ℝ} (hε : 0 < ε) :
    LipschitzWith (Real.toNNReal (1/ε)) (seamRemainder ε) := by
  simpa only [seamRemainder, zero_add] using
    (LipschitzWith.const (1:ℝ)).sub (heisenbergSeamCutoff_lipschitz hε)

private theorem seamRemainder_integral_le {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1/4) :
    (∫ x, seamRemainder ε x ∂haarAddCircle) ≤ 4*ε := by
  let I := closedBall (0 : Circle) (2*ε)
  have hψ : Integrable (seamRemainder ε) (haarAddCircle : Measure Circle) :=
    (seamRemainder_lipschitz hε).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hi : Integrable (I.indicator (fun _ => (1 : ℝ))) (haarAddCircle : Measure Circle) :=
    (integrable_const 1).indicator measurableSet_closedBall
  refine (integral_mono hψ hi ?_).trans_eq ?_
  · intro x
    by_cases hx : x ∈ I
    · rw [indicator_of_mem hx]
      exact (seamRemainder_bounds ε x).2
    · rw [indicator_of_not_mem hx, seamRemainder_eq_zero hε]
      exact le_of_lt (lt_of_not_ge (by simpa [I, mem_closedBall] using hx))
  · change (∫ x : Circle, I.indicator (1 : Circle → ℝ) x ∂haarAddCircle) = 4*ε
    rw [integral_indicator_one measurableSet_closedBall]
    have hv : (volume : Measure Circle) = haarAddCircle := by
      rw [AddCircle.volume_eq_smul_haarAddCircle]
      norm_num
    rw [← hv]
    simp only [measureReal_def, I, AddCircle.volume_closedBall]
    rw [min_eq_right (show 2*(2*ε) ≤ (1:ℝ) by linarith), ENNReal.toReal_ofReal (by positivity)]
    ring

/-- A shrinking horizontal seam has average mass of order its width,
uniformly on the admissible progressions of the scalar estimate. -/
theorem heisenberg_seamAverage_of_horizontal {β : ℝ} {r : ℕ → ℕ}
    (hHorizontal : HorizontalCircleEstimate β r) {E : ℝ} (hE : 0 < E) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ X : ℝ in atTop,
      ∀ j : ℕ, (r j : ℝ) ≤ X^(1/100 : ℝ) → X^(1/100 : ℝ) < (r (j+1) : ℝ) →
      ∀ (a : ℤ) (v H : ℕ), 0 < v → (v : ℝ) ≤ X^(1/10000 : ℝ) → ¬ r j ∣ v →
      X^(1/2 : ℝ) ≤ (H : ℝ) →
      let ε := (Real.log X)^(-E)
      (∑ t ∈ positiveInterval H,
        (1 - heisenbergSeamCutoff ε ((β * ((a + (v : ℤ)*t : ℤ) : ℝ) : ℝ) : Circle))) /
          (H : ℝ) ≤ D*ε := by
  obtain ⟨D, hD, hScalar⟩ := hHorizontal (2*E) (by positivity)
  refine ⟨4+2*D, by positivity, ?_⟩
  have hsmall := ((tendsto_rpow_atTop hE).comp Real.tendsto_log_atTop).eventually_ge_atTop (4 : ℝ)
  filter_upwards [hScalar, hsmall, Real.tendsto_log_atTop.eventually_ge_atTop 1]
    with X hs hsmall hLog
  intro j hjlo hjhi a v H hv hvX hcop hH
  let ε := (Real.log X)^(-E)
  have hlog₀ : 0 < Real.log X := zero_lt_one.trans_le hLog
  have hε : 0 < ε := Real.rpow_pos_of_pos hlog₀ _
  have hε' : ε ≤ 1/4 := by
    dsimp [ε]
    rw [Real.rpow_neg hlog₀.le, one_div]
    exact (inv_le_inv₀ (Real.rpow_pos_of_pos hlog₀ _) (by norm_num : (0:ℝ)<4)).mpr hsmall
  have hε₁ : ε ≤ 1 := hε'.trans (by norm_num)
  let κ : ℝ≥0 := Real.toNNReal (1/ε)
  let ψ : C(Circle, ℝ) := ⟨seamRemainder ε, (seamRemainder_lipschitz hε).continuous⟩
  have hψLip : LipschitzWith κ ψ := seamRemainder_lipschitz hε
  have hψsup : ‖ψ‖ ≤ 1 := by
    apply (ContinuousMap.norm_le _ zero_le_one).mpr
    intro x
    have h := seamRemainder_bounds ε x
    simpa [ψ, Real.norm_eq_abs, abs_of_nonneg h.1] using h.2
  have hψnorm : ‖ψ‖ + (κ:ℝ) ≤ 2/ε := by
    have he : 1 ≤ 1/ε := (le_div_iff₀ hε).mpr (by simpa using hε₁)
    rw [show (κ : ℝ) = 1/ε from Real.coe_toNNReal _ (by positivity)]
    rw [show (2:ℝ)/ε = 1/ε + 1/ε by ring]
    linarith
  have hε2 : (Real.log X)^(-(2*E)) = ε^2 := by
    dsimp [ε]
    rw [← Real.rpow_mul_natCast hlog₀.le]
    congr 1
    push_cast
    ring
  let z (t : ℤ) := ((β*((a+(v:ℤ)*t : ℤ):ℝ) : ℝ) : Circle)
  let ν := (∑ t ∈ positiveInterval H, ψ (z t))/(H:ℝ)
  change ν ≤ (4+2*D)*ε
  have h := hs j hjlo hjhi a v H hv hvX hcop hH ψ κ hψLip
  have h' : |ν - ∫ t, ψ t ∂haarAddCircle| ≤ D*ε^2*(‖ψ‖+(κ:ℝ)) := by
    simpa only [ν, z, hε2] using h
  have hb := mul_le_mul_of_nonneg_left hψnorm (show 0 ≤ D*ε^2 by positivity)
  have he : D*ε^2*(2/ε) = (2*D)*ε := by field_simp; ring
  rw [he] at hb
  have hc := seamRemainder_integral_le hε hε'
  change (∫ t, ψ t ∂haarAddCircle) ≤ 4*ε at hc
  have hErr := (le_abs_self (ν - ∫ t, ψ t ∂haarAddCircle)).trans (h'.trans hb)
  linarith only [hErr, hc]

end SeamAverage

end NilBohr
