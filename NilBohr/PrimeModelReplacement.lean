import NilBohr.LocalizedPrimeModel
import NilBohr.HeisenbergCutoff
import NilBohr.SelectorCutoffs
import NilBohr.PrimeProgressions

/-! Prime-model replacement for the full centered chart test.
Absolute Fourier convergence is used only after obtaining a bound that is
uniform over all vertical frequencies. -/

open Filter AddCircle Polynomial
open scoped BigOperators Topology NNReal

namespace NilBohr

private noncomputable def complexSeamCutoff (ε : ℝ) (hε : 0 < ε) : C(Circle, ℂ) :=
  ⟨fun x => (heisenbergSeamCutoff ε x : ℂ),
    Complex.continuous_ofReal.comp (heisenbergSeamCutoff_lipschitz hε).continuous⟩

private theorem norm_complexSeamCutoff_le (ε : ℝ) (hε : 0 < ε) (x : Circle) :
    ‖complexSeamCutoff ε hε x‖ ≤ 1 := by
  have hx := heisenbergSeamCutoff_bounds ε x
  simpa [complexSeamCutoff, Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2

private theorem lipschitz_complexSeamCutoff (ε : ℝ) (hε : 0 < ε) :
    LipschitzWith (Real.toNNReal (1/ε)) (complexSeamCutoff ε hε) := by
  simpa [complexSeamCutoff] using
    (RCLike.lipschitzWith_ofReal (K := ℂ)).comp (heisenbergSeamCutoff_lipschitz hε)

private theorem lipschitz_mul_complexSeamCutoff (ε : ℝ) (hε : 0 < ε)
    (g : C(Circle, ℂ)) (κ : ℝ≥0) (hg : LipschitzWith κ g) :
    LipschitzWith (κ + Real.toNNReal (1/ε) * ‖g‖₊) (g * complexSeamCutoff ε hε) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  let s := complexSeamCutoff ε hε
  change dist (g x * s x) (g y * s y) ≤ _ * dist x y
  have hgxy := hg.dist_le_mul x y
  have hsxy := (lipschitz_complexSeamCutoff ε hε).dist_le_mul x y
  simp only [dist_eq_norm] at hgxy hsxy ⊢
  calc
    ‖g x * s x - g y * s y‖ = ‖(g x-g y)*s x + g y*(s x-s y)‖ := by
      congr 1
      ring
    _ ≤ ‖g x-g y‖ * ‖s x‖ + ‖g y‖ * ‖s x-s y‖ := by
      simpa only [norm_mul] using norm_add_le ((g x-g y)*s x) (g y*(s x-s y))
    _ ≤ ((κ : ℝ)*‖x-y‖)*1 + ‖g‖ * ((Real.toNNReal (1/ε) : ℝ)*‖x-y‖) := by
      exact add_le_add
        (mul_le_mul hgxy (norm_complexSeamCutoff_le ε hε x) (norm_nonneg _) (by positivity))
        (mul_le_mul (ContinuousMap.norm_coe_le_norm g y) hsxy (norm_nonneg _) (norm_nonneg _))
    _ = _ := by push_cast; ring

/-- The prime chart cutoff is exactly a sum of three short-supported
multipliers. Clipping the chart denominator produces a boundary piece, but
this piece vanishes after multiplication by the seam cutoff. -/
theorem quantitativePrimeSelectorCutoffs :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε < 1/16 →
    ∃ (pieces : Fin 3 → C(Circle, ℂ)) (lo hi : Fin 3 → ℝ),
      (∀ j, ∃ κ : ℝ≥0, LipschitzWith κ (pieces j) ∧
        ‖pieces j‖ + (κ : ℝ) ≤ K/ε^2 ∧ 2*(hi j-lo j) < 1 ∧
        (∀ t : ℝ, t ∈ Set.Ico (0 : ℝ) 1 → pieces j (t : Circle) ≠ 0 →
          t ∈ Set.Icc (lo j) (hi j))) ∧
      ∀ x : Circle, (∑ j, pieces j x) = (heisenbergSeamCutoff ε x : ℂ) := by
  obtain ⟨K, hK, hSelect⟩ := quantitativeSelectorCutoffs_with_support
  refine ⟨2*K, by positivity, ?_⟩
  intro ε hε hε'
  obtain ⟨g, lo, hi, ψ, hg, _, _, _, hPart, hSeam⟩ := hSelect ε hε hε'
  let s := complexSeamCutoff ε hε
  let χ (j : Fin 3) := g j * s
  refine ⟨χ, lo, hi, ?_, ?_⟩
  · intro j
    obtain ⟨κ, hLip, hBound, hShort, hSupport⟩ := hg j
    refine ⟨κ + Real.toNNReal (1/ε)*‖g j‖₊,
      lipschitz_mul_complexSeamCutoff ε hε (g j) κ hLip, ?_, hShort, ?_⟩
    · have hNorm : ‖χ j‖ ≤ ‖g j‖ :=
        (ContinuousMap.norm_le _ (norm_nonneg _)).mpr fun x => by
          change ‖g j x * s x‖ ≤ ‖g j‖
          rw [norm_mul]
          exact (mul_le_of_le_one_right (norm_nonneg _) (norm_complexSeamCutoff_le ε hε x)).trans
            (ContinuousMap.norm_coe_le_norm (g j) x)
      have hg' : ‖g j‖ ≤ K/ε := (le_add_of_nonneg_right κ.coe_nonneg).trans hBound
      have hOne : 1 ≤ 1/ε := (le_div_iff₀ hε).mpr (by linarith)
      push_cast
      rw [Real.coe_toNNReal _ (by positivity)]
      calc
        _ ≤ ‖g j‖ + ((κ : ℝ) + (1/ε)*‖g j‖) := add_le_add_right hNorm _
        _ = (‖g j‖ + (κ : ℝ)) + (1/ε)*‖g j‖ := by ring
        _ ≤ K/ε + (1/ε)*(K/ε) := by gcongr
        _ ≤ (1/ε)*(K/ε) + (1/ε)*(K/ε) :=
          add_le_add_right (le_mul_of_one_le_left (by positivity) hOne) _
        _ = (2*K)/ε^2 := by ring
    · intro t ht hχ
      apply hSupport t ht
      intro hZero
      apply hχ
      change g j (t : Circle) * s (t : Circle) = 0
      simp [hZero]
  · intro x
    have hZero : (ψ x : ℂ)*s x = 0 := by
      by_cases hx : ε ≤ ‖x‖
      · simp [hSeam x hx]
      · simp [s, complexSeamCutoff, heisenbergSeamCutoff_eq_zero hε (le_of_not_ge hx)]
    change (∑ j, g j x * s x) = _
    rw [← Finset.sum_mul]
    have hmul := congrArg (fun z : ℂ => z*s x) (hPart x)
    simpa only [add_mul, hZero, add_zero, one_mul] using hmul

private theorem fourier_vertical_eq_phase (h : ℤ) (z : ℝ) :
    fourier h (z : Circle) = phase ((h : ℝ)*z) := by
  rw [fourier_coe_apply]
  unfold phase
  congr 1
  push_cast
  ring

private theorem prime_replacement_phase_add (x y : ℝ) :
    phase (x+y) = phase x * phase y := by
  unfold phase
  rw [Complex.ofReal_add, mul_add, Complex.exp_add]

set_option maxHeartbeats 1000000 in
/-- The localized prime-model estimate extends from each vertical character
to any vertical function with an absolutely summable Fourier series. -/
theorem localized_prime_model_replacement_full_chart (S : ℕ) (hS : 3 ≤ S)
    (hG : NormalizedGowersLaws S) :
    ∃ E : ℝ, 0 < E ∧ ∀ (X D : ℕ) [NeZero D], 0 < X →
    ∀ (a b u₀ : ℤ), Finset.Icc a b ⊆ positiveInterval X →
      (localProgression a b u₀ D).Nonempty →
    ∀ (u : ℤ → ℂ) (χ F : C(Circle, ℂ)),
      Summable (fun n : ℤ => ‖fourierCoeff χ n‖) →
      Summable (fun n : ℤ => ‖fourierCoeff F n‖) →
    ∀ (lo hi : ℝ), 2*(hi-lo) < 1 →
      (∀ t : ℝ, t ∈ Set.Ico (0 : ℝ) 1 → χ (t : Circle) ≠ 0 → t ∈ Set.Icc lo hi) →
    ∀ (α β : ℝ) (Q : Polynomial ℝ), Q.natDegree < S →
    let J := localProgression a b u₀ D
    ‖phaseAverage J (fun m => u m * χ ((β*((m-1 : ℤ) : ℝ) : ℝ) : Circle) *
        F (heisenbergPhase α β (m-1) : Circle)) Q‖ ≤
        ((X : ℝ)/(J.card : ℝ)) * (2+Real.log X) *
          (E * (∑' n : ℤ, ‖fourierCoeff χ n‖) *
            normalizedGowers S 1 (X : ℤ) u) * (∑' n : ℤ, ‖fourierCoeff F n‖) := by
  obtain ⟨E, hE, hMono⟩ := localized_prime_model_replacement_progression S hS hG
  refine ⟨E, hE, ?_⟩
  intro X D _ hX a b u₀ hI hJ u χ F hχF hFF lo hi hShort hSupport α β Q hQ J
  let y (m : ℤ) : Circle := ((β*((m-1 : ℤ) : ℝ) : ℝ) : Circle)
  let z (m : ℤ) := heisenbergPhase α β (m-1)
  let B := ((X : ℝ)/(J.card : ℝ)) * (2+Real.log X) *
    (E * (∑' n : ℤ, ‖fourierCoeff χ n‖) * normalizedGowers S 1 (X : ℤ) u)
  let T (h : ℤ) := phaseAverage J (fun m => u m * χ (y m) * phase ((h : ℝ)*z m)) Q
  have hPer (h : ℤ) : ‖T h‖ ≤ B := by
    have hModeBound := hMono X D hX a b u₀ hI hJ u χ hχF lo hi hShort hSupport α β h Q hQ
    have hPhase (m : ℤ) :
        phase ((h : ℝ)*z m) * phase (-Q.eval (m : ℝ)) =
        phaseExponential ((h : ℝ)*z m-Q.eval (m : ℝ)) := by
      rw [← prime_replacement_phase_add, sub_eq_add_neg]
      rfl
    simp only [z] at hPhase
    dsimp [B]
    apply le_trans _ (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (intervalCyclicFourierCoefficient_l1_le X a b hI)
        (by positivity)) _)
    · simpa only [T, phaseAverage, mul_assoc, hPhase, y, z, J] using hModeBound
    · exact mul_nonneg (mul_nonneg hE.le (tsum_nonneg fun n => norm_nonneg _))
        (normalizedGowers_nonnegative _ _ _ (by omega) _)
  let v (h : ℤ) (m : ℤ) :=
    fourierCoeff F h * (u m * χ (y m) * phase ((h : ℝ)*z m) * phase (-Q.eval (m : ℝ)))
  have hFExp (m : ℤ) : HasSum (fun h => v h m)
      (u m * χ (y m) * F (z m : Circle) * phase (-Q.eval (m : ℝ))) := by
    have h := has_pointwise_sum_fourier_series_of_summable hFF.of_norm (z m : Circle)
    simpa only [v, fourier_vertical_eq_phase, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
      using (h.mul_left (u m * χ (y m))).mul_right (phase (-Q.eval (m : ℝ)))
  have hSum : HasSum (fun h => fourierCoeff F h * T h)
      (phaseAverage J (fun m => u m * χ (y m) * F (z m : Circle)) Q) := by
    have hs := (hasSum_sum (s := J) (fun m _ => hFExp m)).div_const (J.card : ℂ)
    simpa only [phaseAverage, T, v, ← Finset.mul_sum, mul_div_assoc] using hs
  change ‖phaseAverage J (fun m => u m * χ (y m) * F (z m : Circle)) Q‖ ≤ _
  refine le_of_tendsto_of_tendsto
    (continuous_norm.continuousAt.tendsto.comp hSum) (hFF.hasSum.mul_left B) ?_
  filter_upwards [] with U
  calc
    ‖∑ h ∈ U, fourierCoeff F h * T h‖ ≤ ∑ h ∈ U, ‖fourierCoeff F h * T h‖ := norm_sum_le _ _
    _ ≤ ∑ h ∈ U, B * ‖fourierCoeff F h‖ := by
      refine Finset.sum_le_sum fun h _ => ?_
      rw [norm_mul, mul_comm B]
      exact mul_le_mul_of_nonneg_left (hPer h) (norm_nonneg _)

set_option maxHeartbeats 1000000 in
/-- The finite model replacement estimate for the seam-cut, centered
selector, with no loss depending on a vertical frequency. -/
theorem prime_model_replacement_centered_chart (S : ℕ) (hS : 3 ≤ S)
    (hG : NormalizedGowersLaws S) (hBernstein : BernsteinCircleLipschitzFourier)
    (F : C(Circle, ℂ)) (L₀ : ℝ≥0) (hF : LipschitzWith L₀ F) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (X D : ℕ) [NeZero D], 0 < X →
    ∀ (a b u₀ : ℤ), Finset.Icc a b ⊆ positiveInterval X →
      (localProgression a b u₀ D).Nonempty →
    ∀ (u : ℤ → ℂ) (ε α β : ℝ), 0 < ε → ε < 1/16 →
    ∀ Q : Polynomial ℝ, Q.natDegree < S →
    let J := localProgression a b u₀ D
    ‖phaseAverage J
      (fun m => u m * heisenbergCenteredTest F ε (heisenbergOrbit α β (m-1))) Q‖ ≤
      C * ((X : ℝ)/(J.card : ℝ)) * (2+Real.log X) / ε^2 *
        normalizedGowers S 1 (X : ℤ) u := by
  obtain ⟨E, hE, hEst⟩ := localized_prime_model_replacement_full_chart S hS hG
  obtain ⟨B, hB, hFourier⟩ := hBernstein
  obtain ⟨K, hK, hCut⟩ := quantitativePrimeSelectorCutoffs
  let F₀ : C(Circle, ℂ) := F - ContinuousMap.const Circle (circleMean F)
  have hF₀ : LipschitzWith L₀ F₀ := by
    simpa [F₀] using hF.sub (LipschitzWith.const (α := Circle) (circleMean F))
  obtain ⟨hAbsF, _⟩ := hFourier F₀ L₀ hF₀
  let V := 1+(∑' h : ℤ, ‖fourierCoeff F₀ h‖)
  have hV : 0 < V := by
    dsimp [V]
    exact add_pos_of_pos_of_nonneg one_pos (tsum_nonneg fun n => norm_nonneg _)
  let C := E*B*K*V
  refine ⟨3*C, by dsimp [C]; positivity, ?_⟩
  intro X D _ hX a b u₀ hI hJ u ε α β hε hε' Q hQ J
  obtain ⟨χ, lo, hi, hχ, hPart⟩ := hCut ε hε hε'
  let y (m : ℤ) : Circle := ((β*((m-1 : ℤ) : ℝ) : ℝ) : Circle)
  let z (m : ℤ) : Circle := (heisenbergPhase α β (m-1) : Circle)
  let v (j : Fin 3) (m : ℤ) := u m * χ j (y m) * F₀ (z m)
  have hSplit (m : ℤ) : u m * heisenbergCenteredTest F ε (heisenbergOrbit α β (m-1)) =
      ∑ j, v j m := by
    rw [heisenbergCenteredTest_orbit]
    change u m * ((heisenbergSeamCutoff ε (y m) : ℂ)*F₀ (z m)) = _
    rw [← hPart (y m), Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => (mul_assoc _ _ _).symm)
  have hSplitAvg : phaseAverage J
      (fun m => u m * heisenbergCenteredTest F ε (heisenbergOrbit α β (m-1))) Q =
      ∑ j, phaseAverage J (v j) Q := by
    simp only [phaseAverage, hSplit, Finset.sum_mul, Finset.sum_div]
    rw [Finset.sum_comm]
  have hlog : 0 ≤ 2+Real.log (X : ℝ) := by
    exact add_nonneg (by norm_num) (Real.log_nonneg (by exact_mod_cast hX))
  have hG₀ : 0 ≤ normalizedGowers S 1 (X : ℤ) u :=
    normalizedGowers_nonnegative _ _ _ (by omega) _
  have hBound (j : Fin 3) :
      ‖phaseAverage J (v j) Q‖ ≤
        C * ((X : ℝ)/(J.card : ℝ)) * (2+Real.log X) / ε^2 *
          normalizedGowers S 1 (X : ℤ) u := by
    obtain ⟨κ, hLip, hLipBound, hShort, hSupport⟩ := hχ j
    obtain ⟨hAbsχ, hBχ⟩ := hFourier (χ j) κ hLip
    have hχFourier : (∑' n : ℤ, ‖fourierCoeff (χ j) n‖) ≤ B*(K/ε^2) :=
      hBχ.trans (mul_le_mul_of_nonneg_left hLipBound hB.le)
    have hV' : (∑' n : ℤ, ‖fourierCoeff F₀ n‖) ≤ V := by
      dsimp [V]
      linarith
    refine (hEst X D hX a b u₀ hI hJ u (χ j) F₀ hAbsχ hAbsF
      (lo j) (hi j) hShort hSupport α β Q hQ).trans ?_
    calc
      _ ≤ ((X : ℝ)/(J.card : ℝ)) * (2+Real.log X) *
          (E * (B*(K/ε^2)) * normalizedGowers S 1 (X : ℤ) u) * V := by
        gcongr
      _ = _ := by dsimp [C]; ring
  rw [hSplitAvg]
  calc
    _ ≤ ∑ j, ‖phaseAverage J (v j) Q‖ := norm_sum_le _ _
    _ ≤ ∑ _ : Fin 3, C * ((X : ℝ)/(J.card : ℝ)) * (2+Real.log X) / ε^2 *
        normalizedGowers S 1 (X : ℤ) u := Finset.sum_le_sum fun j _ => hBound j
    _ = _ := by simp [nsmul_eq_mul]; ring

set_option maxHeartbeats 1500000 in
/-- Uniformly over the progressions and polynomial tests of Proposition 6.2,
the ambient replacement against the full seam-cut, centered selector saves
every power of the logarithm. The Gowers input is used at a stronger
logarithmic power to absorb the chart and progression costs. -/
theorem primeModelReplacement_log_saving_of_kmtt
    {c₀ : ℝ} (hc₀ : 0 < c₀) (hc₀' : c₀ < 1/11)
    (hBanks : BanksRealZeroBound) (hAmbient : KMTTAmbientPrimeModel c₀)
    (hBernstein : BernsteinCircleLipschitzFourier)
    {d : ℕ} (hd : 0 < d) (hG : NormalizedGowersLaws (max 3 (d+1)))
    (F : C(Circle, ℂ)) (L₀ : ℝ≥0) (hF : LipschitzWith L₀ F)
    {B K L A E : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ K) (hL : 0 ≤ L) (hA : 0 < A) (hE : 0 < E) :
    ∃ C : ℝ, 0 < C ∧
    ∀ᶠ N : ℕ in atTop, ∀ {q b : ℕ} {l r u : ℤ}, 0 < q →
      (q : ℝ) ≤ (Real.log N)^L → (b : ℝ) ≤ B →
      let M := parameterLength N q d
      let X := q*M+1
      Finset.Icc l r ⊆ positiveInterval M →
      (M : ℝ)*(Real.log N)^(-K) ≤ ((Finset.Icc l r).card : ℝ) →
      ∀ (α β : ℝ) (Q : Polynomial ℝ), Q.natDegree ≤ d →
      let P' := (localProgression l r u (q^b)).image (fun y => (q : ℤ)*y+1)
      let ε := (Real.log (X : ℝ))^(-E)
      ‖phaseAverage P' (fun m => (mangoldtWeight m - cramerWeight (cramerCutoff c₀ X) m) *
        heisenbergCenteredTest F ε (heisenbergOrbit α β (m-1))) Q‖ ≤
        C * (Real.log (X : ℝ))^(-A) := by
  let T := K+(B+1)*L
  let P := A+T+2*E+1
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hP : 0 < P := by dsimp [P]; linarith
  let S := max 3 (d+1)
  have hS : 3 ≤ S := le_max_left _ _
  obtain ⟨c, hc, hSizes⟩ := primeProgression_sieve_scales hd B K L hB hK hL
  obtain ⟨C, hC, hProg⟩ := prime_model_replacement_centered_chart S hS hG hBernstein F L₀ hF
  obtain ⟨D, hD, hSaving⟩ :=
    ambient_cramer_log_saving_of_kmtt hc₀ hc₀' hBanks hAmbient (S := S) (by omega) hP
  have hNt : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hSmall := ((tendsto_rpow_atTop hE).comp hNt).eventually_gt_atTop (16 : ℝ)
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.1 (hSaving.and ((hNt.eventually_ge_atTop 1).and hSmall))
  let W := max 1 X₀
  have hW : 0 < (W : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 X₀))
  refine ⟨3*C*c⁻¹*D, by positivity, ?_⟩
  filter_upwards [hSizes, hNt.eventually_ge_atTop (2*(d : ℝ)*Real.log (W : ℝ))] with N hSizes hN
  intro q b l r u hq hqL hb M X hI hLen α β Q hQ P' ε
  let t := Real.log (X : ℝ)
  have hX : 0 < X := Nat.succ_pos _
  have hx : 0 < (X : ℝ) := by exact_mod_cast hX
  obtain ⟨hPC, _, hScale, _, hLower, _⟩ := hSizes hq hqL hb hI hLen
  have hlogW : Real.log (W : ℝ) ≤ t :=
    ((le_div_iff₀ (show 0 < 2*(d : ℝ) by positivity)).mpr (by simpa only [mul_comm] using hN)).trans hScale
  have hWX : W ≤ X := by exact_mod_cast ((Real.log_le_log_iff hW hx).mp hlogW)
  obtain ⟨hSaving, ht, hBig⟩ := hX₀ X ((le_max_right 1 X₀).trans hWX)
  have ht' : 0 < t := by exact zero_lt_one.trans_le ht
  have hε : 0 < ε := Real.rpow_pos_of_pos ht' _
  have hε' : ε < 1/16 := by
    change t^(-E) < 1/16
    rw [Real.rpow_neg ht'.le, one_div]
    exact (inv_lt_inv₀ (Real.rpow_pos_of_pos ht' _) (by norm_num : (0:ℝ)<16)).mpr hBig
  change P'.card = (localProgression l r u (q^b)).card at hPC
  have hCard : 0 < (P'.card : ℝ) := lt_of_lt_of_le (by positivity) hLower
  have hCardNat : 0 < P'.card := by exact_mod_cast hCard
  have hPN : (localProgression l r u (q^b)).Nonempty := by
    apply Finset.card_pos.mp
    rwa [← hPC]
  obtain ⟨_, _, hForm, _, _, _⟩ := primeProgression_as_affine hq hI hPN
  change P' = _ at hForm
  have hI' : Finset.Icc ((q : ℤ)*l+1) ((q : ℤ)*r+1) ⊆ positiveInterval X := by
    obtain ⟨v, hv⟩ := hPN
    obtain ⟨hl, hr⟩ := Finset.mem_Icc.mp (Finset.mem_filter.mp hv).1
    have hlr : l ≤ r := hl.trans hr
    have hl' := (Finset.mem_Icc.mp (hI (Finset.mem_Icc.mpr ⟨le_rfl, hlr⟩))).1
    have hr' := (Finset.mem_Icc.mp (hI (Finset.mem_Icc.mpr ⟨hlr, le_rfl⟩))).2
    have hqZ : 0 ≤ (q : ℤ) := by positivity
    intro m hm
    obtain ⟨hm₁, hm₂⟩ := Finset.mem_Icc.mp hm
    apply Finset.mem_Icc.mpr
    constructor
    · exact (by nlinarith only [mul_nonneg hqZ (show 0 ≤ l by omega)] :
        (1 : ℤ) ≤ (q : ℤ)*l+1).trans hm₁
    · refine hm₂.trans ?_
      change _ ≤ ((q*M+1 : ℕ) : ℤ)
      push_cast
      exact add_le_add_right (mul_le_mul_of_nonneg_left hr' hqZ) _
  let v (m : ℤ) := mangoldtWeight m - cramerWeight (cramerCutoff c₀ X) m
  have hRatio : (X : ℝ)/(P'.card : ℝ) ≤ c⁻¹*t^T := by
    apply (div_le_iff₀ hCard).mpr
    have hCancel : t^T*t^(-T) = 1 := by
      rw [← Real.rpow_add ht', add_neg_cancel, Real.rpow_zero]
    calc
      (X : ℝ) = (c⁻¹*t^T)*(c*(X : ℝ)*t^(-T)) := by
        rw [show (c⁻¹*t^T)*(c*(X : ℝ)*t^(-T)) =
          (c⁻¹*c)*(t^T*t^(-T))*(X : ℝ) by ring, inv_mul_cancel₀ hc.ne', hCancel, one_mul, one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hLower (by positivity)
  have hεInv : (ε^2)⁻¹ = t^(2*E) := by
    change ((t^(-E))^2)⁻¹ = _
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul ht'.le]
    have hExp : (-E)*((2 : ℕ) : ℝ) = -(2*E) := by push_cast; ring
    rw [hExp, Real.rpow_neg ht'.le, inv_inv]
  letI : NeZero (q^(b+1)) := ⟨(pow_pos hq (b+1)).ne'⟩
  have hJJ : (localProgression ((q : ℤ)*l+1) ((q : ℤ)*r+1) ((q : ℤ)*u+1)
      (q^(b+1))).Nonempty := by
    rw [← hForm]
    exact Finset.card_pos.mp hCardNat
  have hFinite := hProg X (q^(b+1)) hX ((q : ℤ)*l+1) ((q : ℤ)*r+1) ((q : ℤ)*u+1)
    hI' hJJ v ε α β hε hε' Q (hQ.trans_lt ((Nat.lt_succ_self d).trans_le (le_max_right 3 (d+1))))
  dsimp only at hFinite
  rw [← hForm] at hFinite
  have htMul : t^T*t*t^(2*E)*t^(-P) = t^(-A) := by
    calc
      _ = t^T*t^(1:ℝ)*t^(2*E)*t^(-P) := by rw [Real.rpow_one]
      _ = _ := by
        rw [← Real.rpow_add ht', ← Real.rpow_add ht', ← Real.rpow_add ht']
        congr 1
        dsimp [P]
        ring
  have hg₀ : 0 ≤ normalizedGowers S 1 (X : ℤ) v :=
    normalizedGowers_nonnegative _ _ _ (by omega) _
  have hLog : 2+t ≤ 3*t := by linarith only [show 1 ≤ t from ht]
  change ‖phaseAverage P'
    (fun m => v m * heisenbergCenteredTest F ε (heisenbergOrbit α β (m-1))) Q‖ ≤ _
  calc
    _ ≤ C * ((X : ℝ)/(P'.card : ℝ)) * (2+t) / ε^2 *
        normalizedGowers S 1 (X : ℤ) v := hFinite
    _ ≤ C*(c⁻¹*t^T)*(3*t)*t^(2*E)*(D*t^(-P)) := by
      rw [div_eq_mul_inv (C * ((X : ℝ)/(P'.card : ℝ)) * (2+t)) _, hεInv]
      gcongr
    _ = (3*C*c⁻¹*D)*t^(-A) := by rw [← htMul]; ring

end NilBohr
