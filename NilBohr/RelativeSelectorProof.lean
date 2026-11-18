import NilBohr.BareSelectorComparison
import NilBohr.PrimeSelectorDiscrepancy
import NilBohr.SelectorCutoffs
import NilBohr.LocalGeneralized
import NilBohr.DensityIncrement
import NilBohr.BracketRecurrence
import NilBohr.HorizontalCircleEstimate

/-! Uniform assembly of the relative selector comparison. -/

open Filter AddCircle MeasureTheory Polynomial
open scoped BigOperators Topology NNReal

namespace NilBohr

private theorem relativeModulus_shrink {c₀ c₁ c₂ : ℝ} (hc₀ : 0 ≤ c₀) (hc : c₁ ≤ c₂)
    {w₀ N q w : ℕ} (hN : 1 ≤ Real.log (N : ℝ))
    (h : RelativeModulus c₀ c₁ w₀ N q w) : RelativeModulus c₀ c₂ w₀ N q w := by
  obtain ⟨hw, hq, hRange, hDiv, hSmooth, hBound⟩ := h
  have hL : 1 ≤ Real.log (cramerCutoff c₀ N) :=
    (Real.one_le_rpow hN hc₀).trans (cramerCutoff_log_bounds hc₀ hN).2.1
  exact ⟨hw, hq, hRange.trans (Real.rpow_le_rpow_of_exponent_le hL hc), hDiv, hSmooth, hBound⟩

private theorem fixedFamily_as_cases {ℓ : ℕ} (P : Fin (ℓ+1) → Polynomial ℤ)
    (hP : FixedPolynomialFamily P) : P = Fin.cases 0 (fun i => P i.succ) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using hP.2.1
  · simp

private theorem lambdaModulus_nonnegative (q : ℕ) (t : ℤ) : 0 ≤ lambdaModulus q t :=
  mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) ArithmeticFunction.vonMangoldt_nonneg

set_option maxHeartbeats 2000000 in
/-- Uniform Theorem 3.2 from the independently stated high-order prime input,
weighted Gowers bound, the scalar and centered progression estimates, and the
quantitative cutoff construction. All selection and error absorption are
checked at the prescribed floor value of M. -/
theorem relativeSelectorComparison_of_progression_estimates {c₀ C : ℝ}
    (hc₀ : 0 < c₀) (hc₀' : c₀ < 1/11) (hC : 1 ≤ C)
    {d ℓ : ℕ} (hd : 0 < d) (hℓ : 0 < ℓ)
    (hVN : LocalGeneralizedVonNeumann) (hCountGowers : KMTTWeightedGowers)
    (hMono : NormalizedGowersAdjacentMonotonicity)
    (hLaws : ∀ S : ℕ, 2 ≤ S → NormalizedGowersLaws S)
    (hPrime : ∀ S : ℕ, 3 ≤ S → HighOrderRelativePrimeUniformity c₀ d S)
    (hBernstein : BernsteinCircleLipschitzFourier)
    {α β : ℝ} (F : C(Circle, ℂ)) (κF : ℝ≥0) (hF : LipschitzWith κF F)
    {r : ℕ → ℕ} (hr : AdmissibleBetaDenominators β r)
    (hScalar : HorizontalCircleEstimate β r)
    (hPhase : CenteredHeisenbergPhaseEstimate d (heisenbergPhase α β) F r) :
    RelativeSelectorComparison c₀ C d ℓ (heisenbergPhase α β) F := by
  classical
  let V := heisenbergPhase α β
  obtain ⟨S₀, C₀, hS₀, hC₀, hCounting⟩ := hCountGowers d ℓ C hC
  let S := S₀+1
  have hS : 3 ≤ S := Nat.succ_le_succ hS₀
  obtain ⟨C₁, hC₁, hOrder⟩ := hMono S₀ (by omega)
  let A := C₀*C₁
  have hA : 0 < A := mul_pos hC₀ hC₁
  have hG := hLaws S (by omega)
  obtain ⟨E, hE, hMean⟩ := hG.meanBound
  obtain ⟨cPrime, η₀, B₀, w₀, N₀, hcPrime, hη₀, hB₀, hw₀, hhigh⟩ := hPrime S hS
  let cRel := min cPrime (1/10)
  have hcRel : 0 < cRel := lt_min hcPrime (by norm_num)
  have hcRel₁ : cRel ≤ 1/10 := min_le_right _ _
  let η := min η₀ 1
  have hη : 0 < η := lt_min hη₀ one_pos
  have hη₁ : η ≤ 1 := min_le_right _ _
  have hη' : η ≤ η₀ := min_le_left _ _
  let δ := η/2
  have hδ : 0 < δ := half_pos hη
  have hδ₁ : δ ≤ 1 := by dsimp [δ]; linarith
  obtain ⟨BFour, hBFour, hFour⟩ := hBernstein
  obtain ⟨hFsum, _⟩ := hFour F κF hF
  let FFour := ∑' h : ℤ, ‖fourierCoeff F h‖
  have hFFour : 0 ≤ FFour := tsum_nonneg fun _ => norm_nonneg _
  obtain ⟨KCut, hKCut, hCut⟩ := quantitativeSelectorCutoffs
  let KK := 3*BFour*KCut
  have hKK : 0 < KK := by dsimp [KK]; positivity
  obtain ⟨L, hL, hscalar⟩ := hScalar 2 (by norm_num)
  let L' := KCut + L*KCut*(32*(2*(d:ℝ)))^2
  have hL' : 0 < L' := by dsimp [L']; positivity
  let B' := 1024*B₀
  let PrimeError := FFour*A*KK*B' + ‖F‖*(2*L'+E*KK*B')
  have hPrimeError : 0 ≤ PrimeError := by dsimp [PrimeError, B']; positivity
  have hbare := unweightedSelectorComparison_of_local_phase hVN hc₀ hc₀' hcRel hcRel₁ hC
    hw₀ hd hℓ F F.continuous ⟨r, hr, hPhase⟩
  obtain ⟨Bbare, hBbare, Nbare, hbare⟩ := hbare 1 one_pos
  let K := PrimeError/32 + Bbare
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨hrMono, a, _, hrPrime, c, D, _, hc, hD, _, hrApp⟩ := hr
  have hstart := (tendsto_rpow_atTop (show (0:ℝ) < 1/100 by norm_num)).eventually_ge_atTop (r 0 : ℝ)
  have hdenom := horizontal_scale_bounds c D 1 (2*(d:ℝ)) hc hD one_pos (by positivity)
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp (hscalar.and (hdenom.and hstart))
  let Xmin := max 1 X₀
  have hXmin : 0 < Xmin := zero_lt_one.trans_le (le_max_left _ _)
  have hLog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hXgrow := hLog.eventually_ge_atTop (2*(d:ℝ)*Real.log Xmin)
  have hwindow := eventually_localSelectorTest_window hc₀ hc₀' hcRel₁ one_pos one_pos one_pos hd hw₀ 0
  have hscale := eventually_parameterLength_relativeScaleWindow hc₀ hc₀' hcRel₁ hd w₀
  have hEv : ∀ᶠ N : ℕ in atTop, ∀ q w : ℕ, RelativeModulus c₀ cRel w₀ N q w →
      let M := parameterLength N q d
      ∀ P : Fin (ℓ+1) → Polynomial ℤ, FixedPolynomialFamily P →
        (P (Fin.last ℓ)).natDegree = d → (∀ i, i ≠ 0 → HasCoefficients C q (P i)) →
      ∀ f : Fin (ℓ+1) → ℤ → ℂ,
        (∀ i, OneBoundedOn (positiveInterval N) (f i)) →
        (∀ i, SupportedOn (positiveInterval N) (f i)) →
        ‖countingForm N M (positiveInterval N) P (fun y => (lambdaModulus q y : ℂ)*selectorWeight V F q y) f -
          circleMean F * countingForm N M (positiveInterval N) P (fun _ => 1) f‖ ≤ K*(w:ℝ)^(-δ) := by
    filter_upwards [hwindow, hscale, hXgrow, hLog.eventually_ge_atTop 1,
      eventually_ge_atTop (1:ℕ), eventually_ge_atTop N₀, eventually_ge_atTop Nbare]
      with N hWindow hScale hXgrow hlogN hN hN₀ hNbare
    intro q w hMod M P hP hDeg hCoeffs f hf hf'
    let xScale := ((q*M+1 : ℕ) : ℝ)
    let ε := (w:ℝ)^(-δ)/32
    obtain ⟨_, hM, hwLog, hlogX, hTests⟩ := hWindow q w hMod
    have hq := hMod.2.1
    have hq₁ : (1:ℝ) ≤ q := by exact_mod_cast hq
    have hw₁ : (1:ℝ) ≤ w := by exact_mod_cast (show 1 ≤ w from (by omega : 1 ≤ w₀).trans hMod.1)
    have hw : (0:ℝ) < w := zero_lt_one.trans_le hw₁
    have hN' : 0 < N := by omega
    have hε : 0 < ε := by dsimp [ε]; positivity
    have hε' : ε < 1/16 := by
      dsimp [ε]
      have h := Real.rpow_le_one_of_one_le_of_nonpos hw₁ (neg_nonpos.mpr hδ.le)
      linarith
    have hX : 0 < xScale := by dsimp [xScale]; positivity
    have hX' : X₀ ≤ xScale := by
      have hmin : Xmin ≤ xScale := by
        apply (Real.log_le_log_iff hXmin hX).mp
        exact ((le_div_iff₀ (by positivity : 0 < 2*(d:ℝ))).mpr (by
          simpa only [mul_comm (Real.log Xmin)] using hXgrow)).trans hlogX
      exact (le_max_right _ _).trans hmin
    obtain ⟨hs, hden, hstart⟩ := hX₀ xScale hX'
    obtain ⟨j, hjlo, hjhi⟩ := exists_bracketing_denominators r hrMono _ hstart
    obtain ⟨hlo, hhi, _, _⟩ := hrApp j
    have hrp := (hrPrime j).1
    have hlogXw : (w:ℝ)/(2*(d:ℝ)) ≤ Real.log xScale :=
      (div_le_div_of_nonneg_right hwLog (by positivity)).trans hlogX
    have hwlt : w < r j := by
      have hg := (hden (r j) (r (j+1)) hrp.pos hlo hhi hjhi).1
      rw [Real.rpow_one] at hg
      have hh := (div_le_iff₀ (by positivity : 0 < 2*(d:ℝ))).mp hlogXw
      have hg' : Real.log xScale * (2*(d:ℝ)) < (r j:ℝ) := by
        simpa only [mul_comm (Real.log xScale)] using hg
      have hh' : (w:ℝ) < (r j:ℝ) := hh.trans_lt hg'
      exact_mod_cast hh'
    have hcop : ¬ r j ∣ q := fun h => (not_le_of_gt hwlt) (hMod.2.2.2.2.1 _ hrp h)
    have hProg : localProgression 1 (M:ℤ) 0 (q^0) = positiveInterval M := by
      simp [localProgression, positiveInterval, Int.modEq_one]
    have hPsize : (M:ℝ)*(q:ℝ)^(-(1:ℝ))*((w:ℝ)^(-(1:ℝ)-1))^(1:ℝ) ≤
        ((Finset.Icc 1 (M:ℤ)).card:ℝ) := by
      change (M:ℝ)*(q:ℝ)^(-(1:ℝ))*((w:ℝ)^(-(1:ℝ)-1))^(1:ℝ) ≤ ((positiveInterval M).card:ℝ)
      rw [card_positiveInterval, Real.rpow_one]
      exact (mul_le_of_le_one_right (by positivity) (Real.rpow_le_one_of_one_le_of_nonpos hw₁ (by norm_num))).trans
        (mul_le_of_le_one_right (by positivity) (Real.rpow_le_one_of_one_le_of_nonpos hq₁ (by norm_num)))
    obtain ⟨hStep, hKlen⟩ := hTests 1 (M:ℤ) 0 0 (by rfl) hPsize
      (by rw [hProg]; exact Finset.card_pos.mp (by simpa))
    rw [hProg, card_positiveInterval] at hKlen
    have hStep' : (q:ℝ) ≤ xScale^(1/10000:ℝ) := by simpa [xScale, M] using hStep
    obtain ⟨pieces, lo, hi, ψ, hpieces, hψ₀, ⟨κψ, hψLip, hψSize⟩, hψIntegral, hPartition⟩ := hCut ε hε hε'
    have hScalarRaw := hs j hjlo hjhi 0 q M hq hStep' hcop hKlen ψ κψ hψLip
    let ν := (∑ t ∈ positiveInterval M, ψ ((β*(((q:ℤ)*t : ℤ):ℝ) : ℝ) : Circle))/(M:ℝ)
    have hLogPos : 0 < Real.log xScale := (div_pos hw (by positivity)).trans_le hlogXw
    have hζ : (Real.log xScale)⁻¹ ≤ (32*(2*(d:ℝ)))*ε := by
      calc
        _ ≤ ((w:ℝ)/(2*(d:ℝ)))⁻¹ := (inv_le_inv₀ hLogPos (by positivity)).mpr hlogXw
        _ = (2*(d:ℝ))*(w:ℝ)^(-(1:ℝ)) := by rw [inv_div, Real.rpow_neg_one, div_eq_mul_inv]
        _ ≤ (2*(d:ℝ))*(w:ℝ)^(-δ) := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hw₁ (by linarith)) (by positivity)
        _ = _ := by dsimp [ε]; ring
    have hζ' : (Real.log xScale)^(-(2:ℝ)) ≤ ((32*(2*(d:ℝ)))*ε)^2 := by
      have he : (Real.log xScale)^(-(2:ℝ)) = ((Real.log xScale)⁻¹)^2 := by
        rw [← Real.rpow_neg_one, ← Real.rpow_mul_natCast hLogPos.le]
        congr 1
        norm_num
      rw [he]
      exact pow_le_pow_left₀ (by positivity) hζ 2
    have hAperture : ν ≤ L'*ε := by
      have hs' : |ν - ∫ x, ψ x ∂haarAddCircle| ≤ L*(Real.log xScale)^(-(2:ℝ))*(‖ψ‖+(κψ:ℝ)) := by
        simpa only [ν, zero_add] using hScalarRaw
      have hBound : L*(Real.log xScale)^(-(2:ℝ))*(‖ψ‖+(κψ:ℝ)) ≤
          L*KCut*(32*(2*(d:ℝ)))^2*ε := by
        calc
          _ ≤ (L*(((32*(2*(d:ℝ)))*ε)^2))*(KCut/ε) := by gcongr
          _ = _ := by field_simp; ring
      dsimp [L']
      linarith [le_abs_self (ν - ∫ x, ψ x ∂haarAddCircle)]
    let u := fun t => lambdaModulus q t - 1
    have hu (t : ℤ) : -1 ≤ u t := by dsimp [u]; linarith [lambdaModulus_nonnegative q t]
    have hg₀ := normalizedGowers_nonnegative 1 (M:ℤ) S (show 1 ≤ S by omega) (fun t => (u t:ℂ))
    have hMod' := relativeModulus_shrink hc₀.le (min_le_left cPrime (1/10)) hlogN hMod
    have hg : normalizedGowers S 1 (M:ℤ) (fun t => (u t:ℂ)) ≤ B' * ε^2 := by
      have hh := (hhigh N q w M hN₀ hMod' (hScale q w hMod)).1
      have hh' : normalizedGowers S 1 (M:ℤ) (fun t => (u t:ℂ)) ≤ B₀*(w:ℝ)^(-η₀) := by
        simpa only [u, Complex.ofReal_sub, Complex.ofReal_one] using hh
      refine hh'.trans ?_
      calc
        _ ≤ B₀*(w:ℝ)^(-η) := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hw₁ (by linarith)) hB₀.le
        _ = _ := by
          dsimp [B', ε]
          rw [div_pow, ← Real.rpow_mul_natCast hw.le, show (-δ)*((2:ℕ):ℝ) = -η by dsimp [δ]; ring]
          ring
    have hpAbs (j : Fin 3) := hFour (pieces j) (hpieces j).choose (hpieces j).choose_spec.1
    have hpBound (j : Fin 3) : (∑' h : ℤ, ‖fourierCoeff (pieces j) h‖) ≤ BFour*(KCut/ε) :=
      (hpAbs j).2.trans (mul_le_mul_of_nonneg_left (hpieces j).choose_spec.2.1 hBFour.le)
    have hSum : (∑ j : Fin 3, ∑' h : ℤ, ‖fourierCoeff (pieces j) h‖) ≤ KK/ε := by
      calc
        _ ≤ ∑ _ : Fin 3, BFour*(KCut/ε) := Finset.sum_le_sum fun j _ => hpBound j
        _ = _ := by simp [KK, div_eq_mul_inv]; ring
    have hψComplex : LipschitzWith κψ (continuousCircleOfReal ψ) := by
      simpa [continuousCircleOfReal] using Complex.isometry_ofReal.lipschitz.comp hψLip
    have hψNorm : ‖continuousCircleOfReal ψ‖ ≤ ‖ψ‖ := by
      apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
      intro t
      simpa [continuousCircleOfReal] using ψ.norm_coe_le_norm t
    obtain ⟨hψAbs, hψFour⟩ := hFour _ κψ hψComplex
    have hBoundaryFour : (∑' h : ℤ, ‖fourierCoeff (continuousCircleOfReal ψ) h‖) ≤ KK/ε := by
      calc
        _ ≤ BFour*(KCut/ε) := hψFour.trans (mul_le_mul_of_nonneg_left
          ((add_le_add_right hψNorm _).trans hψSize) hBFour.le)
        _ ≤ _ := by dsimp [KK]; rw [← mul_div_assoc]; gcongr; linarith
    have hcount (v : ℤ → ℂ) : ‖countingForm N M (positiveInterval N) P v f‖ ≤
        A * normalizedGowers S 1 (M:ℤ) v := by
      let P' (i : Fin ℓ) := P i.succ
      have hDeg' (i : Fin ℓ) : (P' i).natDegree ≤ d := by
        rw [← hDeg]
        exact hP.2.2.2.monotone (Fin.le_last _)
      have hCard (_ : Fin (ℓ+1)) : ((positiveInterval N).card:ℝ) ≤ C*(N:ℝ) := by
        rw [card_positiveInterval]
        simpa using mul_le_mul_of_nonneg_right hC (Nat.cast_nonneg N)
      have hBound := hCounting N M hN' hM P' hDeg' v f (fun _ => positiveInterval N) hCard hf hf'
      rw [← fixedFamily_as_cases P hP] at hBound
      exact hBound.trans (by
        simpa only [A, mul_assoc] using mul_le_mul_of_nonneg_left (hOrder M hM v) hC₀.le)
    have hPrimeFinite := norm_countingForm_selector_discrepancy_le hN' hM hS hG E hE (hMean M hM)
      P f hf hf' A hA.le hcount α β q u hu F hFsum Finset.univ pieces lo hi
      (fun j _ => (hpAbs j).1) (fun j _ => (hpieces j).choose_spec.2.2.1)
      (fun j _ => (hpieces j).choose_spec.2.2.2) ψ hψ₀ hψAbs hPartition
    have hOptimize := selector_error_absorb hε hE.le hKK.le (mul_nonneg hFFour hA.le) (norm_nonneg F)
      hg₀ hg hSum hBoundaryFour hAperture
    have hPrimeBound : ‖countingForm N M (positiveInterval N) P
        (fun y => ((lambdaModulus q y:ℂ)-1)*selectorWeight V F q y) f‖ ≤ PrimeError*ε := by
      change ‖countingForm N M (positiveInterval N) P
        (fun y => ((lambdaModulus q y:ℂ)-1)*selectorWeight V F q y) f‖ ≤ PrimeError*ε
      simpa only [u, Complex.ofReal_sub, Complex.ofReal_one, selectorWeight, V, L', B', PrimeError]
        using (hPrimeFinite.trans hOptimize)
    have hbare' := hbare N q w hNbare hMod P hP hDeg hCoeffs f hf hf'
    have hBareBound : ‖countingForm N M (positiveInterval N) P
        (fun y => selectorWeight V F q y - circleMean F) f‖ ≤ Bbare*(w:ℝ)^(-δ) :=
      hbare'.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hw₁ (by linarith)) hBbare.le)
    refine (norm_selector_count_sub_le N M (positiveInterval N) P (fun y => (lambdaModulus q y : ℂ))
      (selectorWeight V F q) (circleMean F) f).trans ((add_le_add hPrimeBound hBareBound).trans_eq ?_)
    dsimp [K, ε]
    ring
  obtain ⟨Nfinal, hFinal⟩ := eventually_atTop.mp hEv
  exact ⟨cRel, δ, K, w₀, Nfinal, hcRel, hδ, hK, hw₀, fun N q w hN => hFinal N hN q w⟩

/-- The cited quantitative inputs used by the uniform selector theorem.
The centered Heisenberg phase estimate is an original manuscript argument
and is passed separately. -/
structure SelectorLiteratureInputs (c₀ : ℝ) : Prop where
  banks : BanksRealZeroBound
  ambientPrimeModel : KMTTAmbientPrimeModel c₀
  normalizedDilation : KMTTNormalizedDilation
  relativeCramer : KMTTRelativeCramer c₀
  localInverse : KMTTLocalInverse
  weightedGowers : KMTTWeightedGowers
  adjacentMonotonicity : NormalizedGowersAdjacentMonotonicity
  gowersTriangle : ∀ (S : ℕ) (L U : ℤ), 2 ≤ S → L ≤ U → ∀ f g : ℤ → ℂ,
    normalizedGowers S L U (fun n => f n + g n) ≤
      normalizedGowers S L U f + normalizedGowers S L U g
  bernstein : BernsteinCircleLipschitzFourier
  scalarObstruction : ScalarHeisenbergObstruction

/-- Theorem 3.2 from the cited quantitative inputs and the independently
stated centered phase estimate at the chosen prime denominators. -/
theorem relativeSelectorComparison_of_centered_phase {c₀ C : ℝ}
    (hc₀ : 0 < c₀) (hc₀' : c₀ < 1/11) (hC : 1 ≤ C)
    {d ℓ : ℕ} (hd : 0 < d) (hℓ : 0 < ℓ) (hExt : SelectorLiteratureInputs c₀)
    {α β : ℝ} (hα : BadlyApproximable α) {r : ℕ → ℕ} (hr : AdmissibleBetaDenominators β r)
    (F : C(Circle, ℂ)) (κF : ℝ≥0) (hF : LipschitzWith κF F)
    (hPhase : CenteredHeisenbergPhaseEstimate d (heisenbergPhase α β) F r) :
    RelativeSelectorComparison c₀ C d ℓ (heisenbergPhase α β) F := by
  have hLaws (S : ℕ) (hS : 2 ≤ S) : NormalizedGowersLaws S :=
    NormalizedGowersLaws.of_triangle_and_adjacent (by omega)
      (fun L U => hExt.gowersTriangle S L U hS) hExt.adjacentMonotonicity
  have hPrime (S : ℕ) (hS : 3 ≤ S) : HighOrderRelativePrimeUniformity c₀ d S :=
    high_order_relative_prime_of_kmtt hc₀ hc₀' hExt.banks hExt.ambientPrimeModel
      hExt.normalizedDilation hExt.relativeCramer hd (by omega) (hLaws S (by omega))
  exact relativeSelectorComparison_of_progression_estimates hc₀ hc₀' hC hd hℓ
    (localGeneralizedVonNeumann_of_kmtt hExt.localInverse) hExt.weightedGowers
    hExt.adjacentMonotonicity hLaws hPrime hExt.bernstein F κF hF hr
    (horizontalCircleEstimate_of_scalar hExt.scalarObstruction α β hα hr) hPhase

/-- The remaining original phase input, quantified over the parameters and
selectors in the recurrence application. -/
def UniformCenteredHeisenbergPhase : Prop :=
  ∀ (d : ℕ) (α β : ℝ), 0 < d → BadlyApproximable α → AdmissibleBeta β →
    ∀ (F : C(Circle, ℂ)) (κF : ℝ≥0), LipschitzWith κF F →
      ∃ r : ℕ → ℕ, AdmissibleBetaDenominators β r ∧
        CenteredHeisenbergPhaseEstimate d (heisenbergPhase α β) F r

/-- Theorem 1.2 conditional on the cited quantitative inputs and the
uniform original centered phase estimate. -/
theorem heisenbergRecurrence_of_centered_phase {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hc₀' : c₀ < 1/11) (hExt : SelectorLiteratureInputs c₀)
    (hWeak : KMTTLocalWeakRegularity) (hPhase : UniformCenteredHeisenbergPhase) :
    HeisenbergRecurrence := by
  apply heisenbergRecurrence_of_relativeSelectorComparison hWeak hc₀
  rintro C d ℓ hC hd hℓ α β hα hβ F ⟨κF, hF⟩
  let F' : C(Circle, ℂ) := ⟨F, hF.continuous⟩
  obtain ⟨r, hr, hPhase⟩ := hPhase d α β hd hα hβ F' κF hF
  exact relativeSelectorComparison_of_centered_phase hc₀ hc₀' hC hd hℓ hExt hα hr F' κF hF hPhase

/-- Corollary 1.3 under the same explicit premises as the Heisenberg
recurrence theorem. -/
theorem bracketRecurrence_of_centered_phase {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hc₀' : c₀ < 1/11) (hExt : SelectorLiteratureInputs c₀)
    (hWeak : KMTTLocalWeakRegularity) (hPhase : UniformCenteredHeisenbergPhase) :
    BracketRecurrence :=
  bracket_recurrence_of_heisenberg_recurrence
    (heisenbergRecurrence_of_centered_phase hc₀ hc₀' hExt hWeak hPhase)

end NilBohr
