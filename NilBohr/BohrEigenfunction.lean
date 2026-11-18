import NilBohr.BracketPointwise

/-! The introductory example in which a Bohr restriction changes the limit. -/

open AddCircle Filter MeasureTheory Set
open scoped BigOperators Topology Interval

namespace NilBohr

private theorem arc_weighted_prime_limit (hV : VinogradovPrimeEquidistribution)
    {θ : ℝ} (hθ : Irrational θ) (J : OpenArc) (F : C(Circle, ℂ))
    (hF : ∀ z, ‖F z‖ ≤ 1) :
    Tendsto (primeAverage (fun p =>
      (J.circleIndicator (θ * ((p : ℝ)-1) : Circle) : ℂ) *
        F (θ * ((p : ℝ)-1) : Circle))) atTop
      (𝓝 (circleMean (J.carrier.indicator (F : Circle → ℂ)))) := by
  classical
  let x : ℕ → Circle := fun p => ((θ * ((p : ℝ)-1) : ℝ) : Circle)
  let G : Circle → ℂ := J.carrier.indicator F
  have hG (z : Circle) : G z = (J.circleIndicator z : ℂ) * F z := by
    by_cases hz : z ∈ J.carrier <;> simp [G, OpenArc.circleIndicator, hz]
  change Tendsto (primeAverage (fun p => (J.circleIndicator (x p) : ℂ) * F (x p)))
    atTop (𝓝 (circleMean G))
  simp_rw [← hG]
  rw [Metric.tendsto_nhds]
  intro δ hδ
  obtain ⟨l,u,K,hl,hu,horder,_,hgap⟩ := J.exists_lipschitz_sandwich (show 0 < δ/4 by positivity)
  let L : C(Circle, ℂ) := ⟨fun z => (l z : ℂ) * F z, (Complex.continuous_ofReal.comp hl.continuous).mul F.continuous⟩
  let g := fun z => u z - l z
  have hg : Continuous g := hu.continuous.sub hl.continuous
  have hbound (z : Circle) : ‖G z - L z‖ ≤ g z := by
    rw [hG]
    change ‖(J.circleIndicator z : ℂ)*F z - (l z : ℂ)*F z‖ ≤ _
    rw [← sub_mul, ← Complex.ofReal_sub, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (sub_nonneg.mpr (horder z).2.1)]
    exact (mul_le_of_le_one_right (sub_nonneg.mpr (horder z).2.1) (hF z)).trans
      (sub_le_sub_right (horder z).2.2.1 _)
  have hIntG : Integrable G (haarAddCircle : Measure Circle) :=
    (F.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).indicator
      (J.carrier_eq_ball.symm ▸ measurableSet_ball)
  have hIntL : Integrable L (haarAddCircle : Measure Circle) :=
    L.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hIntNorm : ‖circleMean G - circleMean L‖ ≤ ∫ z, g z ∂haarAddCircle := by
    rw [circleMean, circleMean, ← integral_sub hIntG hIntL]
    exact (norm_integral_le_integral_norm _).trans
      (integral_mono (hIntG.sub hIntL).norm
        (hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) hbound)
  have hLimit := vinogradov_shifted hV hθ L
  have hGapLimit : Tendsto (fun N => (∑ p ∈ primesThrough N, g (x p)) /
      ((primesThrough N).card : ℝ)) atTop (𝓝 (∫ z, g z ∂haarAddCircle)) := by
    let g' : C(Circle, ℂ) := ⟨fun z => (g z : ℂ), Complex.continuous_ofReal.comp hg⟩
    have h := (Complex.continuous_re.tendsto _).comp (vinogradov_shifted hV hθ g')
    simpa [circleMean, g', primeAverage, ← Complex.ofReal_sum, ← Complex.ofReal_natCast,
      ← Complex.ofReal_div, Function.comp_def, integral_complex_ofReal, x] using h
  have hGapEventually : ∀ᶠ N in (atTop : Filter ℕ),
      (∑ p ∈ primesThrough N, g (x p)) / ((primesThrough N).card : ℝ) < δ/4 :=
    hGapLimit.eventually (gt_mem_nhds hgap)
  filter_upwards [hGapEventually, Metric.tendsto_nhds.mp hLimit (δ/2) (by positivity)] with N hge hle
  have hSeqNorm : ‖primeAverage (G ∘ x) N - primeAverage (L ∘ x) N‖ ≤
      (∑ p ∈ primesThrough N, g (x p)) / ((primesThrough N).card : ℝ) := by
    rw [primeAverage, primeAverage, ← sub_div, ← Finset.sum_sub_distrib, norm_div,
      Complex.norm_natCast]
    exact div_le_div_of_nonneg_right
      ((norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => hbound (x p))) (by positivity)
  have hmiddle : ‖primeAverage (L ∘ x) N - circleMean L‖ < δ/2 := by
    simpa only [dist_eq_norm, Function.comp_apply, x] using hle
  have hend : ‖circleMean L - circleMean G‖ < δ/4 := by
    rw [norm_sub_rev]
    exact hIntNorm.trans_lt hgap
  change dist (primeAverage (G ∘ x) N) (circleMean G) < δ
  rw [dist_eq_norm]
  calc
    _ ≤ ‖primeAverage (G ∘ x) N - primeAverage (L ∘ x) N‖ +
        ‖primeAverage (L ∘ x) N - circleMean L‖ + ‖circleMean L - circleMean G‖ := by
      simpa only [sub_add_sub_cancel] using
        (norm_add_le ((primeAverage (G ∘ x) N - primeAverage (L ∘ x) N) +
          (primeAverage (L ∘ x) N - circleMean L)) (circleMean L - circleMean G)).trans
          (add_le_add_right (norm_add_le _ _) _)
    _ < _ := by linarith [hSeqNorm.trans_lt hge]

/-- The symmetric open arc of radius `ε` around zero on the unit circle. -/
def symmetricBohrArc (ε : ℝ) (hε : 0 < ε) (hhalf : ε < 1/2) : OpenArc :=
  ⟨-ε, 2*ε, by positivity, by linarith⟩

theorem symmetricBohrArc_carrier (ε : ℝ) (hε : 0 < ε) (hhalf : ε < 1/2) :
    (symmetricBohrArc ε hε hhalf).carrier = {x : Circle | ‖x‖ < ε} := by
  rw [OpenArc.carrier_eq_ball]
  simp [symmetricBohrArc, OpenArc.center, Metric.ball, dist_eq_norm]

private theorem fourier_one_phase (x : ℝ) :
    fourier (T := 1) 1 (x : Circle) = phase x := by
  rw [fourier_coe_apply, phase]
  simp

private theorem bohrArc_fourier_mean (ε : ℝ) (hε : 0 < ε) (hhalf : ε < 1/2) :
    circleMean ((symmetricBohrArc ε hε hhalf).carrier.indicator (fourier (T := 1) 1)) =
      ((Real.sin (2 * Real.pi * ε) / Real.pi : ℝ) : ℂ) := by
  let G : Circle → ℂ := (symmetricBohrArc ε hε hhalf).carrier.indicator (fourier (T := 1) 1)
  have hh := AddCircle.intervalIntegral_preimage (1 : ℝ) (-(1/2 : ℝ)) G
  rw [AddCircle.volume_eq_smul_haarAddCircle] at hh
  simp only [ENNReal.ofReal_one, one_smul] at hh
  change circleMean G = _
  rw [circleMean, ← hh, show -(1/2 : ℝ)+1 = 1/2 by ring]
  have hv : (∫ x in -(1/2 : ℝ)..(1/2 : ℝ), G (x : Circle)) =
      ∫ x in -ε..ε, phase x := by
    rw [intervalIntegral.integral_of_le (by norm_num : -(1/2 : ℝ) ≤ 1/2),
      intervalIntegral.integral_of_le (by linarith)]
    let s := Ioc (-(1/2 : ℝ)) (1/2)
    have hEq : ∀ x ∈ s, G (x : Circle) = (Ioo (-ε) ε).indicator phase x := by
      intro x hx
      have hx' : |x| ≤ 1/2 := abs_le.mpr ⟨hx.1.le,hx.2⟩
      have hnorm : ‖(x : Circle)‖ = |x| := (AddCircle.norm_coe_eq_abs_iff 1 (by norm_num)).mpr
        (by simpa using hx')
      have hmem : (x : Circle) ∈ (symmetricBohrArc ε hε hhalf).carrier ↔ x ∈ Ioo (-ε) ε := by
        rw [symmetricBohrArc_carrier]
        change ‖(x : Circle)‖ < ε ↔ _
        rw [hnorm, abs_lt]
        rfl
      have hw := fourier_one_phase x
      by_cases hxI : x ∈ Ioo (-ε) ε
      · simp [G, Set.indicator_of_mem, hmem.mpr hxI, hxI, hw]
      · have hnmem : (x : Circle) ∉ (symmetricBohrArc ε hε hhalf).carrier :=
          fun h => hxI (hmem.mp h)
        simp [G, hnmem, hxI]
    rw [setIntegral_congr_fun measurableSet_Ioc hEq, integral_indicator measurableSet_Ioo,
      Measure.restrict_restrict measurableSet_Ioo]
    have hsub : Ioo (-ε) ε ⊆ s := by intro x hx; exact ⟨by linarith [hx.1],by linarith [hx.2]⟩
    rw [inter_eq_left.mpr hsub, integral_Ioc_eq_integral_Ioo]
  rw [hv]
  unfold phase
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [integral_exp_mul_complex (mul_ne_zero (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) hp)
    Complex.I_ne_zero)]
  have hexp (x : ℝ) : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * x) =
      (Real.cos (2*Real.pi*x) : ℂ) + (Real.sin (2*Real.pi*x) : ℂ) * Complex.I := by
    rw [show 2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) =
        ((2*Real.pi*x : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_mul_I]
    simp
  rw [hexp, hexp, show 2*Real.pi*(-ε) = -(2*Real.pi*ε) by ring,
    Real.cos_neg, Real.sin_neg]
  push_cast
  field_simp [hp, Complex.I_ne_zero]
  ring

/-- The normalized exponential mean along the symmetric Bohr-restricted
primes in the introduction. The selector is exactly the open ball on the
circle, so the endpoints are excluded. -/
theorem symmetricBohr_selected_exponential_tendsto
    (hV : VinogradovPrimeEquidistribution) {θ ε : ℝ} (hθ : Irrational θ)
    (hε : 0 < ε) (hhalf : ε < 1/2) :
    Tendsto (selectedPrimeAverage (fun n => θ * (n : ℝ)) (symmetricBohrArc ε hε hhalf)
      (fun p => phase (θ * ((p : ℝ)-1)))) atTop
      (𝓝 ((Real.sin (2*Real.pi*ε)/(2*Real.pi*ε) : ℝ) : ℂ)) := by
  let J := symmetricBohrArc ε hε hhalf
  let V : ℤ → ℝ := fun n => θ*(n : ℝ)
  let a : ℕ → ℂ := fun p => phase (θ * ((p : ℝ)-1))
  have hnum : Tendsto (selectedOverPrimes V J a) atTop
      (𝓝 ((Real.sin (2*Real.pi*ε)/Real.pi : ℝ) : ℂ)) := by
    have h := arc_weighted_prime_limit hV hθ J (fourier (T := 1) 1)
      (fun z => by rw [fourier_apply]; exact (_root_.Circle.norm_coe _).le)
    rw [bohrArc_fourier_mean ε hε hhalf] at h
    apply h.congr
    intro N
    rw [selectedOverPrimes_eq_weighted]
    congr 1
    funext p
    rw [fourier_one_phase]
    simp [OpenArc.circleIndicator_coe, V, a]
  have hden : Tendsto (fun N => (primeDensityRatio V J N : ℂ)) atTop (𝓝 (↑(2*ε) : ℂ)) := by
    have h := arc_weighted_prime_limit hV hθ J (ContinuousMap.const Circle (1 : ℂ))
      (fun _ => by simp)
    have hmean : circleMean (J.carrier.indicator (fun _ : Circle => (1 : ℂ))) = (↑(2*ε) : ℂ) := by
      rw [circleMean, integral_indicator_const _ (J.carrier_eq_ball.symm ▸ measurableSet_ball),
        measureReal_def, J.haar_carrier, ENNReal.toReal_ofReal J.length_pos.le]
      simp [J, symmetricBohrArc, smul_eq_mul]
    change Tendsto _ atTop (𝓝 (circleMean (J.carrier.indicator (fun _ : Circle => (1 : ℂ))))) at h
    rw [hmean] at h
    apply h.congr
    intro N
    rw [← selectedOverPrimes_one, selectedOverPrimes_eq_weighted]
    congr 1
    funext p
    simp [OpenArc.circleIndicator_coe, V]
  have hne : ((↑(2*ε) : ℂ)) ≠ 0 := by exact_mod_cast (show 2*ε ≠ 0 by positivity)
  have h := hnum.div hden hne
  have heq : ((Real.sin (2*Real.pi*ε)/Real.pi : ℝ) : ℂ) / (↑(2*ε) : ℂ) =
      ((Real.sin (2*Real.pi*ε)/(2*Real.pi*ε) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_div, div_div, show Real.pi*(2*ε) = 2*Real.pi*ε by ring]
  rw [heq] at h
  apply h.congr
  intro N
  exact (selectedPrimeAverage_eq_div_ratio V J a N).symm

/-- For the irrational rotation with eigenfunction `e(t)`, the unrestricted
limit is zero and the symmetric Bohr-restricted limit is nonzero. -/
theorem bohr_rotation_eigenfunction_example (hV : VinogradovPrimeEquidistribution)
    {θ ε : ℝ} (hθ : Irrational θ) (hε : 0 < ε) (hhalf : ε < 1/2) (t : ℝ) :
    let a : ℕ → ℂ := fun p => phase (t + θ*((p : ℝ)-1))
    let s : ℂ := (Real.sin (2*Real.pi*ε)/(2*Real.pi*ε) : ℝ)
    Tendsto (primeAverage a) atTop (𝓝 0) ∧
    Tendsto (selectedPrimeAverage (fun n => θ*(n : ℝ)) (symmetricBohrArc ε hε hhalf) a)
      atTop (𝓝 (phase t * s)) ∧ phase t * s ≠ 0 := by
  dsimp only
  have hzero := circleMean_fourier_eq_zero (h := 1) one_ne_zero
  have hun := vinogradov_shifted hV hθ (fourier (T := 1) 1)
  simp only [hzero, fourier_one_phase] at hun
  have hsel := symmetricBohr_selected_exponential_tendsto hV hθ hε hhalf
  refine ⟨?_, ?_, ?_⟩
  · have h := hun.const_mul (phase t)
    simp only [mul_zero] at h
    apply h.congr
    intro N
    simp only [primeAverage, phase_add, ← Finset.mul_sum, mul_div_assoc]
  · apply (hsel.const_mul (phase t)).congr
    intro N
    simp only [selectedPrimeAverage, phase_add, ← Finset.mul_sum, mul_div_assoc]
  · apply mul_ne_zero
    · exact Complex.exp_ne_zero _
    apply Complex.ofReal_ne_zero.mpr
    have hπ := Real.pi_pos
    apply (div_pos ?_ (by positivity)).ne'
    exact Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith)

end NilBohr
