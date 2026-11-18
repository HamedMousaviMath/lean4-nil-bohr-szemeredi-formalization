import NilBohr.Rotations
import NilBohr.BetaDensity
import NilBohr.LocalPhases

/-! From cancellation of all nonzero Fourier characters to the interval
comparison. -/

namespace NilBohr

open Filter MeasureTheory Polynomial
open scoped Topology BigOperators ENNReal

private theorem integrable_circleContinuous (F : C(Circle, ℂ)) :
    Integrable F AddCircle.haarAddCircle :=
  F.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace F)

private noncomputable def centeredPrimeOperator (V : ℤ → ℝ) (a : ℕ → ℂ) (N : ℕ) :
    C(Circle, ℂ) →ₗ[ℂ] ℂ where
  toFun F := primeAverage (fun p =>
    (F (V ((p : ℤ) - 1) : Circle) - circleMean F) * a p) N
  map_add' F G := by
    have hm : circleMean (F + G : C(Circle, ℂ)) = circleMean F + circleMean G :=
      integral_add (integrable_circleContinuous F) (integrable_circleContinuous G)
    simp only [hm, ContinuousMap.add_apply]
    have h (p : ℕ) :
        (F (V ((p : ℤ) - 1) : Circle) + G (V ((p : ℤ) - 1) : Circle) -
          (circleMean F + circleMean G)) * a p =
        (F (V ((p : ℤ) - 1) : Circle) - circleMean F) * a p +
          (G (V ((p : ℤ) - 1) : Circle) - circleMean G) * a p := by ring
    simp_rw [h]
    simp only [primeAverage, Finset.sum_add_distrib, add_div]
  map_smul' c F := by
    have hm : circleMean (c • F : C(Circle, ℂ)) = c * circleMean F := by
      exact integral_const_mul c F
    simp only [hm, ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    have h (p : ℕ) :
        (c * F (V ((p : ℤ) - 1) : Circle) - c * circleMean F) * a p =
        c * ((F (V ((p : ℤ) - 1) : Circle) - circleMean F) * a p) := by ring
    simp_rw [h]
    simp only [primeAverage, ← Finset.mul_sum, ← mul_div_assoc]

private theorem norm_centeredPrimeOperator_le (V : ℤ → ℝ) (a : ℕ → ℂ) (N : ℕ)
    (F : C(Circle, ℂ)) {B : ℝ} (hB : 0 ≤ B) (ha : ∀ p, ‖a p‖ ≤ B) :
    ‖centeredPrimeOperator V a N F‖ ≤ (2 * ‖F‖) * B := by
  have h_mean : ‖circleMean F‖ ≤ ‖F‖ := by
    have h := norm_integral_le_of_norm_le_const (μ := (AddCircle.haarAddCircle : Measure Circle))
      (Eventually.of_forall F.norm_coe_le_norm)
    simpa [circleMean, measureReal_univ_eq_one] using h
  apply norm_primeAverage_le _ _ _ (by positivity)
  intro p
  rw [norm_mul]
  exact mul_le_mul
    ((norm_sub_le _ _).trans (by linarith [F.norm_coe_le_norm (V ((p : ℤ) - 1) : Circle)]))
    (ha p) (norm_nonneg _) (by positivity)

/-- Once every nonzero Fourier mode cancels, the comparison holds for
every continuous circle weight, by Mathlib's uniform trigonometric
density and the boundedness of the averaging functionals. -/
theorem ae_centered_primeAverage_of_fourier_cancellation
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (V : ℤ → ℝ) (a : X → ℕ → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ᵐ x ∂μ, ∀ p, ‖a x p‖ ≤ B)
    (h_modes : ∀ h : ℤ, h ≠ 0 →
      ∀ᵐ x ∂μ, Tendsto (primeAverage (fun p =>
        fourier (T := 1) h (V ((p : ℤ) - 1) : Circle) * a x p)) atTop (𝓝 0))
    (F : C(Circle, ℂ)) :
    ∀ᵐ x ∂μ, Tendsto (primeAverage (fun p =>
      (F (V ((p : ℤ) - 1) : Circle) - circleMean F) * a x p)) atTop (𝓝 0) := by
  let L (x : X) (N : ℕ) := centeredPrimeOperator V (a x) N
  let span := Submodule.span ℂ (Set.range (fourier (T := 1)))
  have h_trig (G : C(Circle, ℂ)) (hG : G ∈ span) :
      ∀ᵐ x ∂μ, Tendsto (fun N => L x N G) atTop (𝓝 0) := by
    induction hG using Submodule.span_induction with
    | mem G hG =>
      obtain ⟨h, rfl⟩ := hG
      by_cases hh : h = 0
      · subst h
        have h_one : (fourier (T := 1) 0 : Circle → ℂ) = fun _ => 1 :=
          funext (fun _ => fourier_zero)
        have h_mean : circleMean (fourier (T := 1) 0) = 1 := by
          rw [circleMean, h_one, integral_const, measureReal_univ_eq_one, one_smul]
        have hz (x : X) : (fun N => L x N (fourier (T := 1) 0)) = fun _ => 0 := by
          funext N
          simp [L, centeredPrimeOperator, h_mean, fourier_zero, primeAverage]
        exact Eventually.of_forall (fun x => by rw [hz]; exact tendsto_const_nhds)
      · have hz (x : X) : (fun N => L x N (fourier (T := 1) h)) =
          primeAverage (fun p => fourier (T := 1) h (V ((p : ℤ) - 1) : Circle) * a x p) := by
          funext N
          change primeAverage (fun p =>
            (fourier (T := 1) h (V ((p : ℤ) - 1) : Circle) -
              circleMean (fourier (T := 1) h)) * a x p) N = _
          rw [circleMean_fourier_eq_zero hh]
          simp only [sub_zero]
        simpa only [hz] using (show ∀ᵐ x ∂μ, Tendsto (fun N => L x N (fourier (T := 1) h))
          atTop (𝓝 0) from (h_modes h hh).mono (fun x hx => by rwa [hz]))
    | zero =>
      exact Eventually.of_forall (fun x => by simp only [map_zero]; exact tendsto_const_nhds)
    | add F G _ _ hF hG =>
      filter_upwards [hF, hG] with x hxF hxG
      simpa only [map_add, zero_add] using hxF.add hxG
    | smul c F _ hF =>
      filter_upwards [hF] with x hxF
      simpa only [map_smul, smul_eq_mul, mul_zero] using hxF.const_mul c
  have hdense : F ∈ closure (span : Set C(Circle, ℂ)) := by
    change F ∈ span.topologicalClosure
    rw [show span.topologicalClosure = ⊤ from span_fourier_closure_eq_top]
    trivial
  let ε (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)
  choose G hG hclose using fun j : ℕ =>
    Metric.mem_closure_iff.mp hdense (ε j) (by dsimp [ε]; positivity)
  filter_upwards [hb, ae_all_iff.mpr (fun j => h_trig (G j) (hG j))] with x hx hGlim
  change Tendsto (fun N => L x N F) atTop (𝓝 0)
  rw [Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt (div_pos hδ (show 0 < 4 * (B + 1) by positivity))
  have hej : ε j < δ / (4 * (B + 1)) := hj
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.mp (hGlim j) (δ / 2) (by positivity)
  refine ⟨N₀, fun N hN => ?_⟩
  rw [dist_zero_right]
  have h_t := hN₀ N hN
  rw [dist_zero_right] at h_t
  have h_close := hclose j
  rw [dist_eq_norm] at h_close
  calc
    ‖L x N F‖ = ‖L x N (F - G j) + L x N (G j)‖ := by
      rw [← map_add, sub_add_cancel]
    _ ≤ ‖L x N (F - G j)‖ + ‖L x N (G j)‖ := norm_add_le _ _
    _ ≤ (2 * ‖F - G j‖) * B + ‖L x N (G j)‖ :=
      add_le_add_right (norm_centeredPrimeOperator_le V (a x) N _ hB hx) _
    _ < δ := by
      have h_mul := (lt_div_iff₀ (show 0 < 4 * (B + 1) by positivity)).mp hej
      have h_guard := mul_le_mul_of_nonneg_right h_close.le hB
      have hepos : 0 ≤ ε j := by dsimp [ε]; positivity
      nlinarith


/-- Vinogradov's equidistribution of an irrational rotation evaluated at primes,
expressed with continuous circle tests and normalized by the number of primes. -/
def VinogradovPrimeEquidistribution : Prop :=
  ∀ β : ℝ, Irrational β → ∀ F : C(Circle, ℂ),
    Tendsto (primeAverage (fun p => F (β * (p : ℝ) : Circle))) atTop (𝓝 (circleMean F))

/-- The translation by one in the prime parameter preserves the Haar limit. -/
theorem vinogradov_shifted (hV : VinogradovPrimeEquidistribution) {β : ℝ}
    (hβ : Irrational β) (F : C(Circle, ℂ)) :
    Tendsto (primeAverage (fun p => F (β * ((p : ℝ) - 1) : Circle))) atTop (𝓝 (circleMean F)) := by
  let G : C(Circle, ℂ) := ⟨fun t => F (t + ((-β : ℝ) : Circle)),
    F.continuous.comp (continuous_id.add continuous_const)⟩
  have hmean : circleMean G = circleMean F := by
    exact integral_add_right_eq_self (μ := (AddCircle.haarAddCircle : Measure Circle)) F _
  rw [← hmean]
  apply (hV β hβ G).congr
  intro N
  congr 1
  funext p
  have he : β * ((p : ℝ) - 1) = β * (p : ℝ) + -β := by ring
  simp [G, he, AddCircle.coe_add]

private theorem vinogradov_real_shifted (hV : VinogradovPrimeEquidistribution) {β : ℝ}
    (hβ : Irrational β) (F : Circle → ℝ) (hF : Continuous F) :
    Tendsto (fun N => (∑ p ∈ primesThrough N, F (β * ((p : ℝ) - 1) : Circle)) /
      ((primesThrough N).card : ℝ)) atTop (𝓝 (∫ t, F t ∂AddCircle.haarAddCircle)) := by
  let Fℂ : C(Circle, ℂ) := ⟨fun t => (F t : ℂ), Complex.continuous_ofReal.comp hF⟩
  have h := (Complex.continuous_re.tendsto _).comp (vinogradov_shifted hV hβ Fℂ)
  simpa [circleMean, Fℂ, primeAverage, ← Complex.ofReal_sum, ← Complex.ofReal_natCast,
    ← Complex.ofReal_div, Function.comp_def, integral_complex_ofReal] using h

private theorem primeAverage_add_weight (a b : ℕ → ℂ) (N : ℕ) :
    primeAverage (fun p => a p + b p) N = primeAverage a N + primeAverage b N := by
  simp [primeAverage, Finset.sum_add_distrib, add_div]

private theorem primeAverage_sub_weight (a b : ℕ → ℂ) (N : ℕ) :
    primeAverage (fun p => a p - b p) N = primeAverage a N - primeAverage b N := by
  simp [primeAverage, Finset.sum_sub_distrib, sub_div]

private theorem norm_primeAverage_le_weighted_mean (a : ℕ → ℂ) (g : ℕ → ℝ) (N : ℕ)
    (h : ∀ p, ‖a p‖ ≤ g p) :
    ‖primeAverage a N‖ ≤ (∑ p ∈ primesThrough N, g p) / ((primesThrough N).card : ℝ) := by
  rw [primeAverage, norm_div, Complex.norm_natCast]
  exact div_le_div_of_nonneg_right
    ((norm_sum_le _ _).trans (Finset.sum_le_sum (fun p _ => h p))) (by positivity)

/-- Vanishing of all Fourier modes, including the zero mode, implies the
uncentered comparison with any continuous multiplier. -/
theorem ae_primeAverage_mul_continuous_of_modes
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (V : ℤ → ℝ) (a : X → ℕ → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ᵐ x ∂μ, ∀ p, ‖a x p‖ ≤ B)
    (h_modes : ∀ k : ℤ, ∀ᵐ x ∂μ, Tendsto (primeAverage (fun p =>
      fourier (T := 1) k (V ((p : ℤ) - 1) : Circle) * a x p)) atTop (𝓝 0))
    (F : C(Circle, ℂ)) :
    ∀ᵐ x ∂μ, Tendsto (primeAverage (fun p =>
      F (V ((p : ℤ) - 1) : Circle) * a x p)) atTop (𝓝 0) := by
  filter_upwards [ae_centered_primeAverage_of_fourier_cancellation V a hB hb
    (fun k _ => h_modes k) F, h_modes 0] with x hx hx₀
  simp_rw [fourier_zero, one_mul] at hx₀
  have h_eq (N : ℕ) := primeAverage_add_weight
    (fun p => (F (V ((p : ℤ) - 1) : Circle) - circleMean F) * a x p)
    (fun p => circleMean F * a x p) N
  have h_scalar (N : ℕ) : primeAverage (fun p => circleMean F * a x p) N =
      circleMean F * primeAverage (a x) N := by
    unfold primeAverage
    rw [← mul_div_assoc, Finset.mul_sum]
  have h_add := hx.add (hx₀.const_mul (circleMean F))
  rw [mul_zero, zero_add] at h_add
  apply h_add.congr
  intro N
  rw [← h_scalar, ← h_eq]
  congr 1
  funext p
  ring

private noncomputable def segmentTaper (a b δ x : ℝ) : ℝ :=
  max 0 (min 1 (min ((x - a) / δ) ((b - x) / δ)))

private theorem segmentTaper_bounds (a b δ x : ℝ) :
    0 ≤ segmentTaper a b δ x ∧ segmentTaper a b δ x ≤ 1 := by
  unfold segmentTaper
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

private theorem segmentTaper_zero_left {a b δ x : ℝ} (hδ : 0 < δ) (hx : x ≤ a) :
    segmentTaper a b δ x = 0 := by
  unfold segmentTaper
  apply max_eq_left
  exact (min_le_right _ _).trans ((min_le_left _ _).trans
    (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le))

private theorem segmentTaper_zero_right {a b δ x : ℝ} (hδ : 0 < δ) (hx : b ≤ x) :
    segmentTaper a b δ x = 0 := by
  unfold segmentTaper
  apply max_eq_left
  exact (min_le_right _ _).trans ((min_le_right _ _).trans
    (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le))

private theorem segmentTaper_one {a b δ x : ℝ} (hδ : 0 < δ)
    (h₁ : a + δ ≤ x) (h₂ : x ≤ b - δ) : segmentTaper a b δ x = 1 := by
  unfold segmentTaper
  have h₁' : 1 ≤ (x - a) / δ := (le_div_iff₀ hδ).mpr (by linarith)
  have h₂' : 1 ≤ (b - x) / δ := (le_div_iff₀ hδ).mpr (by linarith)
  rw [min_eq_left (le_min h₁' h₂'), max_eq_right (by norm_num)]

private noncomputable def segmentApprox (F : ℝ → ℂ) (hF : Continuous F)
    {a b δ : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hδ : 0 < δ) : C(Circle, ℂ) := by
  let G (x : ℝ) := (segmentTaper a b δ x : ℂ) * F x
  refine ⟨AddCircle.liftIco 1 0 G, AddCircle.liftIco_zero_continuous ?_ ?_⟩
  · simp [G, segmentTaper_zero_left hδ ha, segmentTaper_zero_right hδ hb]
  · apply Continuous.continuousOn
    have h : Continuous (segmentTaper a b δ) := by
      unfold segmentTaper
      fun_prop
    exact (Complex.continuous_ofReal.comp h).mul hF

private noncomputable def endpointRamp (c : Circle) (δ : ℝ) (t : Circle) : ℝ :=
  max 0 (min 1 (2 - dist t c / δ))

private theorem endpointRamp_continuous (c : Circle) (δ : ℝ) :
    Continuous (endpointRamp c δ) := by
  unfold endpointRamp
  fun_prop

private theorem endpointRamp_nonneg (c : Circle) (δ : ℝ) (t : Circle) :
    0 ≤ endpointRamp c δ t := le_max_left _ _

private theorem endpointRamp_one {c t : Circle} {δ : ℝ} (hδ : 0 < δ)
    (h : dist t c ≤ δ) : endpointRamp c δ t = 1 := by
  have hdiv : dist t c / δ ≤ 1 := (div_le_iff₀ hδ).2 (by simpa using h)
  unfold endpointRamp
  rw [min_eq_left (by linarith), max_eq_right (by norm_num)]

private theorem endpointRamp_small_mean (c : Circle) {δ : ℝ} (hδ : 0 < δ)
    (hδ' : 4 * δ < 1) : (∫ t, endpointRamp c δ t ∂AddCircle.haarAddCircle) ≤ 4 * δ := by
  obtain ⟨c', rfl⟩ := QuotientAddGroup.mk_surjective c
  let J : OpenArc := ⟨c' - 2 * δ, 4 * δ, by positivity, hδ'⟩
  have hcenter : J.center = (c' : Circle) := by
    unfold OpenArc.center
    congr 1
    change c' - 2 * δ + 4 * δ / 2 = c'
    ring
  have hj : J.carrier = Metric.ball (c' : Circle) (2 * δ) := by
    rw [J.carrier_eq_ball, hcenter]
    rw [show J.length / 2 = 2 * δ by dsimp [J]; ring]
  change (∫ t, endpointRamp (c' : Circle) δ t ∂AddCircle.haarAddCircle) ≤ J.length
  rw [← J.integral_circleIndicator]
  apply integral_mono
    ((endpointRamp_continuous _ _).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
    ((integrable_const (1 : ℝ)).indicator (by rw [hj]; exact Metric.isOpen_ball.measurableSet))
  intro t
  change endpointRamp (c' : Circle) δ t ≤ J.carrier.indicator (1 : Circle → ℝ) t
  by_cases h : t ∈ J.carrier
  · simp [Set.indicator_of_mem h, endpointRamp]
  · rw [Set.indicator_of_not_mem h]
    have hh : 2 * δ ≤ dist t (c' : Circle) := le_of_not_gt (by simpa [hj] using h)
    have hdiv : 2 ≤ dist t (c' : Circle) / δ := (le_div_iff₀ hδ).2 hh
    unfold endpointRamp
    rw [max_eq_left ((min_le_right _ _).trans (by linarith))]

private theorem segmentApprox_error (F : ℝ → ℂ) (hF : Continuous F)
    (hFn : ∀ t, ‖F t‖ = 1) {a b δ : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hδ : 0 < δ)
    {t : ℝ} (ht : t ∈ Set.Ico 0 1) :
    ‖(if t ∈ Set.Ico a b then F t else 0) - segmentApprox F hF ha hb hδ (t : Circle)‖ ≤
      endpointRamp (a : Circle) δ (t : Circle) + endpointRamp (b : Circle) δ (t : Circle) := by
  classical
  have heval : segmentApprox F hF ha hb hδ (t : Circle) = (segmentTaper a b δ t : ℂ) * F t :=
    AddCircle.liftIco_zero_coe_apply (f := fun x => (segmentTaper a b δ x : ℂ) * F x) ht
  rw [heval]
  have hnn := (segmentTaper_bounds a b δ t).1
  have hle := (segmentTaper_bounds a b δ t).2
  have hnonneg := add_nonneg (endpointRamp_nonneg (a : Circle) δ (t : Circle))
    (endpointRamp_nonneg (b : Circle) δ (t : Circle))
  by_cases h : t ∈ Set.Ico a b
  · rw [if_pos h]
    by_cases hi : a + δ ≤ t ∧ t ≤ b - δ
    · rw [segmentTaper_one hδ hi.1 hi.2, Complex.ofReal_one, one_mul, sub_self, norm_zero]
      exact hnonneg
    · have hdist (s : ℝ) : dist (t : Circle) (s : Circle) ≤ |t - s| := by
        rw [dist_eq_norm, ← AddCircle.coe_sub]
        exact torusNorm_le_abs _
      have err : ‖F t - (segmentTaper a b δ t : ℂ) * F t‖ ≤ 1 := by
        rw [← one_sub_mul, ← Complex.ofReal_one, ← Complex.ofReal_sub, norm_mul, hFn,
          mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
        linarith
      push_neg at hi
      by_cases h₁ : a + δ ≤ t
      · have h₂ := hi h₁
        have hb' : dist (t : Circle) (b : Circle) ≤ δ := (hdist b).trans (by
          rw [abs_of_nonpos (sub_nonpos.mpr h.2.le)]
          linarith)
        rw [endpointRamp_one hδ hb']
        exact err.trans (le_add_of_nonneg_left (endpointRamp_nonneg _ _ _))
      · have ha' : dist (t : Circle) (a : Circle) ≤ δ := (hdist a).trans (by
          rw [abs_of_nonneg (sub_nonneg.mpr h.1)]
          linarith)
        rw [endpointRamp_one hδ ha']
        exact err.trans (le_add_of_nonneg_right (endpointRamp_nonneg _ _ _))
  · rw [if_neg h]
    have hz : segmentTaper a b δ t = 0 := by
      rcases lt_or_ge t a with hl | hl
      · exact segmentTaper_zero_left hδ hl.le
      · exact segmentTaper_zero_right hδ (le_of_not_gt (fun hr => h ⟨hl, hr⟩))
    simpa [hz] using hnonneg

/-- A piecewise multiplier on a half-open horizontal interval can be tapered
in arbitrarily narrow endpoint strips. Vinogradov's theorem controls those
strips independently of the bounded ergodic inputs. -/
theorem ae_primeAverage_segment_mul_of_modes
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (hV : VinogradovPrimeEquidistribution) {β : ℝ} (hβ : Irrational β)
    (u : X → ℕ → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (h_u : ∀ᵐ x ∂μ, ∀ p, ‖u x p‖ ≤ B)
    (h_modes : ∀ k : ℤ, ∀ᵐ x ∂μ,
      Tendsto (primeAverage (fun p => fourier (T := 1) k
        (β * ((p : ℝ) - 1) : Circle) * u x p)) atTop (𝓝 0))
    (F : ℝ → ℂ) (hF : Continuous F) (hFn : ∀ t, ‖F t‖ = 1)
    {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    ∀ᵐ x ∂μ, Tendsto (primeAverage (fun p =>
      let t := Int.fract (β * ((p : ℝ) - 1))
      (if t ∈ Set.Ico a b then F t else 0) * u x p)) atTop (𝓝 0) := by
  let δ (j : ℕ) : ℝ := (1 / ((j : ℝ) + 1)) / 8
  have hδ (j : ℕ) : 0 < δ j := by dsimp [δ]; positivity
  have hδ' (j : ℕ) : 4 * δ j < 1 := by
    dsimp [δ]
    have hu : 1 / ((j : ℝ) + 1) ≤ 1 :=
      (div_le_iff₀ (by positivity)).mpr (by linarith [(show (0 : ℝ) ≤ j by positivity)])
    linarith
  let G (j : ℕ) := segmentApprox F hF ha hb (hδ j)
  let gap (j : ℕ) (t : Circle) :=
    endpointRamp (a : Circle) (δ j) t + endpointRamp (b : Circle) (δ j) t
  have hlim (j : ℕ) : ∀ᵐ x ∂μ, Tendsto (primeAverage (fun p =>
      G j (β * ((p : ℝ) - 1) : Circle) * u x p)) atTop (𝓝 0) := by
    have hw : ∀ p : ℕ, (β * (((p : ℕ) : ℤ) - 1 : ℤ) : ℝ) = β * ((p : ℝ) - 1) := by
      simp
    have hm (k : ℤ) : ∀ᵐ x ∂μ, Tendsto (primeAverage (fun p =>
        fourier (T := 1) k (β * ((((p : ℕ) : ℤ) - 1 : ℤ) : ℝ) : Circle) * u x p))
          atTop (𝓝 0) := by simpa only [hw] using h_modes k
    simpa only [hw] using
      (ae_primeAverage_mul_continuous_of_modes (fun n => β * (n : ℝ)) u hB h_u hm (G j))
  have hgap_cont (j : ℕ) : Continuous (gap j) :=
    (endpointRamp_continuous _ _).add (endpointRamp_continuous _ _)
  have hmean (j : ℕ) : (∫ t, gap j t ∂AddCircle.haarAddCircle) ≤ 8 * δ j := by
    have hi (c : Circle) : Integrable (endpointRamp c (δ j)) AddCircle.haarAddCircle :=
      (endpointRamp_continuous _ _).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    unfold gap
    rw [integral_add (hi _) (hi _)]
    linarith [endpointRamp_small_mean (a : Circle) (hδ j) (hδ' j),
      endpointRamp_small_mean (b : Circle) (hδ j) (hδ' j)]
  filter_upwards [h_u, ae_all_iff.mpr hlim] with x hx hxl
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let ρ := ε / (4 * (B + 1))
  have hρ : 0 < ρ := div_pos hε (by positivity)
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hρ
  have hj' : 8 * δ j < ρ := by dsimp [δ]; linarith
  have hg := vinogradov_real_shifted hV hβ (gap j) (hgap_cont j)
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.mp (hxl j) (ε / 2) (by positivity)
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp hg ρ hρ
  refine ⟨max N₀ N₁, fun N hN => ?_⟩
  let U (p : ℕ) : ℂ := (if Int.fract (β * ((p : ℝ) - 1)) ∈ Set.Ico a b
    then F (Int.fract (β * ((p : ℝ) - 1))) else 0) * u x p
  let A (p : ℕ) : ℂ := G j (β * ((p : ℝ) - 1) : Circle) * u x p
  let Δ (p : ℕ) : ℝ := gap j (β * ((p : ℝ) - 1) : Circle)
  have hclose : ‖primeAverage A N‖ < ε / 2 := by
    simpa only [dist_zero_right] using hN₀ N ((le_max_left _ _).trans hN)
  have hmeanN : (∑ p ∈ primesThrough N, Δ p) / ((primesThrough N).card : ℝ) < 2 * ρ := by
    have he := hN₁ N ((le_max_right _ _).trans hN)
    rw [Real.dist_eq] at he
    change |(∑ p ∈ primesThrough N, Δ p) / ((primesThrough N).card : ℝ) -
      (∫ t, gap j t ∂AddCircle.haarAddCircle)| < ρ at he
    linarith [lt_of_le_of_lt (le_abs_self _) he, hmean j]
  have herror (p : ℕ) : ‖U p - A p‖ ≤ B * Δ p := by
    dsimp [U, A, Δ, G, gap]
    rw [← sub_mul, norm_mul]
    let z := β * ((p : ℝ) - 1)
    have hz := segmentApprox_error F hF hFn ha hb (hδ j)
      (t := Int.fract z) ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
    simp only [AddCircle.coe_fract] at hz
    rw [mul_comm B]
    exact mul_le_mul hz (hx p) (norm_nonneg _) (add_nonneg
      (endpointRamp_nonneg _ _ _) (endpointRamp_nonneg _ _ _))
  have hh := norm_primeAverage_le_weighted_mean (fun p => U p - A p) (fun p => B * Δ p) N herror
  rw [primeAverage_sub_weight, ← Finset.mul_sum, mul_div_assoc] at hh
  have hscale : B * (2 * ρ) ≤ ε / 2 := by
    dsimp [ρ]
    rw [show B * (2 * (ε / (4 * (B + 1)))) = (2 * B * ε) / (4 * (B + 1)) by ring]
    exact (div_le_iff₀ (by positivity)).mpr (by nlinarith)
  rw [dist_zero_right]
  change ‖primeAverage U N‖ < ε
  calc
    ‖primeAverage U N‖ = ‖(primeAverage U N - primeAverage A N) + primeAverage A N‖ := by
      rw [sub_add_cancel]
    _ ≤ ‖primeAverage U N - primeAverage A N‖ + ‖primeAverage A N‖ := norm_add_le _ _
    _ < ε := by
      have hm := mul_le_mul_of_nonneg_left hmeanN.le hB
      linarith

private theorem fourier_to_phase (k : ℤ) (x : ℝ) :
    fourier (T := 1) k (x : Circle) = phase ((k : ℝ) * x) := by
  simp only [fourier_coe_apply, Complex.ofReal_one, div_one, phase,
    Complex.ofReal_mul, Complex.ofReal_intCast, mul_assoc]

private theorem ae_heisenberg_fourier_horizontal_twist
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    (T : ProbabilitySystem X μ) {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ)
    (hP : ErgodicPolynomialFamily P) (f : Fin ℓ → X → ℂ)
    (hf : ∀ i, MemLp (f i) ∞ μ) (α β : ℝ) (h : ℤ) (hh : h ≠ 0)
    (ψ : Polynomial ℝ) (hψ : ψ.natDegree ≤ 2)
    (hs : ∀ (S : ProbabilitySystem (X × (Circle × Circle)) (μ.prod twoTorusHaar))
      {d : ℕ} (Q : Fin d → Polynomial ℤ), ErgodicPolynomialFamily Q →
      SmoothPrimeLimit S Q (heisenbergPhase α β))
    (k : ℤ) : ∀ᵐ x ∂μ, Tendsto (primeAverage (fun p =>
      fourier (T := 1) k (β * ((p : ℝ) - 1) : Circle) *
        (phase (-(h : ℝ) * heisenbergPhase α β ((p : ℤ) - 1) + ψ.eval ((p : ℝ) - 1)) *
          ergodicSequence T P f ((p : ℤ) - 1) x))) atTop (𝓝 0) := by
  let Q := ψ + C ((k : ℝ) * β) * Polynomial.X
  have hQ : Q.natDegree ≤ 2 := by
    have hm : (C ((k : ℝ) * β) * Polynomial.X).natDegree ≤ 2 :=
      (natDegree_C_mul_le _ _).trans (by simp)
    unfold Q
    exact (natDegree_add_le _ _).trans (max_le hψ hm)
  have ht := ae_tendsto_primeAverage_fourier_quadratic_twist T P hP f hf
    (heisenbergPhase α β) (-h) (neg_ne_zero.mpr hh) Q hQ hs
  filter_upwards [ht] with x hx
  apply hx.congr
  intro N
  congr 1
  funext p
  simp only [Q, eval_add, eval_mul, eval_C, eval_X, Int.cast_neg, fourier_to_phase,
    ← mul_assoc, ← phase_add]
  congr 2
  ring

/-- Every nonzero Fourier mode of the bracket phase has zero ergodic prime
average. The proof keeps the two half-open cells, with the seam in the upper
one, and controls their endpoint strips by scalar prime equidistribution. -/
theorem ae_bracket_fourier_cancellation
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    (hV : VinogradovPrimeEquidistribution) (T : ProbabilitySystem X μ)
    {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ) (hP : ErgodicPolynomialFamily P)
    (f : Fin ℓ → X → ℂ) (hf : ∀ i, MemLp (f i) ∞ μ)
    (α β : ℝ) (hβ : AdmissibleBeta β)
    (hs : ∀ (S : ProbabilitySystem (X × (Circle × Circle)) (μ.prod twoTorusHaar))
      {d : ℕ} (Q : Fin d → Polynomial ℤ), ErgodicPolynomialFamily Q →
      SmoothPrimeLimit S Q (heisenbergPhase α β))
    (h : ℤ) (hh : h ≠ 0) :
    ∀ᵐ x ∂μ, Tendsto (primeAverage (fun p =>
      fourier (T := 1) h (bracketPhase α β ((p : ℤ) - 1) : Circle) *
        ergodicSequence T P f ((p : ℤ) - 1) x)) atTop (𝓝 0) := by
  classical
  let A : Polynomial ℝ := C ((h : ℝ) * (α * β / 2)) * (Polynomial.X ^ 2 + Polynomial.X)
  let B : Polynomial ℝ := A + C ((h : ℝ) * α) * Polynomial.X
  have hA : A.natDegree ≤ 2 := by
    unfold A
    apply (natDegree_C_mul_le _ _).trans
    exact (natDegree_add_le _ _).trans (max_le (by simp) (by simp))
  have hB : B.natDegree ≤ 2 := by
    unfold B
    exact (natDegree_add_le _ _).trans (max_le hA ((natDegree_C_mul_le _ _).trans (by simp)))
  let F (t : ℝ) := phase (-(h : ℝ) * α * t)
  let G (t : ℝ) := phase ((h : ℝ) * α * (1 - t))
  have hF : Continuous F := by dsimp [F, phase]; fun_prop
  have hG : Continuous G := by dsimp [G, phase]; fun_prop
  let u (Q : Polynomial ℝ) (x : X) (p : ℕ) :=
    phase (-(h : ℝ) * heisenbergPhase α β ((p : ℤ) - 1) + Q.eval ((p : ℝ) - 1)) *
      ergodicSequence T P f ((p : ℤ) - 1) x
  obtain ⟨C₀, hC, hu⟩ := ae_ergodicSequence_bounded T P f hf
  have hub (Q : Polynomial ℝ) : ∀ᵐ x ∂μ, ∀ p, ‖u Q x p‖ ≤ C₀ :=
    hu.mono (fun x hx p => by simpa only [u, norm_mul, norm_phase, one_mul] using hx ((p : ℤ) - 1))
  have hseg₁ := ae_primeAverage_segment_mul_of_modes hV hβ.liouville.irrational (u A) hC (hub A)
    (ae_heisenberg_fourier_horizontal_twist T P hP f hf α β h hh A hA hs) F hF
    (fun t => norm_phase _) (a := 0) (b := 1 - β) (by norm_num) (by linarith [hβ.1])
  have hseg₂ := ae_primeAverage_segment_mul_of_modes hV hβ.liouville.irrational (u B) hC (hub B)
    (ae_heisenberg_fourier_horizontal_twist T P hP f hf α β h hh B hB hs) G hG
    (fun t => norm_phase _) (a := 1 - β) (b := 1) (by linarith [hβ.2.1]) (by norm_num)
  filter_upwards [hseg₁, hseg₂] with x hx₁ hx₂
  have hlim := hx₁.add hx₂
  rw [zero_add] at hlim
  apply hlim.congr
  intro N
  simp only [← primeAverage_add_weight]
  congr 1
  funext p
  let n : ℤ := (p : ℤ) - 1
  let t := Int.fract (β * ((p : ℝ) - 1))
  have hn : (n : ℝ) = (p : ℝ) - 1 := by simp [n]
  have ht₀ : 0 ≤ t := Int.fract_nonneg _
  have ht₁ : t < 1 := Int.fract_lt_one _
  have hphase := phase_bracket_eq_piecewise α β n h hβ.1.le hβ.2.1.le
  change phase ((h : ℝ) * bracketPhase α β n) = _ at hphase
  simp only [hn] at hphase
  dsimp only [n] at hphase
  simp only [t] at ht₀ ht₁
  simp only [fourier_to_phase]
  rw [hphase]
  simp only [u, A, B, eval_add, eval_mul, eval_C, eval_X, eval_pow, F, G]
  by_cases ht : t < 1 - β
  · have h₁ : t ∈ Set.Ico 0 (1 - β) := ⟨ht₀, ht⟩
    have h₂ : t ∉ Set.Ico (1 - β) 1 := fun ht' => (not_le_of_gt ht) ht'.1
    simp only [t] at ht h₁ h₂
    simp only [h₁, h₂, ht, if_true, if_false, zero_mul, add_zero]
    ring
  · have h₁ : t ∉ Set.Ico 0 (1 - β) := fun ht' => ht ht'.2
    have h₂ : t ∈ Set.Ico (1 - β) 1 := ⟨le_of_not_gt ht, ht₁⟩
    simp only [t] at ht h₁ h₂
    simp only [h₁, h₂, ht, if_true, if_false, zero_mul, zero_add, phase_add]
    ring

/-- The bracket version of the smooth comparison of Proposition 7.1 follows
from the Heisenberg comparison on the two-circle product systems and the
classical scalar Vinogradov input. -/
theorem bracket_smooth_of_heisenberg_smooth
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    (hV : VinogradovPrimeEquidistribution) (T : ProbabilitySystem X μ)
    {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ) (hP : ErgodicPolynomialFamily P)
    (α β : ℝ) (hβ : AdmissibleBeta β)
    (hs : ∀ (S : ProbabilitySystem (X × (Circle × Circle)) (μ.prod twoTorusHaar))
      {d : ℕ} (Q : Fin d → Polynomial ℤ), ErgodicPolynomialFamily Q →
      SmoothPrimeLimit S Q (heisenbergPhase α β)) :
    SmoothPrimeLimit T P (bracketPhase α β) := by
  intro f hf F hF
  obtain ⟨K, hK⟩ := hF
  obtain ⟨B, hB, hb⟩ := ae_ergodicSequence_bounded T P f hf
  exact ae_centered_primeAverage_of_fourier_cancellation (bracketPhase α β)
    (fun x p => ergodicSequence T P f ((p : ℤ) - 1) x) hB
    (hb.mono (fun x hx p => hx ((p : ℤ) - 1)))
    (ae_bracket_fourier_cancellation hV T P hP f hf α β hβ hs) ⟨F, hK.continuous⟩

/-- Conditional pointwise bracket-selector theorem (Corollary 1.5).
The paper's Heisenberg smooth comparison is required on the rotation
extensions underlying the quadratic twists. The other premises are the
classical Vinogradov theorem, PNT, and Mirek–Wan–Wright. -/
theorem pointwise_bracket_of_heisenberg_smooth
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    (hV : VinogradovPrimeEquidistribution) (hPNT : PrimeNumberTheorem)
    (hMWW : MirekWanWrightPointwise X) (T : ProbabilitySystem X μ)
    {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ) (hP : ErgodicPolynomialFamily P)
    (f : Fin ℓ → X → ℂ) (hf : ∀ i, MemLp (f i) ∞ μ)
    (α β : ℝ) (hβ : AdmissibleBeta β) (J : OpenArc)
    (hs : ∀ (S : ProbabilitySystem (X × (Circle × Circle)) (μ.prod twoTorusHaar))
      {d : ℕ} (Q : Fin d → Polynomial ℤ), ErgodicPolynomialFamily Q →
      SmoothPrimeLimit S Q (heisenbergPhase α β)) :
    PrimePointwiseConclusion T P f (bracketPhase α β) J :=
  pointwise_of_smooth_limits T P f hf (bracketPhase α β) J
    (bracket_smooth_of_heisenberg_smooth hV T P hP α β hβ hs)
    (ae_unrestrictedPrimeAverage_tendsto hPNT hMWW T P hP f hf)

/-- Corollary 1.5 at the original quantifiers. The remaining manuscript input
is the logarithmic L¹ estimate on the relevant rotation extensions. -/
theorem bracket_pointwise_of_heisenberg_log_decay
    (X : Type*) [MeasurableSpace X]
    (hV : VinogradovPrimeEquidistribution) (hPNT : PrimeNumberTheorem)
    (hMWW : MirekWanWrightPointwise X)
    (hlog : ∀ (μ : Measure X) [IsProbabilityMeasure μ]
      (S : ProbabilitySystem (X × (Circle × Circle)) (μ.prod twoTorusHaar))
      {d : ℕ} (Q : Fin d → Polynomial ℤ), ErgodicPolynomialFamily Q →
      ∀ α β : ℝ, BadlyApproximable α → AdmissibleBeta β →
      SmoothErgodicLogDecay S Q (heisenbergPhase α β)) :
    PrimePointwiseFor X bracketPhase := by
  intro μ hμ T ℓ P hP f hf α β hα hβ J
  exact pointwise_bracket_of_heisenberg_smooth hV hPNT hMWW T P hP f hf α β hβ J
    (fun S _ Q hQ => smoothPrimeLimit_of_log_decay hPNT S Q _ (hlog μ S Q hQ α β hα hβ))

end NilBohr
