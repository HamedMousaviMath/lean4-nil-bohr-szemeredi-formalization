import NilBohr.GowersMultiplier
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.PSeries

/-! Quantitative absolute summability for Lipschitz functions on the circle. -/

open Filter MeasureTheory AddCircle
open scoped BigOperators NNReal ENNReal Topology

namespace NilBohr

noncomputable section

private theorem fourier_add_argument (n : ℤ) (x h : Circle) :
    fourier n (x + h) = fourier n x * fourier n h := by
  simp only [fourier_apply, smul_add, toCircle_add, Circle.coe_mul]

private theorem fourierCoeff_translate (χ : C(Circle, ℂ)) (h : Circle) (n : ℤ) :
    fourierCoeff (fun x => χ (x + h)) n = fourier n h * fourierCoeff χ n := by
  simp only [fourierCoeff, smul_eq_mul]
  calc
    (∫ x : Circle, fourier (-n) x * χ (x + h) ∂haarAddCircle) =
        ∫ x : Circle, fourier n h * (fourier (-n) (x+h) * χ (x+h)) ∂haarAddCircle := by
      apply integral_congr_ae
      filter_upwards [] with x
      have hz : fourier n h * fourier (-n) h = 1 := by
        rw [← fourier_add, add_neg_cancel, fourier_zero]
      rw [fourier_add_argument]
      calc
        _ = ((fourier n h * fourier (-n) h) * fourier (-n) x) * χ (x+h) := by rw [hz, one_mul]
        _ = _ := by ring
    _ = ∫ x : Circle, fourier n h * (fourier (-n) x * χ x) ∂haarAddCircle :=
      integral_add_right_eq_self (μ := (haarAddCircle : Measure Circle))
        (fun x : Circle => fourier n h * (fourier (-n) x * χ x)) h
    _ = _ := integral_const_mul _ _

/-- The difference quotient is continuous in the spatial variable, even
though the limiting derivative of a Lipschitz function need not be. -/
private def circleDifferenceQuotient (χ : C(Circle, ℂ)) (t : ℝ) : C(Circle, ℂ) where
  toFun x := (t : ℂ)⁻¹ * (χ (x + (t : Circle)) - χ x)
  continuous_toFun := by
    exact continuous_const.mul ((χ.continuous.comp (continuous_id.add continuous_const)).sub χ.continuous)

private theorem fourierCoeff_circleDifferenceQuotient (χ : C(Circle, ℂ)) (n : ℤ) (t : ℝ) :
    fourierCoeff (circleDifferenceQuotient χ t) n =
      ((t : ℂ)⁻¹ * (fourier n (t : Circle) - 1)) * fourierCoeff χ n := by
  change fourierCoeff (fun x => (t : ℂ)⁻¹ * (χ (x + (t : Circle)) - χ x)) n = _
  rw [fourierCoeff.const_mul]
  have hadd : fourierCoeff (fun x => χ (x + (t : Circle)) - χ x) n =
      fourierCoeff (fun x => χ (x + (t : Circle))) n - fourierCoeff χ n := by
    simp only [fourierCoeff, smul_eq_mul, mul_sub]
    have h₁ : Continuous (fun x : Circle => fourier (-n) x * χ (x + (t : Circle))) :=
      (fourier (-n)).continuous.mul (χ.continuous.comp (continuous_id.add continuous_const))
    have h₂ : Continuous (fun x : Circle => fourier (-n) x * χ x) :=
      (fourier (-n)).continuous.mul χ.continuous
    exact integral_sub (h₁.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (h₂.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  rw [hadd, fourierCoeff_translate]
  ring

private theorem norm_circleDifferenceQuotient_le (χ : C(Circle, ℂ)) {K : ℝ≥0}
    (hχ : LipschitzWith K χ) {t : ℝ} (ht : t ≠ 0) (x : Circle) :
    ‖circleDifferenceQuotient χ t x‖ ≤ K := by
  have h := hχ.dist_le_mul (x + (t : Circle)) x
  rw [dist_eq_norm, dist_eq_norm, add_sub_cancel_left] at h
  have htNorm : ‖(t : Circle)‖ ≤ |t| := torusNorm_le_abs t
  change ‖(t : ℂ)⁻¹ * (χ (x + (t : Circle)) - χ x)‖ ≤ (K : ℝ)
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs]
  calc
    |t|⁻¹ * ‖χ (x + (t : Circle)) - χ x‖ ≤ |t|⁻¹ * ((K : ℝ) * |t|) := by
      gcongr
      exact h.trans (mul_le_mul_of_nonneg_left htNorm K.coe_nonneg)
    _ = (K : ℝ) := by rw [mul_left_comm, inv_mul_cancel₀ (abs_ne_zero.mpr ht), mul_one]

private theorem sum_sq_fourierCoeff_le (χ : C(Circle, ℂ)) (K : ℝ)
    (hχ : ∀ x, ‖χ x‖ ≤ K) (s : Finset ℤ) :
    ∑ n ∈ s, ‖fourierCoeff χ n‖ ^ 2 ≤ K ^ 2 := by
  let u : Lp ℂ 2 (haarAddCircle : Measure Circle) :=
    ContinuousMap.toLp (E := ℂ) 2 haarAddCircle ℂ χ
  have hS : Summable fun n : ℤ => ‖fourierCoeff χ n‖ ^ 2 := by
    have hs := (lp.memℓp (fourierBasis.repr u)).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, pow_two, fourierBasis_repr,
      u, fourierCoeff_toLp] using hs
  calc
    ∑ n ∈ s, ‖fourierCoeff χ n‖ ^ 2 ≤ ∑' n : ℤ, ‖fourierCoeff χ n‖ ^ 2 :=
      hS.sum_le_tsum s (fun _ _ => sq_nonneg _)
    _ = ∫ x : Circle, ‖χ x‖ ^ 2 ∂haarAddCircle := by
      simp_rw [← fourierCoeff_toLp χ]
      rw [tsum_sq_fourierCoeff]
      apply integral_congr_ae
      filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (haarAddCircle : Measure Circle) χ] with x hx
      change ‖u x‖ ^ 2 = ‖χ x‖ ^ 2
      rw [hx]
    _ ≤ K ^ 2 := by
      have hi : Integrable (fun x : Circle => ‖χ x‖ ^ 2) haarAddCircle :=
        (χ.continuous.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      have hh : ∀ x : Circle, ‖χ x‖ ^ 2 ≤ K ^ 2 :=
        fun x => pow_le_pow_left₀ (norm_nonneg _) (hχ x) 2
      calc
        (∫ x : Circle, ‖χ x‖ ^ 2 ∂haarAddCircle) ≤
            ∫ _ : Circle, K ^ 2 ∂haarAddCircle := integral_mono hi (integrable_const _) hh
        _ = K ^ 2 := by simp

private def angularFrequency (n : ℤ) : ℂ :=
  2 * (Real.pi : ℂ) * Complex.I * n

private theorem tendsto_fourier_difference (n : ℤ) :
    Tendsto (fun t : ℝ => (t : ℂ)⁻¹ * (fourier n (t : Circle) - 1)) (𝓝[≠] 0)
      (𝓝 (angularFrequency n)) := by
  have h : HasDerivAt (fun t : ℝ => Complex.exp (angularFrequency n * (t : ℂ)))
      (angularFrequency n) 0 := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := 0)).const_mul (angularFrequency n)).cexp
  simpa only [zero_add, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
    Complex.real_smul, Complex.ofReal_inv, fourier_coe_apply, angularFrequency,
    Complex.ofReal_one, div_one] using h.tendsto_slope_zero

/-- A Lipschitz function has bounded square energy of its frequency-weighted
Fourier coefficients. The bound is uniform over finite sets of frequencies. -/
private theorem sum_sq_weighted_fourierCoeff_le (χ : C(Circle, ℂ)) {K : ℝ≥0}
    (hχ : LipschitzWith K χ) (s : Finset ℤ) :
    ∑ n ∈ s, (|(n : ℝ)| * ‖fourierCoeff χ n‖) ^ 2 ≤ (K : ℝ) ^ 2 := by
  have hl (n : ℤ) : Tendsto (fun t : ℝ => ‖fourierCoeff (circleDifferenceQuotient χ t) n‖ ^ 2)
      (𝓝[≠] 0) (𝓝 (‖angularFrequency n * fourierCoeff χ n‖ ^ 2)) := by
    simpa only [fourierCoeff_circleDifferenceQuotient] using
      (((tendsto_fourier_difference n).mul_const (fourierCoeff χ n)).norm.pow 2)
  have hs : ∑ n ∈ s, ‖angularFrequency n * fourierCoeff χ n‖ ^ 2 ≤ (K : ℝ) ^ 2 := by
    apply le_of_tendsto (tendsto_finset_sum _ fun n _ => hl n)
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht₀ : t ≠ 0 := ht
    exact sum_sq_fourierCoeff_le _ _ (norm_circleDifferenceQuotient_le χ hχ ht₀) s
  refine (Finset.sum_le_sum fun n _ => ?_).trans hs
  apply pow_le_pow_left₀ (by positivity) _ 2
  have hfreq : ‖angularFrequency n‖ = (2 * Real.pi) * |(n : ℝ)| := by
    simp [angularFrequency, norm_mul, Complex.norm_intCast, Real.norm_eq_abs,
      abs_of_nonneg Real.pi_pos.le]
  rw [norm_mul, hfreq, mul_assoc]
  apply le_mul_of_one_le_left (by positivity)
  linarith [Real.pi_gt_three]

private theorem norm_fourierCoeff_zero_le (χ : C(Circle, ℂ)) :
    ‖fourierCoeff χ 0‖ ≤ ‖χ‖ := by
  simp only [fourierCoeff, neg_zero, fourier_zero, one_smul]
  simpa using norm_integral_le_of_norm_le_const
    (μ := (haarAddCircle : Measure Circle)) (C := ‖χ‖)
    (ae_of_all _ fun x => χ.norm_coe_le_norm x)

/-- The Lipschitz instance of Bernstein's Fourier theorem follows directly
from Parseval for difference quotients and Cauchy–Schwarz. -/
theorem bernsteinCircleLipschitzFourier : BernsteinCircleLipschitzFourier := by
  classical
  let R : ℝ := ∑' n : ℤ, 1 / (n : ℝ) ^ 2
  have hR : 0 ≤ R := tsum_nonneg (by intro n; positivity)
  have hRS : Summable (fun n : ℤ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_int_pow.mpr (by decide : 1 < 2)
  let D := Real.sqrt R
  have hD : 0 ≤ D := Real.sqrt_nonneg _
  refine ⟨1+D, by linarith, ?_⟩
  intro χ K hχ
  have hb (s : Finset ℤ) (h0 : 0 ∉ s) :
      ∑ n ∈ s, ‖fourierCoeff χ n‖ ≤ (K : ℝ) * D := by
    let f (n : ℤ) := |(n : ℝ)| * ‖fourierCoeff χ n‖
    let g (n : ℤ) := |(n : ℝ)|⁻¹
    have hterm (n : ℤ) (hn : n ∈ s) : f n * g n = ‖fourierCoeff χ n‖ := by
      have hn₀ : n ≠ 0 := by rintro rfl; exact h0 hn
      have habs : |(n : ℝ)| ≠ 0 := abs_ne_zero.mpr (by exact_mod_cast hn₀)
      dsimp only [f, g]
      rw [mul_right_comm, mul_inv_cancel₀ habs, one_mul]
    have hf : ∑ n ∈ s, f n ^ 2 ≤ (K : ℝ) ^ 2 :=
      sum_sq_weighted_fourierCoeff_le χ hχ s
    have hg : ∑ n ∈ s, g n ^ 2 ≤ R := by
      simpa only [g, inv_pow, sq_abs, one_div, R] using hRS.sum_le_tsum s (by intros; positivity)
    calc
      ∑ n ∈ s, ‖fourierCoeff χ n‖ = ∑ n ∈ s, f n * g n :=
        Finset.sum_congr rfl fun n hn => (hterm n hn).symm
      _ ≤ Real.sqrt (∑ n ∈ s, f n ^ 2) * Real.sqrt (∑ n ∈ s, g n ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt s f g
      _ ≤ (K : ℝ) * D := by
        have hfs : Real.sqrt (∑ n ∈ s, f n ^ 2) ≤ K := by
          simpa only [Real.sqrt_sq K.coe_nonneg] using Real.sqrt_le_sqrt hf
        exact mul_le_mul hfs (Real.sqrt_le_sqrt hg) (Real.sqrt_nonneg _) K.coe_nonneg
  have hpartial (s : Finset ℤ) : ∑ n ∈ s, ‖fourierCoeff χ n‖ ≤ (1+D) * (‖χ‖ + (K : ℝ)) := by
    have hSub : s ⊆ insert 0 (s.erase 0) := by
      intro n hn
      by_cases heq : n = 0
      · simp [heq]
      · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨heq, hn⟩)
    calc
      ∑ n ∈ s, ‖fourierCoeff χ n‖ ≤ ∑ n ∈ insert 0 (s.erase 0), ‖fourierCoeff χ n‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg hSub (by intros; positivity)
      _ = ‖fourierCoeff χ 0‖ + ∑ n ∈ s.erase 0, ‖fourierCoeff χ n‖ := by
        rw [Finset.sum_insert (Finset.not_mem_erase _ _)]
      _ ≤ ‖χ‖ + (K : ℝ)*D :=
        add_le_add (norm_fourierCoeff_zero_le χ) (hb (s.erase 0) (Finset.not_mem_erase _ _))
      _ ≤ (1+D) * (‖χ‖ + (K : ℝ)) := by
        nlinarith [mul_nonneg hD (norm_nonneg χ), K.coe_nonneg]
  have hSum : Summable (fun n : ℤ => ‖fourierCoeff χ n‖) :=
    summable_of_sum_le (by intro n; exact norm_nonneg _) hpartial
  exact ⟨hSum, hSum.tsum_le_of_sum_le hpartial⟩

private theorem sum_inv_abs_sq_above_le (s : Finset ℤ) {R : ℝ} (hR : 0 < R)
    (hs : ∀ n ∈ s, R < |(n : ℝ)|) :
    ∑ n ∈ s, |(n : ℝ)|⁻¹ ^ 2 ≤ 4 / R := by
  classical
  let k := ⌊R⌋₊
  let m := s.sup Int.natAbs + 1
  let t := Finset.Ioo k m
  let pos : ℕ → ℤ := fun n => n
  let neg : ℕ → ℤ := fun n => -(n : ℤ)
  let f (n : ℤ) := |(n : ℝ)|⁻¹ ^ 2
  have hpos : Function.Injective pos := Nat.cast_injective
  have hneg : Function.Injective neg := neg_injective.comp Nat.cast_injective
  have hsubset : s ⊆ t.image pos ∪ t.image neg := by
    intro n hn
    have habs : n.natAbs ∈ t := by
      refine Finset.mem_Ioo.mpr ⟨?_, Nat.lt_succ_of_le (Finset.le_sup hn)⟩
      have hcast : (k : ℝ) < (n.natAbs : ℝ) := by
        rw [Nat.cast_natAbs, Int.cast_abs]
        exact (Nat.floor_le hR.le).trans_lt (hs n hn)
      exact_mod_cast hcast
    rcases le_total 0 n with h | h
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨n.natAbs, habs, by simp [pos, Int.natCast_natAbs, abs_of_nonneg h]⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨n.natAbs, habs, by simp [neg, Int.natCast_natAbs, abs_of_nonpos h]⟩)
  have hpossum : ∑ n ∈ t.image pos, f n = ∑ i ∈ t, ((i : ℝ) ^ 2)⁻¹ := by
    rw [Finset.sum_image hpos.injOn]
    simp [f, pos, ← inv_pow]
  have hnegsum : ∑ n ∈ t.image neg, f n = ∑ i ∈ t, ((i : ℝ) ^ 2)⁻¹ := by
    rw [Finset.sum_image hneg.injOn]
    simp [f, neg, ← inv_pow]
  have hIoo : ∑ i ∈ t, ((i : ℝ) ^ 2)⁻¹ ≤ 2 / ((k : ℝ) + 1) :=
    sum_Ioo_inv_sq_le k m
  calc
    ∑ n ∈ s, f n ≤ ∑ n ∈ t.image pos ∪ t.image neg, f n :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => sq_nonneg _)
    _ ≤ (∑ n ∈ t.image pos, f n) + ∑ n ∈ t.image neg, f n := by
      have h := Finset.sum_union_inter (s₁ := t.image pos) (s₂ := t.image neg) (f := f)
      have hi : 0 ≤ ∑ n ∈ t.image pos ∩ t.image neg, f n :=
        Finset.sum_nonneg fun _ _ => sq_nonneg _
      linarith only [h, hi]
    _ ≤ 2 / ((k : ℝ) + 1) + 2 / ((k : ℝ) + 1) := by
      rw [hpossum, hnegsum]
      exact add_le_add hIoo hIoo
    _ = 4 / ((k : ℝ) + 1) := by ring
    _ ≤ 4 / R := div_le_div_of_nonneg_left (by norm_num) hR (Nat.lt_floor_add_one R).le

/-- The Fourier mass above a positive real frequency threshold is controlled
by the Lipschitz seminorm alone. -/
theorem fourierCoeff_tail_lipschitz_le (χ : C(Circle, ℂ)) {K : ℝ≥0}
    (hχ : LipschitzWith K χ) {R : ℝ} (hR : 0 < R) :
    (∑' n : ℤ, if R < |(n : ℝ)| then ‖fourierCoeff χ n‖ else 0) ≤
      (K : ℝ) * Real.sqrt (4 / R) := by
  classical
  have hpartial (s : Finset ℤ) :
      ∑ n ∈ s, (if R < |(n : ℝ)| then ‖fourierCoeff χ n‖ else 0) ≤
        (K : ℝ) * Real.sqrt (4 / R) := by
    rw [← Finset.sum_filter]
    let t := s.filter (fun n : ℤ => R < |(n : ℝ)|)
    let f (n : ℤ) := |(n : ℝ)| * ‖fourierCoeff χ n‖
    let g (n : ℤ) := |(n : ℝ)|⁻¹
    have hterm (n : ℤ) (hn : n ∈ t) : f n * g n = ‖fourierCoeff χ n‖ := by
      have hn₀ := hR.trans (Finset.mem_filter.mp hn).2
      dsimp only [f, g]
      rw [mul_right_comm, mul_inv_cancel₀ hn₀.ne', one_mul]
    have hf : ∑ n ∈ t, f n ^ 2 ≤ (K : ℝ) ^ 2 :=
      sum_sq_weighted_fourierCoeff_le χ hχ t
    have hg : ∑ n ∈ t, g n ^ 2 ≤ 4 / R :=
      sum_inv_abs_sq_above_le t hR (fun n hn => (Finset.mem_filter.mp hn).2)
    calc
      ∑ n ∈ t, ‖fourierCoeff χ n‖ = ∑ n ∈ t, f n * g n :=
        Finset.sum_congr rfl fun n hn => (hterm n hn).symm
      _ ≤ Real.sqrt (∑ n ∈ t, f n ^ 2) * Real.sqrt (∑ n ∈ t, g n ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt t f g
      _ ≤ (K : ℝ) * Real.sqrt (4 / R) := by
        have hfs : Real.sqrt (∑ n ∈ t, f n ^ 2) ≤ K := by
          simpa only [Real.sqrt_sq K.coe_nonneg] using Real.sqrt_le_sqrt hf
        exact mul_le_mul hfs (Real.sqrt_le_sqrt hg) (Real.sqrt_nonneg _) K.coe_nonneg
  have hnonneg (n : ℤ) : 0 ≤ (if R < |(n : ℝ)| then ‖fourierCoeff χ n‖ else 0) := by
    split_ifs <;> positivity
  exact (summable_of_sum_le hnonneg hpartial).tsum_le_of_sum_le hpartial

/-- Proposition 6.2's strict Fourier tail cutoff at `η⁻²`, uniformly for
every positive `η` and with the universal constant two. -/
theorem fourierCoeff_tail_eta_le (χ : C(Circle, ℂ)) {K : ℝ≥0}
    (hχ : LipschitzWith K χ) {η : ℝ} (hη : 0 < η) :
    (∑' n : ℤ, if (η ^ 2)⁻¹ < |(n : ℝ)| then ‖fourierCoeff χ n‖ else 0) ≤
      2 * (K : ℝ) * η := by
  have hs : Real.sqrt (4 / (η ^ 2)⁻¹) = 2 * η := by
    rw [div_inv_eq_mul, show (4 : ℝ) * η ^ 2 = (2 * η) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
  have h := fourierCoeff_tail_lipschitz_le χ hχ
    (show 0 < (η ^ 2)⁻¹ by positivity)
  rw [hs, mul_left_comm] at h
  simpa only [mul_assoc] using h

/-- Truncation at the manuscript's cutoff is uniformly accurate on the
circle. In particular this bound applies at every orbit point before
averaging against a prime weight. -/
theorem norm_fourierSeries_truncation_eta_le (χ : C(Circle, ℂ)) {K : ℝ≥0}
    (hχ : LipschitzWith K χ) {η : ℝ} (hη : 0 < η) (x : Circle) :
    ‖χ x - ∑ n ∈ Finset.Icc (-⌊(η ^ 2)⁻¹⌋) ⌊(η ^ 2)⁻¹⌋,
      fourierCoeff χ n • fourier n x‖ ≤ 2 * (K : ℝ) * η := by
  classical
  let R := (η ^ 2)⁻¹
  let s := Finset.Icc (-⌊R⌋) ⌊R⌋
  let t : Set ℤ := (s : Set ℤ)ᶜ
  let a (n : ℤ) := fourierCoeff χ n • fourier n x
  have hcut (n : ℤ) : n ∈ s ↔ |(n : ℝ)| ≤ R := by
    change n ∈ Finset.Icc (-⌊R⌋) ⌊R⌋ ↔ _
    rw [Finset.mem_Icc, ← abs_le, Int.le_floor, Int.cast_abs]
  obtain ⟨_, _, hBernstein⟩ := bernsteinCircleLipschitzFourier
  have hsum : HasSum a (χ x) :=
    has_pointwise_sum_fourier_series_of_summable (hBernstein χ K hχ).1.of_norm x
  have hrest : χ x - (∑ n ∈ s, a n) = ∑' n : t, a n := by
    rw [← hsum.tsum_eq, ← hsum.summable.sum_add_tsum_compl (s := s), add_sub_cancel_left]
  have hnorm (n : ℤ) : ‖a n‖ = ‖fourierCoeff χ n‖ := by
    simp [a, norm_smul, fourier_apply, Circle.norm_coe]
  change ‖χ x - ∑ n ∈ s, a n‖ ≤ _
  rw [hrest]
  calc
    _ ≤ ∑' n : t, ‖a n‖ :=
      norm_tsum_le_tsum_norm (hsum.summable.norm.subtype _)
    _ = ∑' n : ℤ, if R < |(n : ℝ)| then ‖fourierCoeff χ n‖ else 0 := by
      rw [tsum_subtype t (fun n : ℤ => ‖a n‖)]
      apply tsum_congr
      intro n
      have hn : n ∈ t ↔ R < |(n : ℝ)| := by
        change n ∉ s ↔ _
        rw [hcut, not_le]
      simp only [Set.indicator_apply, hn, hnorm]
    _ ≤ _ := fourierCoeff_tail_eta_le χ hχ hη

end

end NilBohr
