import NilBohr.SelectorCutoffInput
import NilBohr.GowersMultiplier
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! Explicit partition by three distance tents away from the boundary of
the unit circle chart. A lower cutoff in the common denominator makes
the functions Lipschitz while localizing the uncovered part. -/

open AddCircle MeasureTheory Metric Set
open scoped NNReal BigOperators

namespace NilBohr

private noncomputable def chartCenter (j : Fin 3) : ℝ := 1/5 + (j.val : ℝ)*(3/10)

private theorem chartCenter_bounds (j : Fin 3) :
    (1:ℝ)/5 ≤ chartCenter j ∧ chartCenter j ≤ 4/5 := by
  fin_cases j <;> norm_num [chartCenter]

private noncomputable def chartRadius (ε : ℝ) : ℝ := 1/5 - ε/4

private noncomputable def chartTent (ε : ℝ) (j : Fin 3) (x : Circle) : ℝ :=
  max 0 (chartRadius ε - dist x (chartCenter j : Circle))

private theorem chartTent_nonneg (ε : ℝ) (j : Fin 3) (x : Circle) : 0 ≤ chartTent ε j x :=
  le_max_left _ _

private theorem chartTent_lipschitz (ε : ℝ) (j : Fin 3) : LipschitzWith 1 (chartTent ε j) := by
  unfold chartTent
  simpa only [zero_add] using
    ((LipschitzWith.const (chartRadius ε)).sub
      (LipschitzWith.dist_left (chartCenter j : Circle))).const_max 0

private theorem chartTent_support {ε : ℝ} (hε : 0 < ε) (j : Fin 3) {t : ℝ}
    (ht : t ∈ Ico (0:ℝ) 1) (hn : chartTent ε j (t : Circle) ≠ 0) :
    t ∈ Icc (chartCenter j - chartRadius ε) (chartCenter j + chartRadius ε) := by
  have hDist : dist (t : Circle) (chartCenter j : Circle) < chartRadius ε := by
    by_contra! h
    exact hn (max_eq_left (sub_nonpos.mpr h))
  rw [dist_eq_norm, ← AddCircle.coe_sub, AddCircle.norm_eq] at hDist
  simp only [inv_one, one_mul, mul_one] at hDist
  obtain ⟨hj₀, hj₁⟩ := chartCenter_bounds j
  let z : ℤ := round (t-chartCenter j)
  change |t-chartCenter j-(z : ℝ)| < chartRadius ε at hDist
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hDist
  have hz : z = 0 := by
    by_contra hnz
    rcases lt_or_gt_of_ne hnz with h | h
    · have hh : (z : ℝ) ≤ -1 := by exact_mod_cast (show z ≤ -1 by omega)
      linarith [ht.1, show chartRadius ε ≤ 1/5 by unfold chartRadius; linarith]
    · have hh : (1 : ℝ) ≤ z := by exact_mod_cast (show 1 ≤ z by omega)
      linarith [ht.2, show chartRadius ε ≤ 1/5 by unfold chartRadius; linarith]
  rw [hz, Int.cast_zero, sub_zero] at hlo hhi
  exact ⟨by linarith, by linarith⟩

private noncomputable def chartTentSum (ε : ℝ) (x : Circle) : ℝ :=
  ∑ j : Fin 3, chartTent ε j x

private theorem chartTent_le_sum (ε : ℝ) (j : Fin 3) (x : Circle) :
    chartTent ε j x ≤ chartTentSum ε x :=
  Finset.single_le_sum (fun i _ => chartTent_nonneg ε i x) (Finset.mem_univ j)

private theorem chartTentSum_nonneg (ε : ℝ) (x : Circle) : 0 ≤ chartTentSum ε x :=
  Finset.sum_nonneg fun j _ => chartTent_nonneg ε j x

private theorem chartTentSum_lipschitz (ε : ℝ) : LipschitzWith 3 (chartTentSum ε) := by
  have h : (1+1+1 : ℝ≥0) = 3 := by norm_num
  have hLip := ((chartTent_lipschitz ε 0).add (chartTent_lipschitz ε 1)).add (chartTent_lipschitz ε 2)
  rw [h] at hLip
  convert hLip using 1
  funext x
  exact Fin.sum_univ_three _

private theorem norm_coe_circle_le_abs (x : ℝ) : ‖(x : Circle)‖ ≤ |x| := by
  rw [AddCircle.norm_eq]
  simpa using (round_le x 0)

private theorem chartDist_coe_eq_abs {x c : ℝ} (h : |x-c| ≤ 1/2) :
    dist (x : Circle) (c : Circle) = |x-c| := by
  rw [dist_eq_norm, ← AddCircle.coe_sub]
  exact (AddCircle.norm_coe_eq_abs_iff 1 (by norm_num)).2 (by simpa using h)

private theorem chartTentSum_lower {ε : ℝ} (hε₀ : 0 < ε) (hε : ε < 1/16) {x : Circle}
    (hx : ε ≤ ‖x‖) : ε/2 ≤ chartTentSum ε x := by
  let t := AddCircle.equivIco (1 : ℝ) 0 x
  have ht : (0:ℝ) ≤ t.val ∧ t.val < 1 := by simpa using t.property
  have htx : (t.val : Circle) = x := (AddCircle.equivIco (1 : ℝ) 0).symm_apply_apply x
  have htlo : ε ≤ t.val := by
    rw [← htx] at hx
    exact hx.trans (by simpa [abs_of_nonneg ht.1] using norm_coe_circle_le_abs t.val)
  have hthi : ε ≤ 1-t.val := by
    have heq : ((t.val - 1 : ℝ) : Circle) = x := by
      rw [AddCircle.coe_sub, htx]
      change x - ((1:ℝ) : AddCircle (1:ℝ)) = x
      simp
    simpa [heq, abs_of_nonpos (by linarith [ht.2] : t.val - 1 ≤ 0)] using
      hx.trans (show ‖x‖ ≤ |t.val-1| from heq ▸ norm_coe_circle_le_abs (t.val-1))
  have lower_of_close (j : Fin 3) (hd : |t.val-chartCenter j| ≤ 1/5-3*ε/4) :
      ε/2 ≤ chartTentSum ε x := by
    have hdist := chartDist_coe_eq_abs (show |t.val-chartCenter j| ≤ 1/2 by linarith)
    rw [htx] at hdist
    apply le_trans _ (chartTent_le_sum ε j x)
    unfold chartTent chartRadius
    rw [hdist]
    exact le_trans (by linarith) (le_max_right _ _)
  by_cases h₁ : t.val ≤ 7/20
  · apply lower_of_close 0
    norm_num [chartCenter, abs_le]
    exact ⟨by linarith, by linarith⟩
  · by_cases h₂ : t.val ≤ 13/20
    · apply lower_of_close 1
      norm_num [chartCenter, abs_le]
      exact ⟨by linarith, by linarith⟩
    · apply lower_of_close 2
      norm_num [chartCenter, abs_le]
      exact ⟨by linarith, by linarith⟩

private theorem lipschitz_div_cutoff {a b : Circle → ℝ} {A B : ℝ≥0}
    (ha : LipschitzWith A a) (hb : LipschitzWith B b) {r : ℝ} (hr : 0 < r)
    (ha₀ : ∀ x, 0 ≤ a x) (hab : ∀ x, a x ≤ b x) (hrb : ∀ x, r ≤ b x) :
    LipschitzWith (⟨(A+B:ℝ≥0)/r, by positivity⟩ : ℝ≥0) (fun x => a x / b x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq, NNReal.coe_mk, NNReal.coe_add] at *
  have h1 := ha.dist_le_mul x y
  have h2 := hb.dist_le_mul y x
  rw [Real.dist_eq] at h1 h2
  rw [dist_comm y x] at h2
  have hx : 0 < b x := hr.trans_le (hrb x)
  have hy : 0 < b y := hr.trans_le (hrb y)
  have heq : a x / b x - a y / b y =
      ((a x - a y) + (a y / b y)*(b y-b x)) / b x := by
    field_simp
    ring
  have hy₀ : 0 ≤ a y / b y := div_nonneg (ha₀ y) hy.le
  have hy₁ : a y / b y ≤ 1 := (div_le_one hy).mpr (hab y)
  rw [heq, abs_div, abs_of_pos hx]
  refine ((div_le_div_of_nonneg_right (abs_add_le _ _) hx.le).trans ?_)
  rw [abs_mul, abs_of_nonneg hy₀]
  refine (div_le_div_of_nonneg_right (add_le_add h1
    ((mul_le_of_le_one_left (abs_nonneg _) hy₁).trans h2)) hx.le).trans ?_
  rw [← add_mul, div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_left (by positivity) hr (hrb x)

private noncomputable def chartDenominator (ε : ℝ) (x : Circle) : ℝ :=
  max (chartTentSum ε x) (ε/2)

private theorem chartDenominator_lipschitz (ε : ℝ) :
    LipschitzWith 3 (chartDenominator ε) :=
  (chartTentSum_lipschitz ε).max_const _

private noncomputable def chartPiece (ε : ℝ) (j : Fin 3) (x : Circle) : ℝ :=
  chartTent ε j x / chartDenominator ε x

private noncomputable def chartBoundary (ε : ℝ) (x : Circle) : ℝ :=
  1-chartTentSum ε x / chartDenominator ε x

private theorem chartPiece_bounds {ε : ℝ} (hε : 0 < ε) (j : Fin 3) (x : Circle) :
    0 ≤ chartPiece ε j x ∧ chartPiece ε j x ≤ 1 := by
  have hd : 0 < chartDenominator ε x :=
    lt_of_lt_of_le (by positivity : 0 < ε/2) (le_max_right _ _)
  exact ⟨div_nonneg (chartTent_nonneg _ _ _) hd.le,
    (div_le_one hd).mpr ((chartTent_le_sum ε j x).trans (le_max_left _ _))⟩

private theorem chartBoundary_bounds {ε : ℝ} (hε : 0 < ε) (x : Circle) :
    0 ≤ chartBoundary ε x ∧ chartBoundary ε x ≤ 1 := by
  have hd : 0 < chartDenominator ε x :=
    lt_of_lt_of_le (by positivity : 0 < ε/2) (le_max_right _ _)
  exact ⟨sub_nonneg.mpr ((div_le_one hd).mpr (le_max_left _ _)),
    sub_le_self _ (div_nonneg (chartTentSum_nonneg ε _) hd.le)⟩

private theorem chartPiece_lipschitz {ε : ℝ} (hε : 0 < ε) (j : Fin 3) :
    LipschitzWith (⟨8/ε, by positivity⟩ : ℝ≥0) (chartPiece ε j) := by
  convert lipschitz_div_cutoff (chartTent_lipschitz ε j) (chartDenominator_lipschitz ε)
      (show 0 < ε/2 by positivity) (chartTent_nonneg ε j)
      (fun x => (chartTent_le_sum ε j x).trans (le_max_left _ _))
      (fun _ => le_max_right _ _) using 1
  apply NNReal.eq
  push_cast
  ring

private theorem chartBoundary_lipschitz {ε : ℝ} (hε : 0 < ε) :
    LipschitzWith (⟨12/ε, by positivity⟩ : ℝ≥0) (chartBoundary ε) := by
  have h := (LipschitzWith.const (1 : ℝ)).sub
    (lipschitz_div_cutoff (chartTentSum_lipschitz ε) (chartDenominator_lipschitz ε)
      (show 0 < ε/2 by positivity) (chartTentSum_nonneg ε)
      (fun _ => le_max_left _ _) (fun _ => le_max_right _ _))
  convert h using 1
  apply NNReal.eq
  push_cast
  ring

private theorem chartBoundary_eq_zero {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1/16)
    {x : Circle} (hx : ε ≤ ‖x‖) : chartBoundary ε x = 0 := by
  have hL := chartTentSum_lower hε hε' hx
  have hp : 0 < chartTentSum ε x := (show 0 < ε/2 by positivity).trans_le hL
  simp [chartBoundary, chartDenominator, max_eq_left hL, hp.ne']

private theorem chartBoundary_integral_le {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1/16) :
    (∫ x : Circle, chartBoundary ε x ∂haarAddCircle) ≤ 2*ε := by
  let I := closedBall (0 : Circle) ε
  have hψ : Integrable (chartBoundary ε) haarAddCircle :=
    (chartBoundary_lipschitz hε).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hi : Integrable (I.indicator (fun _ => (1 : ℝ))) (haarAddCircle : Measure Circle) :=
    (integrable_const 1).indicator measurableSet_closedBall
  refine (integral_mono hψ hi ?_).trans_eq ?_
  · intro x
    by_cases hx : x ∈ I
    · rw [indicator_of_mem hx]
      exact (chartBoundary_bounds hε x).2
    · rw [indicator_of_not_mem hx]
      have hd : ε ≤ ‖x‖ := by
        have hh : ¬ ‖x‖ ≤ ε := by simpa [I, mem_closedBall] using hx
        exact le_of_lt (lt_of_not_ge hh)
      simp [chartBoundary_eq_zero hε hε' hd]
  · change (∫ x : Circle, I.indicator (1 : Circle → ℝ) x ∂haarAddCircle) = 2*ε
    rw [integral_indicator_one measurableSet_closedBall]
    have hv : (volume : Measure Circle) = haarAddCircle := by
      rw [AddCircle.volume_eq_smul_haarAddCircle]
      norm_num
    rw [← hv]
    simp only [measureReal_def, I, AddCircle.volume_closedBall]
    rw [min_eq_right (show 2*ε ≤ (1 : ℝ) by linarith), ENNReal.toReal_ofReal (by positivity)]

/-- The three chart cutoffs with the pointwise support information for the
boundary piece. The boundary vanishes on the complement of the seam ball. -/
theorem quantitativeSelectorCutoffs_with_support :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε < 1/16 →
    ∃ (pieces : Fin 3 → C(Circle, ℂ)) (lo hi : Fin 3 → ℝ) (ψ : C(Circle, ℝ)),
      (∀ j, ∃ κ : ℝ≥0, LipschitzWith κ (pieces j) ∧
        ‖pieces j‖ + (κ : ℝ) ≤ K/ε ∧ 2*(hi j-lo j) < 1 ∧
        (∀ t : ℝ, t ∈ Set.Ico (0 : ℝ) 1 → pieces j (t : Circle) ≠ 0 →
          t ∈ Set.Icc (lo j) (hi j))) ∧
      (∀ x, 0 ≤ ψ x) ∧
      (∃ κ : ℝ≥0, LipschitzWith κ ψ ∧ ‖ψ‖ + (κ : ℝ) ≤ K/ε) ∧
      (∫ x, ψ x ∂haarAddCircle) ≤ K*ε ∧
      (∀ x : Circle, (∑ j, pieces j x) + (ψ x : ℂ) = 1) ∧
      (∀ x : Circle, ε ≤ ‖x‖ → ψ x = 0) := by
  refine ⟨16, by norm_num, ?_⟩
  intro ε hε hε'
  let pieces (j : Fin 3) : C(Circle,ℂ) :=
    ⟨fun x => (chartPiece ε j x : ℂ),
      Complex.continuous_ofReal.comp (chartPiece_lipschitz hε j).continuous⟩
  let ψ : C(Circle,ℝ) := ⟨chartBoundary ε, (chartBoundary_lipschitz hε).continuous⟩
  refine ⟨pieces, fun j => chartCenter j-chartRadius ε, fun j => chartCenter j+chartRadius ε, ψ,
    ?_, fun x => (chartBoundary_bounds hε x).1, ?_, ?_, ?_, ?_⟩
  · intro j
    refine ⟨⟨8/ε, by positivity⟩, ?_, ?_, by unfold chartRadius; linarith, ?_⟩
    · simpa [pieces] using (RCLike.lipschitzWith_ofReal (K := ℂ)).comp (chartPiece_lipschitz hε j)
    · have hnorm : ‖pieces j‖ ≤ 1 := (ContinuousMap.norm_le (pieces j) (by norm_num)).mpr fun x => by
        simp only [pieces, ContinuousMap.coe_mk, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (chartPiece_bounds hε j x).1]
        exact (chartPiece_bounds hε j x).2
      exact (add_le_add_right hnorm _).trans (by
        change 1+8/ε ≤ 16/ε
        apply (le_div_iff₀ hε).mpr
        have he : 8/ε*ε = 8 := div_mul_cancel₀ _ hε.ne'
        linarith)
    · intro t ht hp
      apply chartTent_support hε j ht
      intro hz
      apply hp
      simp [pieces, chartPiece, hz]
  · refine ⟨⟨12/ε, by positivity⟩, chartBoundary_lipschitz hε, ?_⟩
    have hnorm : ‖ψ‖ ≤ 1 := (ContinuousMap.norm_le ψ (by norm_num)).mpr fun x => by
      simp only [ψ, ContinuousMap.coe_mk, Real.norm_eq_abs,
        abs_of_nonneg (chartBoundary_bounds hε x).1]
      exact (chartBoundary_bounds hε x).2
    refine (add_le_add_right hnorm _).trans ?_
    change 1+12/ε ≤ 16/ε
    apply (le_div_iff₀ hε).mpr
    have he : 12/ε*ε = 12 := div_mul_cancel₀ _ hε.ne'
    linarith
  · exact (chartBoundary_integral_le hε hε').trans (by linarith)
  · intro x
    change (∑ j : Fin 3, (chartPiece ε j x : ℂ)) + (chartBoundary ε x : ℂ) = 1
    simp only [← Complex.ofReal_sum, ← Complex.ofReal_add, ← Complex.ofReal_one]
    apply congrArg Complex.ofReal
    simp only [chartBoundary, chartPiece, ← Finset.sum_div, chartTentSum]
    ring
  · exact fun _ hx => chartBoundary_eq_zero hε hε' hx

/-- Three explicit chart cutoffs with a boundary mass at most twice the
cutoff scale. The common denominator is clipped below by half that scale. -/
theorem quantitativeSelectorCutoffs : QuantitativeSelectorCutoffs := by
  obtain ⟨K, hK, hCut⟩ := quantitativeSelectorCutoffs_with_support
  refine ⟨K, hK, fun ε hε hε' => ?_⟩
  obtain ⟨pieces, lo, hi, ψ, hPiece, hψ, hψLip, hInt, hSum, _⟩ := hCut ε hε hε'
  exact ⟨pieces, lo, hi, ψ, hPiece, hψ, hψLip, hInt, hSum⟩

end NilBohr
