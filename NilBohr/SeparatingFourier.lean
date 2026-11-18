import NilBohr.Rotations

/-! Fourier facts for the two lower bounds in Appendix A. -/

open AddCircle Filter MeasureTheory
open scoped Topology BigOperators

namespace NilBohr

/-- A nonconstant continuous circle function has a nonzero Fourier
coefficient at a nonzero index. -/
theorem exists_nonzero_fourierCoeff_of_nonconstant
    (F : C(Circle, ℂ)) (hF : ∃ x y : Circle, F x ≠ F y) :
    ∃ h : ℤ, h ≠ 0 ∧ fourierCoeff F h ≠ 0 := by
  by_contra! hz
  have hSum := hasSum_fourier_series_of_summable
    (hasSum_single (f := fun h : ℤ => fourierCoeff F h) 0 hz).summable
  have hconst : HasSum (fun h : ℤ => fourierCoeff F h • fourier (T := 1) h)
      (fourierCoeff F 0 • fourier (T := 1) 0) := by
    exact hasSum_single 0 fun h hh => by
      rw [hz h hh]
      ext x
      simp [ContinuousMap.smul_apply]
  have hEq := hSum.unique hconst
  obtain ⟨x, y, hxy⟩ := hF
  apply hxy
  rw [hEq]
  simp [fourier_zero]

/-- Centering the selector preserves its nonzero Fourier coefficients. -/
theorem circleMean_centered_mul_fourier (F : C(Circle, ℂ)) {h : ℤ} (hh : h ≠ 0) :
    circleMean (fun x => (F x - circleMean F) * fourier (T := 1) (-h) x) =
      fourierCoeff F h := by
  let u : Circle → ℂ := fun x => F x * fourier (T := 1) (-h) x
  let v : Circle → ℂ := fun x => circleMean F * fourier (T := 1) (-h) x
  have hu : Continuous u := F.continuous.mul (fourier (T := 1) (-h)).continuous
  have hv : Continuous v := continuous_const.mul (fourier (T := 1) (-h)).continuous
  have hzero : circleMean (fourier (T := 1) (-h)) = 0 :=
    circleMean_fourier_eq_zero (neg_ne_zero.mpr hh)
  have hvzero : circleMean v = 0 := by
    change (∫ x, circleMean F * fourier (T := 1) (-h) x ∂haarAddCircle) = 0
    rw [integral_const_mul, ← circleMean, hzero, mul_zero]
  rw [show (fun x => (F x - circleMean F) * fourier (T := 1) (-h) x) =
    (fun x => u x - v x) by ext x; exact sub_mul _ _ _, circleMean,
    integral_sub (hu.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (hv.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  change circleMean u - circleMean v = _
  rw [hvzero, sub_zero]
  simp only [circleMean, u, fourierCoeff, smul_eq_mul, mul_comm]

private theorem integrable_continuous_circle (F : C(Circle, ℂ)) :
    Integrable F haarAddCircle :=
  F.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

private noncomputable def centeredCircleAverage (H : ℕ) (x : ℕ → Circle) :
    C(Circle, ℂ) →ₗ[ℂ] ℂ where
  toFun F := (∑ n ∈ Finset.range H, F (x n)) / (H : ℂ) - circleMean F
  map_add' F G := by
    have hmean : circleMean (F + G : C(Circle, ℂ)) = circleMean F + circleMean G :=
      integral_add (integrable_continuous_circle F) (integrable_continuous_circle G)
    simp only [ContinuousMap.add_apply, Finset.sum_add_distrib, hmean, add_div]
    ring
  map_smul' c F := by
    have hmean : circleMean (c • F : C(Circle, ℂ)) = c * circleMean F := integral_const_mul c F
    simp only [ContinuousMap.smul_apply, smul_eq_mul, hmean, RingHom.id_apply,
      ← Finset.mul_sum, mul_div_assoc, mul_sub]

private theorem norm_centeredCircleAverage_le (H : ℕ) (x : ℕ → Circle) (F : C(Circle, ℂ)) :
    ‖centeredCircleAverage H x F‖ ≤ 2 * ‖F‖ := by
  have hmean : ‖circleMean F‖ ≤ ‖F‖ := by
    have h := norm_integral_le_of_norm_le_const (μ := (haarAddCircle : Measure Circle))
      (Eventually.of_forall F.norm_coe_le_norm)
    simpa [circleMean, measureReal_univ_eq_one] using h
  have havg : ‖(∑ n ∈ Finset.range H, F (x n)) / (H : ℂ)‖ ≤ ‖F‖ := by
    by_cases hH : H = 0
    · subst H
      simp
    have hpos : 0 < (H : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hH
    rw [norm_div, Complex.norm_natCast, div_le_iff₀ hpos]
    calc
      _ ≤ ∑ n ∈ Finset.range H, ‖F (x n)‖ := norm_sum_le _ _
      _ ≤ ∑ _ ∈ Finset.range H, ‖F‖ :=
        Finset.sum_le_sum fun n _ => F.norm_coe_le_norm (x n)
      _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]
  change ‖(∑ n ∈ Finset.range H, F (x n)) / (H : ℂ) - circleMean F‖ ≤ _
  simpa only [two_mul] using (norm_sub_le _ _).trans (add_le_add havg hmean)

/-- Weyl's criterion for finite rows on the unit circle. The row lengths
may vary, and the tests on each row are normalized by its own length. -/
theorem tendsto_circle_average_of_fourier
    (H : ℕ → ℕ) (x : ℕ → ℕ → Circle) (hH : Tendsto H atTop atTop)
    (hModes : ∀ k : ℤ, k ≠ 0 →
      Tendsto (fun j => (∑ n ∈ Finset.range (H j), fourier (T := 1) k (x j n)) /
        (H j : ℂ)) atTop (𝓝 0)) (F : C(Circle, ℂ)) :
    Tendsto (fun j => (∑ n ∈ Finset.range (H j), F (x j n)) / (H j : ℂ)) atTop
      (𝓝 (circleMean F)) := by
  let L (j : ℕ) := centeredCircleAverage (H j) (x j)
  let span := Submodule.span ℂ (Set.range (fourier (T := 1)))
  have htrig (G : C(Circle, ℂ)) (hG : G ∈ span) :
      Tendsto (fun j => L j G) atTop (𝓝 0) := by
    induction hG using Submodule.span_induction with
    | mem G hG =>
      obtain ⟨k, rfl⟩ := hG
      by_cases hk : k = 0
      · subst k
        apply tendsto_const_nhds.congr'
        filter_upwards [hH.eventually_gt_atTop 0] with j hj
        have hcast : (H j : ℂ) ≠ 0 := by exact_mod_cast hj.ne'
        have h_one : (fourier (T := 1) 0 : Circle → ℂ) = fun _ => 1 :=
          funext fun _ => fourier_zero
        simp [L, centeredCircleAverage, h_one, circleMean, measureReal_univ_eq_one, hcast]
      · simpa [L, centeredCircleAverage, circleMean_fourier_eq_zero hk] using hModes k hk
    | zero =>
      simpa only [map_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
    | add F G _ _ hF hG => simpa only [map_add, zero_add] using hF.add hG
    | smul c F _ hF => simpa only [map_smul, smul_eq_mul, mul_zero] using hF.const_mul c
  have hdense : F ∈ closure (span : Set C(Circle, ℂ)) := by
    change F ∈ span.topologicalClosure
    rw [show span.topologicalClosure = ⊤ from span_fourier_closure_eq_top]
    trivial
  have hlim : Tendsto (fun j => L j F) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨G, hG, hclose⟩ := Metric.mem_closure_iff.mp hdense (ε / 4) (by positivity)
    obtain ⟨j₀, hj₀⟩ := Metric.tendsto_atTop.mp (htrig G hG) (ε / 2) (by positivity)
    refine ⟨j₀, fun j hj => ?_⟩
    rw [dist_zero_right]
    have hc : ‖F - G‖ < ε / 4 := by
      rw [← dist_eq_norm]
      exact hclose
    have hg : ‖L j G‖ < ε / 2 := by simpa only [dist_zero_right] using hj₀ j hj
    calc
      ‖L j F‖ = ‖L j (F - G) + L j G‖ := by rw [← map_add, sub_add_cancel]
      _ ≤ ‖L j (F - G)‖ + ‖L j G‖ := norm_add_le _ _
      _ ≤ 2 * ‖F - G‖ + ‖L j G‖ :=
        add_le_add_right (norm_centeredCircleAverage_le _ _ _) _
      _ < ε := by linarith only [hc, hg]
  simpa [L, centeredCircleAverage] using hlim.add
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => circleMean F) atTop (𝓝 (circleMean F)))

end NilBohr
