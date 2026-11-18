import NilBohr.OrbitEquidistribution
import Mathlib.Topology.ContinuousMap.Compact

open Filter AddCircle MeasureTheory
open scoped BigOperators Topology NNReal

namespace NilBohr

/-- The scalar part of Proposition 4.3 restricted to functions of the second
horizontal coordinate. The Lipschitz dependence is homogeneous, as in the
quantitative scalar obstruction estimate. -/
def HorizontalCircleEstimate (β : ℝ) (r : ℕ → ℕ) : Prop :=
  ∀ D : ℝ, 0 < D → ∃ L : ℝ, 0 < L ∧ ∀ᶠ X : ℝ in atTop,
    ∀ j : ℕ, (r j : ℝ) ≤ X^(1/100 : ℝ) → X^(1/100 : ℝ) < (r (j+1) : ℝ) →
    ∀ (a : ℤ) (v K : ℕ), 0 < v → (v : ℝ) ≤ X^(1/10000 : ℝ) → ¬ r j ∣ v →
      X^(1/2 : ℝ) ≤ (K : ℝ) → ∀ (ψ : C(Circle, ℝ)) (κ : ℝ≥0), LipschitzWith κ ψ →
      |(∑ t ∈ positiveInterval K, ψ ((β*((a+(v:ℤ)*t : ℤ):ℝ) : ℝ) : Circle))/(K:ℝ) -
        ∫ t, ψ t ∂haarAddCircle| ≤ L * (Real.log X)^(-D) * (‖ψ‖ + (κ : ℝ))

private theorem heisenbergGroupDistance_y (g h : HeisenbergPoint) :
    |g.2.1-h.2.1| ≤ heisenbergGroupDistance g h := by
  unfold heisenbergGroupDistance
  apply le_csInf
  · exact ⟨_, 1, (fun i => if i = 0 then g else h), by simp, by simp, rfl⟩
  rintro d ⟨n, x, hx₀, hxn, rfl⟩
  rw [← hx₀, ← hxn, abs_sub_comm, ← Finset.sum_range_sub (fun i => (x i).2.1) n]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  apply le_min
  · rw [abs_sub_comm]
    exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_left _ _).trans (le_max_right _ _)

/-- The second horizontal coordinate of the lattice quotient is
1-Lipschitz for the Mal'cev chain metric. -/
theorem heisenberg_horizontalCircle_dist_le (g h : HeisenbergPoint) :
    dist (g.2.1 : Circle) (h.2.1 : Circle) ≤ heisenbergQuotientDistance g h := by
  unfold heisenbergQuotientDistance
  apply le_csInf
  · exact ⟨_, 0, 0, 0, rfl⟩
  rintro _ ⟨u, v, w, rfl⟩
  let h' := heisenbergMul h ((u : ℝ), (v : ℝ), (w : ℝ))
  have hcast : (h'.2.1 : Circle) = (h.2.1 : Circle) := by
    have hv : ((v:ℝ):Circle) = 0 := (AddCircle.coe_eq_zero_iff (1:ℝ)).mpr ⟨v, by simp⟩
    simp [h', heisenbergMul, AddCircle.coe_add, hv]
  rw [← hcast, dist_eq_norm, ← AddCircle.coe_sub]
  exact (torusNorm_le_abs _).trans (heisenbergGroupDistance_y g h')

/-- Pulling a real circle test back along the second horizontal coordinate
preserves the supremum plus Lipschitz bound. -/
theorem horizontalCircle_lipschitzNorm {κ : ℝ≥0} (ψ : C(Circle, ℝ))
    (hψ : LipschitzWith κ ψ) :
    HeisenbergLipschitzNormLE (fun g => (ψ (g.2.1 : Circle) : ℂ)) (‖ψ‖ + (κ : ℝ)) := by
  refine ⟨?_, ‖ψ‖, (κ : ℝ), norm_nonneg _, NNReal.coe_nonneg _, le_rfl, ?_, ?_⟩
  · intro g u v w
    have hv : ((v:ℝ):Circle) = 0 := (AddCircle.coe_eq_zero_iff (1:ℝ)).mpr ⟨v, by simp⟩
    simp [heisenbergMul, AddCircle.coe_add, hv]
  · intro g
    simpa only [Complex.norm_real] using ψ.norm_coe_le_norm (g.2.1 : Circle)
  · intro g h
    rw [← Complex.ofReal_sub, Complex.norm_real, ← dist_eq_norm]
    exact ((LipschitzWith.dist_le_mul hψ _ _)).trans
      (mul_le_mul_of_nonneg_left (heisenberg_horizontalCircle_dist_le g h) (NNReal.coe_nonneg _))

/-- The unit-chart average agrees exactly with normalized circle Haar
measure for functions of the second horizontal coordinate. -/
theorem horizontalCircle_chartMean (ψ : C(Circle, ℝ)) :
    heisenbergChartMean (fun g => (ψ (g.2.1 : Circle) : ℂ)) =
      (((∫ x, ψ x ∂haarAddCircle) : ℝ) : ℂ) := by
  unfold heisenbergChartMean
  simp only [intervalIntegral.integral_const, sub_zero, one_smul]
  have h := AddCircle.intervalIntegral_preimage (1:ℝ) 0 (fun x : Circle => (ψ x : ℂ))
  rw [AddCircle.volume_eq_smul_haarAddCircle] at h
  simp only [zero_add, ENNReal.ofReal_one, one_smul] at h
  rw [h]
  exact Complex.ofRealLI.integral_comp_comm (μ := (haarAddCircle : Measure Circle)) (fun x => ψ x)

/-- The scalar Green–Tao criterion and the manuscript's horizontal estimate
supply the circle aperture bound on the same chosen prime sequence. -/
theorem horizontalCircleEstimate_of_scalar (hGT : ScalarHeisenbergObstruction)
    (α β : ℝ) (hα : BadlyApproximable α) {r : ℕ → ℕ} (hr : AdmissibleBetaDenominators β r) :
    HorizontalCircleEstimate β r := by
  intro D hD
  refine ⟨1, one_pos, ?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℝ),
    scalar_heisenberg_equidistribution_for_denominators hGT α β hα hr D 0 hD]
    with X hX hs
  intro j hjlo hjhi a v K hv hvX hcop hK ψ κ hψ
  have hXone : 1 ≤ X := by linarith
  have hvbig := hvX.trans (Real.rpow_le_rpow_of_exponent_le hXone (by norm_num : (1/10000:ℝ) ≤ 1/5000))
  have hKbig := (Real.rpow_le_rpow_of_exponent_le hXone (by norm_num : (1/3:ℝ) ≤ 1/2)).trans hK
  have h := hs j hjlo hjhi a v 1 K hv hvbig hcop (by decide) (by simp) hKbig _ _
    (horizontalCircle_lipschitzNorm ψ hψ)
  rw [horizontalCircle_chartMean] at h
  have hAverage : heisenbergOrbitAverage α β a v 1 K (fun g => (ψ (g.2.1 : Circle) : ℂ)) =
      (((∑ t ∈ positiveInterval K,
        ψ ((β*((a+(v:ℤ)*t : ℤ):ℝ) : ℝ) : Circle))/(K:ℝ) : ℝ) : ℂ) := by
    push_cast
    simp [heisenbergOrbitAverage, dilatedHeisenbergOrbit, heisenbergOrbit, mul_comm]
  rw [hAverage, ← Complex.ofReal_sub, Complex.norm_real] at h
  simpa only [one_mul, Real.norm_eq_abs] using h

end NilBohr
