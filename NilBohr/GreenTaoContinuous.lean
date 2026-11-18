import NilBohr.GreenTaoHaarQuotient

/-! The tests in the specialized Green–Tao interface descend to continuous
tests on the ordinary coset quotient. -/

open MeasureTheory

namespace NilBohr

private noncomputable def heisenbergChainCost (x : ℕ → HeisenbergPoint) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n,
      min (heisenbergMalcevNorm (heisenbergMul (x i) (heisenbergInv (x (i+1)))))
          (heisenbergMalcevNorm (heisenbergMul (x (i+1)) (heisenbergInv (x i))))

private theorem heisenberg_chain_cost_nonneg (x : ℕ → HeisenbergPoint) (n : ℕ) :
    0 ≤ heisenbergChainCost x n := by
  apply Finset.sum_nonneg
  intro i hi
  unfold heisenbergMalcevNorm
  positivity

private theorem heisenbergGroupDistance_nonneg' (g h : HeisenbergPoint) :
    0 ≤ heisenbergGroupDistance g h := by
  apply Real.sInf_nonneg
  rintro d ⟨n, x, _, _, rfl⟩
  exact heisenberg_chain_cost_nonneg x n

private theorem heisenbergGroupDistance_le_relative' (g h : HeisenbergPoint) :
    heisenbergGroupDistance g h ≤ heisenbergMalcevNorm (heisenbergMul g (heisenbergInv h)) := by
  let x : ℕ → HeisenbergPoint := fun i => if i = 0 then g else h
  calc
    heisenbergGroupDistance g h ≤ heisenbergChainCost x 1 := by
      unfold heisenbergGroupDistance
      refine csInf_le ?_ ⟨1, x, by simp [x], by simp [x], rfl⟩
      refine ⟨0, ?_⟩
      rintro d ⟨n, t, _, _, rfl⟩
      exact heisenberg_chain_cost_nonneg t n
    _ ≤ _ := by simp [heisenbergChainCost, x]

/-- The quotient distance is bounded above by the direct coordinate
cost between the two representatives. -/
theorem heisenbergQuotientDistance_le_relative (g h : HeisenbergPoint) :
    heisenbergQuotientDistance g h ≤ heisenbergMalcevNorm (heisenbergMul g (heisenbergInv h)) := by
  calc
    heisenbergQuotientDistance g h ≤ heisenbergGroupDistance g (heisenbergMul h (0, 0, 0)) := by
      unfold heisenbergQuotientDistance
      refine csInf_le ?_ ⟨0, 0, 0, by simp⟩
      refine ⟨0, ?_⟩
      rintro d ⟨u, v, w, rfl⟩
      exact heisenbergGroupDistance_nonneg' _ _
    _ ≤ _ := by simpa [heisenbergMul] using heisenbergGroupDistance_le_relative' g h

/-- A test controlled by the quotient Lipschitz bound is continuous in
matrix coordinates. The single-edge bound suffices for this implication. -/
theorem continuous_of_heisenbergLipschitzNormLE {Φ : HeisenbergPoint → ℂ} {U : ℝ}
    (hΦ : HeisenbergLipschitzNormLE Φ U) : Continuous Φ := by
  obtain ⟨_, S, M, _, hM, _, _, hBound⟩ := hΦ
  refine continuous_iff_continuousAt.mpr fun x => ?_
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  refine squeeze_zero (fun t => norm_nonneg _) (fun t => (hBound t x).trans
    (mul_le_mul_of_nonneg_left (heisenbergQuotientDistance_le_relative t x) hM)) ?_
  have hcont : Continuous (fun t : HeisenbergPoint =>
      M * heisenbergMalcevNorm (heisenbergMul t (heisenbergInv x))) := by
    unfold heisenbergMalcevNorm heisenbergMul
    fun_prop
  have heq : heisenbergMul x (heisenbergInv x) = (0, 0, 0) := by
    rcases x with ⟨x, y, z⟩
    simp [heisenbergMul, heisenbergInv]
  simpa only [ContinuousAt, heq, heisenbergMalcevNorm, abs_zero, mul_zero, sub_zero, max_self]
    using hcont.continuousAt (x := x)

/-- The descended observable for the chart test in the obstruction
interface. Lattice invariance makes it independent of representatives. -/
def heisenbergLipschitzTest (Φ : HeisenbergPoint → ℂ) {U : ℝ}
    (hΦ : HeisenbergLipschitzNormLE Φ U) : HeisenbergNilmanifold → ℂ :=
  Quotient.lift (Φ ∘ HeisenbergGroup.coordinates) (fun g h hg => by
    have hgh : g⁻¹ * h ∈ HeisenbergGroup.lattice := QuotientGroup.leftRel_apply.mp hg
    obtain ⟨u, v, w, hint⟩ := hgh
    have hh : h = g * (⟨u, v, w⟩ : HeisenbergGroup) := by
      rw [← hint, mul_inv_cancel_left]
    change Φ (HeisenbergGroup.coordinates g) = Φ (HeisenbergGroup.coordinates h)
    rw [hh, HeisenbergGroup.coordinates_mul]
    exact (hΦ.1 (HeisenbergGroup.coordinates g) u v w).symm)


@[simp] theorem heisenbergLipschitzTest_projection (Φ : HeisenbergPoint → ℂ) {U : ℝ}
    (hΦ : HeisenbergLipschitzNormLE Φ U) (g : HeisenbergPoint) :
    heisenbergLipschitzTest Φ hΦ (heisenbergQuotientProjection g) = Φ g := by
  change Φ (HeisenbergGroup.coordinates (HeisenbergGroup.coordinates.symm g)) = Φ g
  rw [Equiv.apply_symm_apply]

theorem continuous_heisenbergLipschitzTest (Φ : HeisenbergPoint → ℂ) {U : ℝ}
    (hΦ : HeisenbergLipschitzNormLE Φ U) : Continuous (heisenbergLipschitzTest Φ hΦ) :=
  (QuotientGroup.isQuotientMap_mk HeisenbergGroup.lattice).continuous_iff.mpr
    ((continuous_of_heisenbergLipschitzNormLE hΦ).comp HeisenbergGroup.continuous_coordinates)

/-- The Haar integral of the descended observable agrees with the chart
mean used in the specialized obstruction. -/
theorem integral_heisenbergLipschitzTest (Φ : HeisenbergPoint → ℂ) {U : ℝ}
    (hΦ : HeisenbergLipschitzNormLE Φ U) :
    (∫ q, heisenbergLipschitzTest Φ hΦ q ∂heisenbergNilmanifoldMeasure) =
      heisenbergChartMean Φ := by
  rw [integral_heisenbergNilmanifoldMeasure_continuous _ (continuous_heisenbergLipschitzTest Φ hΦ)]
  apply congrArg heisenbergChartMean
  funext g
  exact heisenbergLipschitzTest_projection Φ hΦ g

end NilBohr
