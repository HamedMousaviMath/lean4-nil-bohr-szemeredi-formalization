import NilBohr.GreenTaoHaarAmbient
import NilBohr.GreenTaoProductTopology

/-! The normalized measure and unit-chart integral on the product with the unit circle. -/

open MeasureTheory Set
open scoped Interval

namespace NilBohr

/-- The quotient measure in product coordinates is the product of the two
normalized factors. -/
noncomputable def heisenbergCircleMeasure : Measure (HeisenbergNilmanifold × Circle) :=
  heisenbergNilmanifoldMeasure.prod AddCircle.haarAddCircle

instance : IsProbabilityMeasure heisenbergCircleMeasure := by
  unfold heisenbergCircleMeasure
  infer_instance

/-- The product probability is preserved by the coordinatewise left action. -/
theorem heisenbergCircleMeasure_leftInvariant (a : HeisenbergGroup) (c : Circle) :
    MeasurePreserving (fun q : HeisenbergNilmanifold × Circle => (a • q.1, c + q.2))
      heisenbergCircleMeasure heisenbergCircleMeasure :=
  (heisenbergNilmanifoldMeasure_leftInvariant a).prod
    (measurePreserving_add_left AddCircle.haarAddCircle c)

theorem measurePreserving_circle_unitChart :
    MeasurePreserving ((↑) : ℝ → Circle) unitChartIntervalMeasure AddCircle.haarAddCircle := by
  have h : (volume : Measure Circle) = AddCircle.haarAddCircle := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    simp
  simpa only [unitChartIntervalMeasure, h, zero_add] using UnitAddCircle.measurePreserving_mk 0

/-- Projection from the four real chart coordinates onto the two quotient factors. -/
def heisenbergCircleChartProjection (p : HeisenbergPoint × ℝ) : HeisenbergNilmanifold × Circle :=
  (heisenbergQuotientProjection p.1, (p.2 : Circle))

theorem measurePreserving_heisenbergCircleChartProjection :
    MeasurePreserving heisenbergCircleChartProjection
      (heisenbergCubeMeasure.prod unitChartIntervalMeasure) heisenbergCircleMeasure :=
  (show MeasurePreserving heisenbergQuotientProjection heisenbergCubeMeasure
    heisenbergNilmanifoldMeasure from ⟨continuous_heisenbergQuotientProjection.measurable, rfl⟩).prod
      measurePreserving_circle_unitChart

/-- The iterated four-dimensional chart functional is the integral against cube Lebesgue. -/
theorem integral_heisenbergProductCubeMeasure {Ψ : HeisenbergPoint × ℝ → ℂ}
    (hΨ : Integrable Ψ (heisenbergCubeMeasure.prod unitChartIntervalMeasure)) :
    (∫ p, Ψ p ∂heisenbergCubeMeasure.prod unitChartIntervalMeasure) =
      heisenbergProductChartMean Ψ := by
  rw [integral_prod Ψ hΨ, heisenbergProductChartMean]
  simp only [intervalIntegral.integral_of_le zero_le_one]
  exact integral_heisenbergCubeMeasure hΨ.integral_prod_left

/-- The normalized product probability gives exactly the iterated unit-chart
functional on every integrable observable. -/
theorem integral_heisenbergCircleMeasure {Φ : HeisenbergNilmanifold × Circle → ℂ}
    (hΦ : Integrable Φ heisenbergCircleMeasure) :
    (∫ q, Φ q ∂heisenbergCircleMeasure) =
      heisenbergProductChartMean (Φ ∘ heisenbergCircleChartProjection) := by
  let hπ := measurePreserving_heisenbergCircleChartProjection
  rw [← hπ.map_eq, integral_map hπ.measurable.aemeasurable]
  · exact integral_heisenbergProductCubeMeasure ((hπ.integrable_comp hΦ.aestronglyMeasurable).mpr hΦ)
  · rw [hπ.map_eq]
    exact hΦ.aestronglyMeasurable

instance : MeasurableSpace HeisenbergProductNilmanifold := borel _

instance : BorelSpace HeisenbergProductNilmanifold := ⟨rfl⟩

/-- The product Haar probability on the actual right-coset quotient. -/
noncomputable def heisenbergProductNilmanifoldMeasure : Measure HeisenbergProductNilmanifold :=
  Measure.map heisenbergProductNilmanifoldHomeomorph.symm heisenbergCircleMeasure

instance : IsProbabilityMeasure heisenbergProductNilmanifoldMeasure :=
  isProbabilityMeasure_map heisenbergProductNilmanifoldHomeomorph.symm.continuous.measurable.aemeasurable

theorem heisenbergProductNilmanifoldHomeomorph_smul (a : HeisenbergProductGroup)
    (q : HeisenbergProductNilmanifold) :
    heisenbergProductNilmanifoldHomeomorph (a • q) =
      (a.1 • (heisenbergProductNilmanifoldHomeomorph q).1,
        ((Multiplicative.toAdd a.2 : ℝ) : Circle) + (heisenbergProductNilmanifoldHomeomorph q).2) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  change heisenbergProductNilmanifoldHomeomorph (QuotientGroup.mk (a * g)) = _
  simp only [heisenbergProductNilmanifoldHomeomorph_apply_mk]
  congr 1

theorem heisenbergProductNilmanifoldMeasure_leftInvariant (a : HeisenbergProductGroup) :
    MeasurePreserving (fun q : HeisenbergProductNilmanifold => a • q)
      heisenbergProductNilmanifoldMeasure heisenbergProductNilmanifoldMeasure := by
  let e := heisenbergProductNilmanifoldHomeomorph
  let L : HeisenbergNilmanifold × Circle → HeisenbergNilmanifold × Circle :=
    fun q => (a.1 • q.1, ((Multiplicative.toAdd a.2 : ℝ) : Circle) + q.2)
  have hL : MeasurePreserving L heisenbergCircleMeasure heisenbergCircleMeasure :=
    heisenbergCircleMeasure_leftInvariant a.1 ((Multiplicative.toAdd a.2 : ℝ) : Circle)
  have hcomm : (fun q : HeisenbergProductNilmanifold => a • q) ∘ e.symm = e.symm ∘ L := by
    funext q
    apply e.injective
    change e (a • e.symm q) = e (e.symm (L q))
    rw [e.apply_symm_apply]
    have h := heisenbergProductNilmanifoldHomeomorph_smul a (e.symm q)
    change e (a • e.symm q) =
      (a.1 • (e (e.symm q)).1, ((Multiplicative.toAdd a.2 : ℝ) : Circle) + (e (e.symm q)).2) at h
    rw [e.apply_symm_apply] at h
    exact h
  have hmeas : Measurable (fun q : HeisenbergProductNilmanifold => a • q) :=
    (continuous_const_smul a).measurable
  refine ⟨hmeas, ?_⟩
  rw [heisenbergProductNilmanifoldMeasure, Measure.map_map hmeas e.symm.continuous.measurable,
    hcomm, ← Measure.map_map e.symm.continuous.measurable hL.measurable, hL.map_eq]

/-- The four real chart coordinates projected to the actual product quotient. -/
def heisenbergProductQuotientProjection (p : HeisenbergPoint × ℝ) :
    HeisenbergProductNilmanifold :=
  QuotientGroup.mk (HeisenbergGroup.coordinates.symm p.1, Multiplicative.ofAdd p.2)

theorem measurePreserving_heisenbergProductQuotientProjection :
    MeasurePreserving heisenbergProductQuotientProjection
      (heisenbergCubeMeasure.prod unitChartIntervalMeasure) heisenbergProductNilmanifoldMeasure := by
  let e := heisenbergProductNilmanifoldHomeomorph
  have hπ : heisenbergProductQuotientProjection = e.symm ∘ heisenbergCircleChartProjection := by
    funext p
    apply e.injective
    simp [e, heisenbergProductQuotientProjection, heisenbergCircleChartProjection,
      heisenbergQuotientProjection]
  rw [hπ]
  exact (show MeasurePreserving e.symm heisenbergCircleMeasure
    heisenbergProductNilmanifoldMeasure from ⟨e.symm.continuous.measurable, rfl⟩).comp
      measurePreserving_heisenbergCircleChartProjection

/-- Integration against the normalized product-quotient probability agrees
with the manuscript's iterated chart integral. -/
theorem integral_heisenbergProductNilmanifoldMeasure {Φ : HeisenbergProductNilmanifold → ℂ}
    (hΦ : Integrable Φ heisenbergProductNilmanifoldMeasure) :
    (∫ q, Φ q ∂heisenbergProductNilmanifoldMeasure) =
      heisenbergProductChartMean (Φ ∘ heisenbergProductQuotientProjection) := by
  let hπ := measurePreserving_heisenbergProductQuotientProjection
  rw [← hπ.map_eq, integral_map hπ.measurable.aemeasurable]
  · exact integral_heisenbergProductCubeMeasure ((hπ.integrable_comp hΦ.aestronglyMeasurable).mpr hΦ)
  · rw [hπ.map_eq]
    exact hΦ.aestronglyMeasurable

theorem integral_heisenbergProductNilmanifoldMeasure_continuous
    (Φ : HeisenbergProductNilmanifold → ℂ) (hΦ : Continuous Φ) :
    (∫ q, Φ q ∂heisenbergProductNilmanifoldMeasure) =
      heisenbergProductChartMean (Φ ∘ heisenbergProductQuotientProjection) :=
  integral_heisenbergProductNilmanifoldMeasure (hΦ.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace Φ))

end NilBohr
