import NilBohr.GreenTaoModel

/-! Cube integration for the normalized Heisenberg quotient measure.

This file isolates the measure-theoretic steps from the topology of the
quotient. A measurable quotient projection invariant under integer right
translations can be supplied to the pushforward construction below.
-/

open Set Filter MeasureTheory
open scoped Interval ENNReal

namespace NilBohr

noncomputable def unitChartIntervalMeasure : Measure ℝ :=
  volume.restrict (Ioc (0 : ℝ) 1)

instance : IsProbabilityMeasure unitChartIntervalMeasure := by
  constructor
  simp [unitChartIntervalMeasure, Real.volume_Ioc]

/-- Lebesgue probability measure on the unit coordinate cube. -/
noncomputable def heisenbergCubeMeasure : Measure HeisenbergPoint :=
  unitChartIntervalMeasure.prod (unitChartIntervalMeasure.prod unitChartIntervalMeasure)

instance : IsProbabilityMeasure heisenbergCubeMeasure := by
  unfold heisenbergCubeMeasure
  infer_instance

theorem heisenbergCubeMeasure_eq :
    heisenbergCubeMeasure =
      volume.restrict (Ioc (0 : ℝ) 1 ×ˢ (Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1)) := by
  rw [heisenbergCubeMeasure, unitChartIntervalMeasure, Measure.prod_restrict, Measure.prod_restrict]
  rfl

/-- The iterated chart functional is the ordinary cube integral. -/
theorem integral_heisenbergCubeMeasure {Φ : HeisenbergPoint → ℂ}
    (hΦ : Integrable Φ heisenbergCubeMeasure) :
    (∫ p, Φ p ∂heisenbergCubeMeasure) = heisenbergChartMean Φ := by
  unfold heisenbergCubeMeasure at hΦ ⊢
  rw [integral_prod Φ hΦ]
  simp only [heisenbergChartMean, intervalIntegral.integral_of_le zero_le_one]
  change (∫ x, ∫ yz, Φ (x, yz) ∂unitChartIntervalMeasure.prod unitChartIntervalMeasure
      ∂unitChartIntervalMeasure) =
    ∫ x, ∫ y, ∫ z, Φ (x, y, z) ∂unitChartIntervalMeasure ∂unitChartIntervalMeasure
      ∂unitChartIntervalMeasure
  apply integral_congr_ae
  filter_upwards [hΦ.prod_right_ae] with x hx
  exact integral_prod (fun yz => Φ (x, yz)) hx

/-- The cube measure pushed forward by a quotient projection. -/
noncomputable def heisenbergChartPushforward {Q : Type*} [MeasurableSpace Q]
    (π : HeisenbergPoint → Q) : Measure Q :=
  Measure.map π heisenbergCubeMeasure

theorem isProbabilityMeasure_heisenbergChartPushforward {Q : Type*} [MeasurableSpace Q]
    {π : HeisenbergPoint → Q} (hπ : Measurable π) :
    IsProbabilityMeasure (heisenbergChartPushforward π) :=
  isProbabilityMeasure_map hπ.aemeasurable

/-- Integrating an integrable quotient test gives exactly its chart mean. -/
theorem integral_heisenbergChartPushforward {Q : Type*} [MeasurableSpace Q]
    {π : HeisenbergPoint → Q} (hπ : Measurable π) {Φ : Q → ℂ}
    (hΦ : Integrable Φ (heisenbergChartPushforward π)) :
    (∫ q, Φ q ∂heisenbergChartPushforward π) = heisenbergChartMean (Φ ∘ π) :=
  (integral_map hπ.aemeasurable hΦ.aestronglyMeasurable).trans
    (integral_heisenbergCubeMeasure (hΦ.comp_measurable hπ))

/-- The probability obtained from the cube is invariant under the induced
left translations. This is measure equality on all measurable sets,
proved by applying chart invariance to indicators. -/
theorem heisenbergChartPushforward_leftInvariant {Q : Type*} [MeasurableSpace Q]
    {π : HeisenbergPoint → Q} (hπ : Measurable π)
    (hq : ∀ g (u v w : ℤ), π (heisenbergMul g ((u : ℝ), (v : ℝ), (w : ℝ))) = π g)
    (a : HeisenbergPoint) {L : Q → Q} (hL : Measurable L)
    (hleft : ∀ g, L (π g) = π (heisenbergMul a g)) :
    Measure.map L (heisenbergChartPushforward π) = heisenbergChartPushforward π := by
  classical
  ext s hs
  have hst := hL hs
  have hpre := hπ hs
  have hpreL := hπ hst
  rw [Measure.map_apply hL hs, heisenbergChartPushforward, Measure.map_apply hπ hst,
    Measure.map_apply hπ hs]
  let f : HeisenbergPoint → ℂ := (π ⁻¹' s).indicator (fun _ => 1)
  let fL : HeisenbergPoint → ℂ := (π ⁻¹' (L ⁻¹' s)).indicator (fun _ => 1)
  have hInv : ∀ g (u v w : ℤ), f (heisenbergMul g ((u : ℝ), (v : ℝ), (w : ℝ))) = f g := by
    intro g u v w
    simp only [f, indicator_apply, mem_preimage, hq g u v w]
  have hcomp : (fun g => f (heisenbergMul a g)) = fL := by
    ext g
    simp only [f, fL, indicator_apply, mem_preimage, hleft g]
  have hchart : heisenbergChartMean fL = heisenbergChartMean f := by
    rw [← hcomp]
    exact heisenbergChartMean_leftInvariant f hInv a
  have hf : Integrable f heisenbergCubeMeasure := (integrable_const _).indicator hpre
  have hfL : Integrable fL heisenbergCubeMeasure := (integrable_const _).indicator hpreL
  have heq : (∫ p, fL p ∂heisenbergCubeMeasure) = ∫ p, f p ∂heisenbergCubeMeasure :=
    (integral_heisenbergCubeMeasure hfL).trans (hchart.trans (integral_heisenbergCubeMeasure hf).symm)
  simp only [f, fL, integral_indicator_const _ hpre, integral_indicator_const _ hpreL,
    measureReal_def, Complex.real_smul, mul_one] at heq
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
    (Complex.ofReal_inj.mp heq)

end NilBohr
