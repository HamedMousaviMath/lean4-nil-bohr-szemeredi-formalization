import NilBohr.GreenTaoHaar
import NilBohr.GreenTaoTopology

/-! The invariant unit-cube probability on the topological Heisenberg quotient. -/

open MeasureTheory

namespace NilBohr

abbrev HeisenbergNilmanifold := HeisenbergGroup ⧸ HeisenbergGroup.lattice

instance : MeasurableSpace HeisenbergNilmanifold := borel _

instance : BorelSpace HeisenbergNilmanifold := ⟨rfl⟩

/-- The projection from matrix coordinates to their right-lattice orbit. -/
def heisenbergQuotientProjection (g : HeisenbergPoint) : HeisenbergNilmanifold :=
  QuotientGroup.mk (HeisenbergGroup.coordinates.symm g)

theorem continuous_heisenbergQuotientProjection : Continuous heisenbergQuotientProjection :=
  QuotientGroup.continuous_mk.comp HeisenbergGroup.continuous_coordinates_symm

theorem heisenbergQuotientProjection_rightInvariant (g : HeisenbergPoint) (u v w : ℤ) :
    heisenbergQuotientProjection (heisenbergMul g ((u : ℝ), (v : ℝ), (w : ℝ))) =
      heisenbergQuotientProjection g := by
  let γ : HeisenbergGroup := ⟨u, v, w⟩
  have hγ : γ ∈ HeisenbergGroup.lattice := ⟨u, v, w, rfl⟩
  have hmul : HeisenbergGroup.coordinates.symm (heisenbergMul g ((u : ℝ), (v : ℝ), (w : ℝ))) =
      HeisenbergGroup.coordinates.symm g * γ := by
    apply HeisenbergGroup.coordinates.injective
    simp [γ, HeisenbergGroup.coordinates, heisenbergMul]
  unfold heisenbergQuotientProjection
  rw [hmul, QuotientGroup.mk_mul_of_mem _ hγ]

theorem heisenbergQuotientProjection_left (a : HeisenbergGroup) (g : HeisenbergPoint) :
    a • heisenbergQuotientProjection g =
      heisenbergQuotientProjection (heisenbergMul (HeisenbergGroup.coordinates a) g) := by
  change QuotientGroup.mk (a * HeisenbergGroup.coordinates.symm g) =
    QuotientGroup.mk (HeisenbergGroup.coordinates.symm _)
  congr 1

/-- The Borel probability pushed forward by the unit-cube quotient map. -/
noncomputable def heisenbergNilmanifoldMeasure : Measure HeisenbergNilmanifold :=
  heisenbergChartPushforward heisenbergQuotientProjection

instance : IsProbabilityMeasure heisenbergNilmanifoldMeasure :=
  isProbabilityMeasure_heisenbergChartPushforward continuous_heisenbergQuotientProjection.measurable

/-- Each left translation on the compact coset quotient preserves the
unit-cube probability. -/
theorem heisenbergNilmanifoldMeasure_leftInvariant (a : HeisenbergGroup) :
    MeasurePreserving (fun q : HeisenbergNilmanifold => a • q)
      heisenbergNilmanifoldMeasure heisenbergNilmanifoldMeasure :=
  ⟨(continuous_const_smul a).measurable,
    heisenbergChartPushforward_leftInvariant continuous_heisenbergQuotientProjection.measurable
      heisenbergQuotientProjection_rightInvariant (HeisenbergGroup.coordinates a)
      (continuous_const_smul a).measurable (heisenbergQuotientProjection_left a)⟩

/-- An integrable observable on the quotient has its stated chart mean. -/
theorem integral_heisenbergNilmanifoldMeasure {Φ : HeisenbergNilmanifold → ℂ}
    (hΦ : Integrable Φ heisenbergNilmanifoldMeasure) :
    (∫ q, Φ q ∂heisenbergNilmanifoldMeasure) =
      heisenbergChartMean (Φ ∘ heisenbergQuotientProjection) :=
  integral_heisenbergChartPushforward continuous_heisenbergQuotientProjection.measurable hΦ

/-- The chart formula in particular holds for every continuous observable. -/
theorem integral_heisenbergNilmanifoldMeasure_continuous (Φ : HeisenbergNilmanifold → ℂ)
    (hΦ : Continuous Φ) :
    (∫ q, Φ q ∂heisenbergNilmanifoldMeasure) =
      heisenbergChartMean (Φ ∘ heisenbergQuotientProjection) :=
  integral_heisenbergNilmanifoldMeasure (hΦ.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace Φ))

end NilBohr
