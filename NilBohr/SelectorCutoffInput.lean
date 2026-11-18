import NilBohr.Definitions
import Mathlib.Topology.ContinuousMap.Compact

/-! Quantitative chart cutoff data for the interior and boundary comparison. -/

open AddCircle MeasureTheory
open scoped BigOperators NNReal

namespace NilBohr

/-- Three localized chart pieces and a nonnegative boundary cutoff, with the
supremum, Lipschitz and scalar integral bounds used in Theorem 3.2. -/
def QuantitativeSelectorCutoffs : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε < 1/16 →
    ∃ (pieces : Fin 3 → C(Circle, ℂ)) (lo hi : Fin 3 → ℝ) (ψ : C(Circle, ℝ)),
      (∀ j, ∃ κ : ℝ≥0, LipschitzWith κ (pieces j) ∧
        ‖pieces j‖ + (κ : ℝ) ≤ K/ε ∧ 2*(hi j-lo j) < 1 ∧
        (∀ t : ℝ, t ∈ Set.Ico (0 : ℝ) 1 → pieces j (t : Circle) ≠ 0 →
          t ∈ Set.Icc (lo j) (hi j))) ∧
      (∀ x, 0 ≤ ψ x) ∧
      (∃ κ : ℝ≥0, LipschitzWith κ ψ ∧ ‖ψ‖ + (κ : ℝ) ≤ K/ε) ∧
      (∫ x, ψ x ∂haarAddCircle) ≤ K*ε ∧
      ∀ x : Circle, (∑ j, pieces j x) + (ψ x : ℂ) = 1

end NilBohr
