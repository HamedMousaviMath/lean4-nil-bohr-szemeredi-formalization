import NilBohr.GreenTaoLeibman
import NilBohr.MalcevChainMetric

/-! The external quantitative Leibman theorem used by the paper.
The constants are uniform in the rational Mal'cev basis and in the
filtered polynomial orbit once dimension and degree are fixed. -/

open MeasureTheory
open scoped Manifold ContDiff

namespace NilBohr

/-- Green–Tao, Theorem 2.9, in the one-parameter, complex-test form.
Supremum and Lipschitz seminorm may be supplied by any upper bounds.
The two obstruction norms are expressed by their coordinate inequalities.
All geometry is a premise about the actual group, cosets and Haar measure. -/
def GreenTaoQuantitativeLeibman : Prop :=
  ∀ m d : ℕ, 0 < m → 0 < d →
    ∃ C D : ℝ, 1 ≤ C ∧ 0 < D ∧
    ∀ (E G : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
      [Group G] [TopologicalSpace G] [ChartedSpace E G] [LieGroup 𝓘(ℝ, E) ∞ G]
      [IsTopologicalGroup G] [SimplyConnectedSpace G] [T2Space G]
      [MeasurableSpace G] [BorelSpace G]
      (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]
      [MeasurableSpace (G ⧸ Γ)] [BorelSpace (G ⧸ Γ)]
      (F : ℕ → Subgroup G) (X : LeibmanMalcevBasis E G Γ F m) (μ : Measure (G ⧸ Γ)),
      IsLeibmanFiltration F d → IsLeibmanHaar Γ μ →
      ∀ (δ : ℝ), 0 < δ → δ < 1/2 → X.IsRational (1/δ) →
      ∀ (N : ℕ), 1 < N → ∀ g : ℤ → G, IsFilteredPolynomial F g →
      ∀ (test : G ⧸ Γ → ℂ) (S L : ℝ), 0 ≤ S → 0 ≤ L →
      (∀ x, ‖test x‖ ≤ S) →
      (∀ x y : G, ‖test (QuotientGroup.mk x) - test (QuotientGroup.mk y)‖ ≤
        L * malcevQuotientChainDistance Γ X.coordinates x y) →
      δ*(S+L) < ‖leibmanOrbitAverage g N test - ∫ x, test x ∂μ‖ →
      ∃ (η : G →* Multiplicative Circle) (k : Fin m → ℤ),
        (∀ γ ∈ Γ, η γ = 1) ∧ HasLeibmanCharacterCoordinates X.coordinates η k ∧
        (∃ j, k j ≠ 0) ∧ (∀ j, |(k j : ℝ)| ≤ C*δ^(-D)) ∧
        ∀ i < d, (N : ℝ)^(i+1) *
          ‖leibmanCircleDifference (i+1) (fun n : ℕ => Multiplicative.toAdd (η (g (n : ℤ)))) 0‖
            ≤ C*δ^(-D)

end NilBohr
