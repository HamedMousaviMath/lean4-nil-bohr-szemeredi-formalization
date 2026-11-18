import NilBohr.GreenTaoModel
import Mathlib.Geometry.Manifold.GroupLieAlgebra
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.MeasureTheory.Measure.Haar.Quotient
import Mathlib.Topology.Algebra.Group.Quotient

/-! Data and conventions of the one-parameter quantitative Leibman theorem
of Green and Tao, Annals of Mathematics 175 (2012), Theorem 2.9. -/

open MeasureTheory
open scoped Manifold ContDiff

namespace NilBohr

noncomputable section

/-- The degree convention and closed connected subgroups of Definition 1.1. -/
structure IsLeibmanFiltration {G : Type*} [Group G] [TopologicalSpace G]
    (F : ℕ → Subgroup G) (d : ℕ) : Prop where
  zero_eq : F 0 = ⊤
  one_eq : F 1 = ⊤
  antitone : Antitone F
  commutator_mem : ∀ {i j : ℕ} {x y : G}, x ∈ F i → y ∈ F j →
    x * y * x⁻¹ * y⁻¹ ∈ F (i + j)
  closed : ∀ i, IsClosed (F i : Set G)
  connected : ∀ i, IsConnected (F i : Set G)
  degree_end : F (d + 1) = ⊥
  degree_nontrivial : F d ≠ ⊥

/-- An ordered adapted basis in the actual manifold Lie algebra.
An axis is the one-parameter group with the corresponding initial
velocity. Factoring in order gives the coordinates of the second kind. -/
structure LeibmanMalcevBasis (E : Type*) (G : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [Group G] [TopologicalSpace G] [ChartedSpace E G]
    (Γ : Subgroup G) (F : ℕ → Subgroup G) (m : ℕ) where
  basis : Basis (Fin m) ℝ (GroupLieAlgebra 𝓘(ℝ, E) G)
  axis : Fin m → Multiplicative ℝ →* G
  axis_smooth : ∀ j, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞
    (fun t : ℝ => axis j (Multiplicative.ofAdd t))
  axis_velocity : ∀ j, HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
    (fun t : ℝ => axis j (Multiplicative.ofAdd t)) 0
    ((ContinuousLinearMap.id ℝ ℝ).smulRight (basis j))
  coordinates : G ≃ (Fin m → ℝ)
  coordinates_factor : ∀ g, (List.ofFn (fun j : Fin m =>
    axis j (Multiplicative.ofAdd (coordinates g j)))).prod = g
  coordinates_lattice : ∀ g, g ∈ Γ ↔ ∀ j, ∃ z : ℤ, coordinates g j = z
  tail_ideal : ∀ (j : ℕ) (x y : GroupLieAlgebra 𝓘(ℝ, E) G),
    (∀ k : Fin m, k.val < j → basis.repr y k = 0) →
    ∀ k : Fin m, k.val < j → basis.repr ⁅x, y⁆ k = 0
  filtration_tail : ∀ i, ∃ j ≤ m, ∀ g, g ∈ F i ↔
    ∀ k : Fin m, k.val < j → coordinates g k = 0

/-- The height of a rational number uses its reduced numerator and
positive denominator, as in Definitions 2.3 and 2.4. -/
def LeibmanMalcevBasis.IsRational {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Group G] [TopologicalSpace G] [ChartedSpace E G] {Γ : Subgroup G}
    {F : ℕ → Subgroup G} {m : ℕ} (X : LeibmanMalcevBasis E G Γ F m) (Q : ℝ) : Prop :=
  ∀ i j k : Fin m, ∃ c : ℚ, X.basis.repr ⁅X.basis i, X.basis j⁆ k = (c : ℝ) ∧
    (c.num.natAbs : ℝ) ≤ Q ∧ (c.den : ℝ) ≤ Q

/-- The normalized quotient Haar measure, represented by restricting ambient
Haar measure to a right lattice fundamental domain of mass one and pushing
it to the quotient. Left invariance is recorded on the quotient itself. -/
def IsLeibmanHaar {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] (Γ : Subgroup G) [MeasurableSpace (G ⧸ Γ)]
    (μ : Measure (G ⧸ Γ)) : Prop :=
  (∀ a : G, MeasurePreserving (fun q : G ⧸ Γ => a • q) μ μ) ∧
  ∃ (ν : Measure G) (D : Set G), ν.IsHaarMeasure ∧
    IsFundamentalDomain Γ.op D ν ∧ MeasurableSet D ∧ ν D = 1 ∧
    μ = (ν.restrict D).map (QuotientGroup.mk : G → G ⧸ Γ)

/-- Coefficients of the circle-valued binomial expansion are the successive
unit forward differences at zero. We use natural indices to read these
coefficients of an integer-indexed orbit. -/
def leibmanCircleDifference : ℕ → (ℕ → Circle) → ℕ → Circle
  | 0, f => f
  | i + 1, f => leibmanCircleDifference i (fun n => f (n + 1) - f n)

/-- The coordinate representation of a horizontal character in
Green–Tao Definition 2.6. -/
def HasLeibmanCharacterCoordinates {G : Type*} [Group G] {m : ℕ}
    (ψ : G → Fin m → ℝ) (η : G →* Multiplicative Circle) (k : Fin m → ℤ) : Prop :=
  ∀ g, η g = Multiplicative.ofAdd
    (((∑ j, (k j : ℝ) * ψ g j) : ℝ) : Circle)

/-- The finite average is on the positive integers through N. -/
def leibmanOrbitAverage {G : Type*} [Group G] {Γ : Subgroup G}
    (g : ℤ → G) (N : ℕ) (test : G ⧸ Γ → ℂ) : ℂ :=
  (∑ n ∈ positiveInterval N, test (QuotientGroup.mk (g n))) / (N : ℂ)

end

end NilBohr
