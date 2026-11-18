import NilBohr.GreenTaoModel
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Instances.Int
import Mathlib.Topology.MetricSpace.Polish

/-! The coordinate topology on the real Heisenberg group and its quotient
by the integer lattice. -/

open Topology
open scoped Manifold ContDiff

namespace NilBohr.HeisenbergGroup

noncomputable section

instance : TopologicalSpace HeisenbergGroup :=
  TopologicalSpace.induced (coordinates : HeisenbergGroup → HeisenbergPoint) inferInstance

/-- The matrix coordinates transport the Euclidean topology to the group. -/
def coordinatesHomeomorph : HeisenbergGroup ≃ₜ HeisenbergPoint where
  toEquiv := coordinates
  continuous_toFun := continuous_induced_dom
  continuous_invFun := continuous_induced_rng.mpr (by
    simpa only [Equiv.self_comp_symm] using continuous_id)

@[fun_prop] theorem continuous_coordinates : Continuous (coordinates : HeisenbergGroup → HeisenbergPoint) :=
  coordinatesHomeomorph.continuous

@[fun_prop] theorem continuous_coordinates_symm :
    Continuous (coordinates.symm : HeisenbergPoint → HeisenbergGroup) :=
  coordinatesHomeomorph.symm.continuous

@[fun_prop] theorem continuous_x : Continuous (fun g : HeisenbergGroup => g.x) :=
  continuous_coordinates.fst

@[fun_prop] theorem continuous_y : Continuous (fun g : HeisenbergGroup => g.y) :=
  continuous_coordinates.snd.fst

@[fun_prop] theorem continuous_z : Continuous (fun g : HeisenbergGroup => g.z) :=
  continuous_coordinates.snd.snd

instance : T2Space HeisenbergGroup :=
  coordinatesHomeomorph.symm.t2Space

instance : SecondCountableTopology HeisenbergGroup :=
  coordinatesHomeomorph.secondCountableTopology

instance : PolishSpace HeisenbergGroup := coordinates.polishSpace_induced

instance : LocallyCompactSpace HeisenbergGroup :=
  coordinatesHomeomorph.locallyCompactSpace_iff.mpr inferInstance

instance : ContractibleSpace HeisenbergGroup :=
  coordinatesHomeomorph.contractibleSpace

theorem simplyConnected : SimplyConnectedSpace HeisenbergGroup := inferInstance

instance : IsTopologicalGroup HeisenbergGroup where
  continuous_mul := continuous_induced_rng.mpr (by
    change Continuous (fun p : HeisenbergGroup × HeisenbergGroup => coordinates (p.1 * p.2))
    simp only [coordinates_mul, heisenbergMul]
    fun_prop)
  continuous_inv := continuous_induced_rng.mpr (by
    change Continuous (fun p : HeisenbergGroup => coordinates p⁻¹)
    simp only [coordinates_inv, heisenbergInv]
    fun_prop)

/-- In the inherited topology the integer-coordinate subgroup is discrete. -/
instance : DiscreteTopology lattice := by
  let casts : ℤ × ℤ × ℤ → HeisenbergPoint := fun p => (p.1, p.2.1, p.2.2)
  have hc : IsEmbedding casts := Int.isClosedEmbedding_coe_real.isEmbedding.prodMap
    (Int.isClosedEmbedding_coe_real.isEmbedding.prodMap Int.isClosedEmbedding_coe_real.isEmbedding)
  let floors : lattice → ℤ × ℤ × ℤ := fun γ => (⌊γ.val.x⌋, ⌊γ.val.y⌋, ⌊γ.val.z⌋)
  have hcomp : casts ∘ floors = (coordinates : HeisenbergGroup → HeisenbergPoint) ∘ Subtype.val := by
    funext γ
    rcases γ with ⟨g, ⟨u, v, w, rfl⟩⟩
    simp [casts, floors, coordinates]
  have h : IsEmbedding (casts ∘ floors) := by
    rw [hcomp]
    exact coordinatesHomeomorph.isEmbedding.comp IsEmbedding.subtypeVal
  exact (hc.of_comp_iff.mp h).discreteTopology

theorem isClosed_lattice : IsClosed (lattice : Set HeisenbergGroup) := inferInstance

/-- The closed unit cube covers the quotient, by the half-open choice of
representative already constructed in the group. -/
theorem isCompact_coset_quotient : IsCompact (Set.univ : Set (HeisenbergGroup ⧸ lattice)) := by
  let cube : Set HeisenbergPoint := Set.Icc 0 1 ×ˢ (Set.Icc 0 1 ×ˢ Set.Icc 0 1)
  let K := coordinatesHomeomorph ⁻¹' cube
  have hK : IsCompact K := coordinatesHomeomorph.isCompact_preimage.mpr
    (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
  let π : HeisenbergGroup → HeisenbergGroup ⧸ lattice := QuotientGroup.mk
  have hπK : π '' K = Set.univ := by
    refine Set.eq_univ_of_forall fun q => ?_
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective (s := lattice) q
    have ⟨hx, hy, hz⟩ := unitChart_mem_cube g
    refine ⟨unitChart g, ⟨⟨hx.1, hx.2.le⟩, ⟨hy.1, hy.2.le⟩, ⟨hz.1, hz.2.le⟩⟩, ?_⟩
    symm
    apply QuotientGroup.eq.mpr
    rw [unitChart_coordinates, ← mul_assoc, inv_mul_cancel, one_mul]
    exact ⟨_, _, _, rfl⟩
  rw [← hπK]
  exact hK.image QuotientGroup.continuous_mk

instance : CompactSpace (HeisenbergGroup ⧸ lattice) :=
  isCompact_univ_iff.mp isCompact_coset_quotient

/-- Hausdorffness of the ordinary coset quotient follows from closedness
of the subgroup and openness of the quotient map. -/
instance : T2Space (HeisenbergGroup ⧸ lattice) := by
  let π : HeisenbergGroup → HeisenbergGroup ⧸ lattice := QuotientGroup.mk
  have hπ : IsOpenQuotientMap π := QuotientGroup.isOpenQuotientMap_mk
  apply t2_iff_isClosed_diagonal.mpr
  apply (hπ.prodMap hπ).isQuotientMap.isClosed_preimage.mp
  have hrel : Prod.map π π ⁻¹' Set.diagonal (HeisenbergGroup ⧸ lattice) =
      (fun p : HeisenbergGroup × HeisenbergGroup => p.1⁻¹ * p.2) ⁻¹'
        (lattice : Set HeisenbergGroup) := by
    ext p
    exact QuotientGroup.eq
  rw [hrel]
  exact isClosed_lattice.preimage (continuous_fst.inv.mul continuous_snd)

/-- The global coordinate chart equips the group with a manifold structure
over the three-dimensional real vector space of its matrix coordinates. -/
instance : ChartedSpace HeisenbergPoint HeisenbergGroup :=
  coordinatesHomeomorph.isOpenEmbedding.singletonChartedSpace

theorem finrank_coordinates : Module.finrank ℝ HeisenbergPoint = 3 := by
  simp [HeisenbergPoint, Module.finrank_prod]

theorem contMDiff_coordinates {n : WithTop ℕ∞} :
    ContMDiff 𝓘(ℝ, HeisenbergPoint) 𝓘(ℝ, HeisenbergPoint) n coordinates :=
  contMDiff_isOpenEmbedding coordinatesHomeomorph.isOpenEmbedding

private theorem contDiff_coordinate_mul {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun p : HeisenbergPoint × HeisenbergPoint => heisenbergMul p.1 p.2) := by
  unfold heisenbergMul
  fun_prop

private theorem contDiff_coordinate_inv {n : WithTop ℕ∞} :
    ContDiff ℝ n heisenbergInv := by
  unfold heisenbergInv
  fun_prop

/-- Multiplication and inversion are analytic in the global chart. -/
instance instLieGroup : LieGroup 𝓘(ℝ, HeisenbergPoint) ω HeisenbergGroup where
  toIsManifold := coordinatesHomeomorph.isOpenEmbedding.isManifold_singleton
  contMDiff_mul := by
    apply ContMDiff.of_comp_isOpenEmbedding coordinatesHomeomorph.isOpenEmbedding
    have hm : ContMDiff ((𝓘(ℝ, HeisenbergPoint)).prod 𝓘(ℝ, HeisenbergPoint))
        𝓘(ℝ, HeisenbergPoint) ω
        (fun p : HeisenbergPoint × HeisenbergPoint => heisenbergMul p.1 p.2) := by
      rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
      exact contDiff_coordinate_mul.contMDiff
    simpa only [Function.comp_def, Prod.map_apply, coordinates_mul] using
      hm.comp (contMDiff_coordinates.prodMap contMDiff_coordinates)
  contMDiff_inv := by
    apply ContMDiff.of_comp_isOpenEmbedding coordinatesHomeomorph.isOpenEmbedding
    simpa only [Function.comp_def, coordinates_inv] using
      contDiff_coordinate_inv.contMDiff.comp contMDiff_coordinates

end

end NilBohr.HeisenbergGroup
