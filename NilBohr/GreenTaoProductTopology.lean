import NilBohr.GreenTaoTopology

/-! The analytic group and ordinary right-coset quotient for the
Heisenberg group with an extra real coordinate. -/

open Topology
open scoped Manifold ContDiff

namespace NilBohr

noncomputable section

/-- The ambient group for the polynomial twist. -/
abbrev HeisenbergProductGroup := HeisenbergGroup × Multiplicative ℝ

/-- The usual real topology, written in multiplicative notation. -/
def realLineHomeomorph : Multiplicative ℝ ≃ₜ ℝ :=
  { toEquiv := Multiplicative.toAdd
    continuous_toFun := continuous_id
    continuous_invFun := continuous_id }

instance : ContractibleSpace (Multiplicative ℝ) :=
  realLineHomeomorph.contractibleSpace

instance : ChartedSpace ℝ (Multiplicative ℝ) :=
  realLineHomeomorph.isOpenEmbedding.singletonChartedSpace

private theorem contMDiff_realLine {n : WithTop ℕ∞} :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) n realLineHomeomorph :=
  contMDiff_isOpenEmbedding realLineHomeomorph.isOpenEmbedding

instance : LieGroup 𝓘(ℝ, ℝ) ω (Multiplicative ℝ) where
  toIsManifold := realLineHomeomorph.isOpenEmbedding.isManifold_singleton
  contMDiff_mul := by
    apply ContMDiff.of_comp_isOpenEmbedding realLineHomeomorph.isOpenEmbedding
    have hm : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ω
        (fun p : ℝ × ℝ => p.1 + p.2) := by
      rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
      exact (contDiff_fst.add contDiff_snd).contMDiff
    exact hm.comp (contMDiff_realLine.prodMap contMDiff_realLine)
  contMDiff_inv := by
    apply ContMDiff.of_comp_isOpenEmbedding realLineHomeomorph.isOpenEmbedding
    exact contMDiff_realLine.neg

/-- The product matrix and real-line coordinates. -/
def heisenbergProductCoordinates : HeisenbergProductGroup ≃ (HeisenbergPoint × ℝ) :=
  HeisenbergGroup.coordinates.prodCongr Multiplicative.toAdd

/-- The product coordinates are a homeomorphism. -/
def heisenbergProductCoordinatesHomeomorph : HeisenbergProductGroup ≃ₜ (HeisenbergPoint × ℝ) :=
  HeisenbergGroup.coordinatesHomeomorph.prodCongr realLineHomeomorph

instance : ChartedSpace (HeisenbergPoint × ℝ) HeisenbergProductGroup :=
  heisenbergProductCoordinatesHomeomorph.isOpenEmbedding.singletonChartedSpace

theorem contMDiff_heisenbergProductCoordinates {n : WithTop ℕ∞} :
    ContMDiff 𝓘(ℝ, HeisenbergPoint × ℝ) 𝓘(ℝ, HeisenbergPoint × ℝ) n
      heisenbergProductCoordinates :=
  contMDiff_isOpenEmbedding heisenbergProductCoordinatesHomeomorph.isOpenEmbedding

instance : LieGroup 𝓘(ℝ, HeisenbergPoint × ℝ) ω HeisenbergProductGroup where
  toIsManifold := heisenbergProductCoordinatesHomeomorph.isOpenEmbedding.isManifold_singleton
  contMDiff_mul := by
    apply ContMDiff.of_comp_isOpenEmbedding heisenbergProductCoordinatesHomeomorph.isOpenEmbedding
    have hm : ContMDiff ((𝓘(ℝ, HeisenbergPoint × ℝ)).prod 𝓘(ℝ, HeisenbergPoint × ℝ))
        𝓘(ℝ, HeisenbergPoint × ℝ) ω
        (fun p : (HeisenbergPoint × ℝ) × (HeisenbergPoint × ℝ) =>
          (heisenbergMul p.1.1 p.2.1, p.1.2 + p.2.2)) := by
      rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
      apply ContDiff.contMDiff
      unfold heisenbergMul
      fun_prop
    simpa only [Function.comp_def, Prod.map_apply, heisenbergProductCoordinates,
      LinearEquiv.coe_prodCongr, Equiv.prodCongr_apply, HeisenbergGroup.coordinates_mul] using
      hm.comp (contMDiff_heisenbergProductCoordinates.prodMap contMDiff_heisenbergProductCoordinates)
  contMDiff_inv := by
    apply ContMDiff.of_comp_isOpenEmbedding heisenbergProductCoordinatesHomeomorph.isOpenEmbedding
    have hi : ContDiff ℝ ω (fun p : HeisenbergPoint × ℝ => (heisenbergInv p.1, -p.2)) := by
      unfold heisenbergInv
      fun_prop
    simpa only [Function.comp_def, heisenbergProductCoordinates, Equiv.prodCongr_apply,
      HeisenbergGroup.coordinates_inv] using hi.contMDiff.comp contMDiff_heisenbergProductCoordinates

theorem heisenbergProductGroup_simplyConnected : SimplyConnectedSpace HeisenbergProductGroup := by
  letI : ContractibleSpace HeisenbergProductGroup :=
    heisenbergProductCoordinatesHomeomorph.contractibleSpace
  infer_instance

theorem finrank_heisenbergProductCoordinates : Module.finrank ℝ (HeisenbergPoint × ℝ) = 4 := by
  rw [Module.finrank_prod, HeisenbergGroup.finrank_coordinates, Module.finrank_self]

/-- The product right lattice has integer coordinates in each factor. -/
def heisenbergProductLattice : Subgroup HeisenbergProductGroup :=
  HeisenbergGroup.lattice.prod ((AddSubgroup.zmultiples (1 : ℝ)).toSubgroup)

abbrev HeisenbergProductNilmanifold := HeisenbergProductGroup ⧸ heisenbergProductLattice

private def productQuotientProjection (g : HeisenbergProductGroup) :
    (HeisenbergGroup ⧸ HeisenbergGroup.lattice) × Circle :=
  (QuotientGroup.mk g.1, ((Multiplicative.toAdd g.2 : ℝ) : Circle))

private theorem productQuotientProjection_open :
    IsOpenQuotientMap productQuotientProjection := by
  exact (QuotientGroup.isOpenQuotientMap_mk (N := HeisenbergGroup.lattice)).prodMap
    (QuotientAddGroup.isOpenQuotientMap_mk (N := AddSubgroup.zmultiples (1 : ℝ)))

theorem heisenbergProductLattice_mem_iff (g : HeisenbergProductGroup) :
    g ∈ heisenbergProductLattice ↔
      g.1 ∈ HeisenbergGroup.lattice ∧ ∃ b : ℤ, Multiplicative.toAdd g.2 = (b : ℝ) := by
  change g.1 ∈ HeisenbergGroup.lattice ∧ Multiplicative.toAdd g.2 ∈
    AddSubgroup.zmultiples (1 : ℝ) ↔ _
  simp [AddSubgroup.mem_zmultiples_iff, eq_comm]

instance : DiscreteTopology heisenbergProductLattice := by
  let casts : (ℤ × ℤ × ℤ) × ℤ → HeisenbergPoint × ℝ := fun p =>
    ((p.1.1, p.1.2.1, p.1.2.2), p.2)
  have hc : IsEmbedding casts := (Int.isClosedEmbedding_coe_real.isEmbedding.prodMap
    (Int.isClosedEmbedding_coe_real.isEmbedding.prodMap
      Int.isClosedEmbedding_coe_real.isEmbedding)).prodMap Int.isClosedEmbedding_coe_real.isEmbedding
  let floors : heisenbergProductLattice → (ℤ × ℤ × ℤ) × ℤ := fun γ =>
    ((⌊γ.val.1.x⌋, ⌊γ.val.1.y⌋, ⌊γ.val.1.z⌋), ⌊Multiplicative.toAdd γ.val.2⌋)
  have hcomp : casts ∘ floors =
      (heisenbergProductCoordinates : HeisenbergProductGroup → HeisenbergPoint × ℝ) ∘ Subtype.val := by
    funext γ
    obtain ⟨⟨u, v, w, huv⟩, b, hb⟩ := (heisenbergProductLattice_mem_iff γ.val).mp γ.prop
    change ((↑⌊γ.val.1.x⌋, ↑⌊γ.val.1.y⌋, ↑⌊γ.val.1.z⌋), ↑⌊Multiplicative.toAdd γ.val.2⌋) =
      ((γ.val.1.x, γ.val.1.y, γ.val.1.z), Multiplicative.toAdd γ.val.2)
    rw [huv, hb]
    simp
  have h : IsEmbedding (casts ∘ floors) := by
    rw [hcomp]
    exact heisenbergProductCoordinatesHomeomorph.isEmbedding.comp IsEmbedding.subtypeVal
  exact (hc.of_comp_iff.mp h).discreteTopology

private theorem productQuotientProjection_eq_iff (g h : HeisenbergProductGroup) :
    productQuotientProjection g = productQuotientProjection h ↔
      g⁻¹ * h ∈ heisenbergProductLattice := by
  rw [heisenbergProductLattice_mem_iff]
  change ((QuotientGroup.mk g.1 : HeisenbergGroup ⧸ HeisenbergGroup.lattice),
      ((Multiplicative.toAdd g.2 : ℝ) : Circle)) =
    (QuotientGroup.mk h.1, ((Multiplicative.toAdd h.2 : ℝ) : Circle)) ↔
      g.1⁻¹ * h.1 ∈ HeisenbergGroup.lattice ∧
      ∃ b : ℤ, -Multiplicative.toAdd g.2 + Multiplicative.toAdd h.2 = (b : ℝ)
  rw [Prod.mk.injEq, QuotientGroup.eq]
  rw [eq_comm, ← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
  simp [sub_eq_add_neg, add_comm, eq_comm]

/-- The actual right-coset quotient is homeomorphic to the product of
the scalar right-coset quotient and the circle. -/
def heisenbergProductNilmanifoldHomeomorph :
    HeisenbergProductNilmanifold ≃ₜ
      (HeisenbergGroup ⧸ HeisenbergGroup.lattice) × Circle := by
  let f : HeisenbergProductNilmanifold →
      (HeisenbergGroup ⧸ HeisenbergGroup.lattice) × Circle :=
    Quotient.lift productQuotientProjection (fun g h hh =>
      (productQuotientProjection_eq_iff g h).mpr (QuotientGroup.leftRel_apply.mp hh))
  have hf (g : HeisenbergProductGroup) :
      f (QuotientGroup.mk g) = productQuotientProjection g := rfl
  have hinj : Function.Injective f := by
    intro q q' h
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective q'
    rw [hf, hf] at h
    exact QuotientGroup.eq.mpr ((productQuotientProjection_eq_iff _ _).mp h)
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨g, hg⟩ := productQuotientProjection_open.surjective q
    exact ⟨QuotientGroup.mk g, hg⟩
  let e := Equiv.ofBijective f ⟨hinj, hsurj⟩
  refine ⟨e, (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
    productQuotientProjection_open.continuous, ?_⟩
  apply productQuotientProjection_open.isQuotientMap.continuous_iff.mpr
  have heq : e.symm ∘ productQuotientProjection = QuotientGroup.mk := by
    funext g
    exact e.symm_apply_apply (QuotientGroup.mk g)
  change Continuous (e.symm ∘ productQuotientProjection)
  rw [heq]
  exact QuotientGroup.continuous_mk

@[simp] theorem heisenbergProductNilmanifoldHomeomorph_apply_mk (g : HeisenbergProductGroup) :
    heisenbergProductNilmanifoldHomeomorph (QuotientGroup.mk g) =
      (QuotientGroup.mk g.1, ((Multiplicative.toAdd g.2 : ℝ) : Circle)) := rfl

instance : CompactSpace HeisenbergProductNilmanifold :=
  heisenbergProductNilmanifoldHomeomorph.symm.compactSpace

instance : T2Space HeisenbergProductNilmanifold :=
  heisenbergProductNilmanifoldHomeomorph.symm.t2Space

theorem isClosed_heisenbergProductLattice : IsClosed (heisenbergProductLattice : Set HeisenbergProductGroup) := by
  have h : (heisenbergProductLattice : Set HeisenbergProductGroup) =
      (QuotientGroup.mk : HeisenbergProductGroup → HeisenbergProductNilmanifold) ⁻¹'
        {QuotientGroup.mk (1 : HeisenbergProductGroup)} := by
    ext g
    simp [Set.mem_preimage, Set.mem_singleton_iff, eq_comm, QuotientGroup.eq]
  rw [h]
  exact isClosed_singleton.preimage QuotientGroup.continuous_mk

end

end NilBohr
