import NilBohr.GreenTaoProductTopology
import Mathlib.Geometry.Manifold.GroupLieAlgebra

/-! Computation of the canonical manifold Lie brackets in the global
matrix coordinates. -/

open Topology Set
open scoped Manifold ContDiff

namespace NilBohr

noncomputable section

section GlobalChart

variable {G : Type*} [TopologicalSpace G] [Nonempty G]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (e : G ≃ₜ E)

private theorem extChartAt_global (g : G) :
    letI := e.isOpenEmbedding.singletonChartedSpace
    (extChartAt 𝓘(ℝ, E) g : G → E) = e := rfl

private theorem extChartAt_global_symm (g : G) :
    letI := e.isOpenEmbedding.singletonChartedSpace
    ((extChartAt 𝓘(ℝ, E) g).symm : E → G) = e.symm := by
  letI := e.isOpenEmbedding.singletonChartedSpace
  funext x
  change (e.isOpenEmbedding.toPartialHomeomorph e).symm ((𝓘(ℝ, E)).symm x) = e.symm x
  rw [show ((𝓘(ℝ, E)).symm x) = e (e.symm x) by simp]
  exact e.isOpenEmbedding.toPartialHomeomorph_left_inv

private theorem hasMFDerivAt_global (f : G → G) (g : G) (D : E →L[ℝ] E)
    (hf : Continuous f) (h : HasFDerivAt (e ∘ f ∘ e.symm) D (e g)) :
    letI := e.isOpenEmbedding.singletonChartedSpace
    HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, E) f g D := by
  letI := e.isOpenEmbedding.singletonChartedSpace
  refine ⟨hf.continuousAt, ?_⟩
  simpa only [writtenInExtChartAt, extChartAt_global e, extChartAt_global_symm e]
    using h.hasFDerivWithinAt (s := range (𝓘(ℝ, E)))

private theorem mfderiv_global_chart (g : G) :
    letI := e.isOpenEmbedding.singletonChartedSpace
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e g = ContinuousLinearMap.id ℝ E := by
  letI := e.isOpenEmbedding.singletonChartedSpace
  apply HasMFDerivAt.mfderiv
  refine ⟨e.continuous.continuousAt, ?_⟩
  have heq : writtenInExtChartAt 𝓘(ℝ, E) 𝓘(ℝ, E) g e = id := by
    funext x
    rw [writtenInExtChartAt, extChartAt_global_symm e]
    change e (e.symm x) = x
    exact e.apply_symm_apply x
  rw [heq]
  exact (hasFDerivAt_id _).hasFDerivWithinAt

private theorem mfderiv_global_chart_symm (x : E) :
    letI := e.isOpenEmbedding.singletonChartedSpace
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm x = ContinuousLinearMap.id ℝ E := by
  letI := e.isOpenEmbedding.singletonChartedSpace
  apply HasMFDerivAt.mfderiv
  refine ⟨e.symm.continuous.continuousAt, ?_⟩
  have heq : writtenInExtChartAt 𝓘(ℝ, E) 𝓘(ℝ, E) x e.symm = id := by
    funext y
    simp [writtenInExtChartAt, extChartAt_global e, mfld_simps]
  rw [heq]
  exact (hasFDerivAt_id _).hasFDerivWithinAt

private theorem mlieBracket_global (V W : G → E) (g : G) :
    letI := e.isOpenEmbedding.singletonChartedSpace
    VectorField.mlieBracket 𝓘(ℝ, E) V W g =
      VectorField.lieBracket ℝ (V ∘ e.symm) (W ∘ e.symm) (e g) := by
  letI := e.isOpenEmbedding.singletonChartedSpace
  rw [← VectorField.mlieBracketWithin_univ, VectorField.mlieBracketWithin_apply]
  simp only [extChartAt_global e, extChartAt_global_symm e, mfderiv_global_chart e,
    ContinuousLinearMap.inverse_id, ContinuousLinearMap.id_apply, Set.preimage_univ,
    Set.univ_inter, modelWithCornersSelf_coe, Set.range_id, VectorField.lieBracketWithin_univ]
  have hp (Y : G → E) :
      VectorField.mpullbackWithin 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm Y univ =
        Y ∘ e.symm := by
    funext x
    rw [VectorField.mpullbackWithin_apply, mfderivWithin_univ, mfderiv_global_chart_symm e]
    change (ContinuousLinearMap.id ℝ E).inverse (Y (e.symm x)) = Y (e.symm x)
    simp only [ContinuousLinearMap.inverse_id, ContinuousLinearMap.id_apply]
  rw [hp, hp]
  change (ContinuousLinearMap.id ℝ E).inverse
    (VectorField.lieBracket ℝ (V ∘ e.symm) (W ∘ e.symm) (e g)) = _
  simp only [ContinuousLinearMap.inverse_id, ContinuousLinearMap.id_apply]

/-- A real-parametrized curve has the given manifold derivative when
it has that derivative in the group's single global chart. -/
theorem hasMFDerivAt_of_global_coordinates (f : ℝ → G) (t : ℝ) (D : ℝ →L[ℝ] E)
    (hf : Continuous f) (h : HasFDerivAt (e ∘ f) D t) :
    letI := e.isOpenEmbedding.singletonChartedSpace
    HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) f t D := by
  letI := e.isOpenEmbedding.singletonChartedSpace
  refine ⟨hf.continuousAt, ?_⟩
  simpa only [writtenInExtChartAt, extChartAt_global e, mfld_simps, Function.comp_id]
    using h.hasFDerivWithinAt (s := range (𝓘(ℝ, ℝ)))

end GlobalChart

private abbrev xProjection :
    HeisenbergPoint →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)

private abbrev yProjection : HeisenbergPoint →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))

private abbrev zProjection : HeisenbergPoint →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))

private def leftMulDerivative (a : ℝ) : HeisenbergPoint →L[ℝ] HeisenbergPoint :=
  xProjection.prod (yProjection.prod (zProjection + a • yProjection))

private theorem leftMulDerivative_hasFDerivAt (a h : HeisenbergPoint) :
    HasFDerivAt (heisenbergMul a) (leftMulDerivative a.1) h := by
  exact
    (xProjection.hasFDerivAt.const_add a.1).prodMk
      ((yProjection.hasFDerivAt.const_add a.2.1).prodMk
        ((zProjection.hasFDerivAt.const_add a.2.2).add
          (yProjection.hasFDerivAt.const_mul a.1)))

private theorem heisenberg_invariantField_coordinates (v : HeisenbergPoint) (g : HeisenbergGroup) :
    mulInvariantVectorField (I := 𝓘(ℝ, HeisenbergPoint)) v g =
      (v.1, v.2.1, v.2.2 + g.x * v.2.1) := by
  have h : HasMFDerivAt 𝓘(ℝ, HeisenbergPoint) 𝓘(ℝ, HeisenbergPoint)
      (g * ·) (1 : HeisenbergGroup) (leftMulDerivative g.x) := by
    apply hasMFDerivAt_global HeisenbergGroup.coordinatesHomeomorph _ _ _
      (continuous_const.mul continuous_id)
    simpa [Function.comp_def, HeisenbergGroup.coordinates_mul] using
      leftMulDerivative_hasFDerivAt (HeisenbergGroup.coordinates g)
        (HeisenbergGroup.coordinates (1 : HeisenbergGroup))
  rw [mulInvariantVectorField, h.mfderiv]
  rfl

private def invariantField (v : HeisenbergPoint) (p : HeisenbergPoint) : HeisenbergPoint :=
  (v.1, v.2.1, v.2.2 + p.1 * v.2.1)

private def invariantFieldDerivative (v : HeisenbergPoint) : HeisenbergPoint →L[ℝ] HeisenbergPoint :=
  (0 : HeisenbergPoint →L[ℝ] ℝ).prod
    ((0 : HeisenbergPoint →L[ℝ] ℝ).prod (v.2.1 • xProjection))

private theorem invariantField_hasFDerivAt (v p : HeisenbergPoint) :
    HasFDerivAt (invariantField v) (invariantFieldDerivative v) p := by
  refine (hasFDerivAt_const _ _).prodMk ((hasFDerivAt_const _ _).prodMk ?_)
  have h : HasFDerivAt (fun q : HeisenbergPoint => v.2.2 + v.2.1 * q.1)
      (v.2.1 • xProjection) p :=
    ((xProjection.hasFDerivAt (x := p)).const_mul v.2.1).const_add v.2.2
  simpa only [invariantField, mul_comm v.2.1] using h

/-- The Lie bracket in the tangent space at the identity of the scalar group. -/
theorem heisenberg_groupLie_bracket
    (v w : GroupLieAlgebra 𝓘(ℝ, HeisenbergPoint) HeisenbergGroup) :
    ⁅v, w⁆ = (0, 0, v.1 * w.2.1 - w.1 * v.2.1) := by
  rw [GroupLieAlgebra.bracket_def, mlieBracket_global HeisenbergGroup.coordinatesHomeomorph]
  have h (a : HeisenbergPoint) :
      mulInvariantVectorField (I := 𝓘(ℝ, HeisenbergPoint)) (G := HeisenbergGroup) a ∘
        HeisenbergGroup.coordinatesHomeomorph.symm = invariantField a := by
    funext p
    rw [Function.comp_apply, heisenberg_invariantField_coordinates]
    rfl
  rw [h, h, VectorField.lieBracket, (invariantField_hasFDerivAt _ _).fderiv,
    (invariantField_hasFDerivAt _ _).fderiv]
  change (0 - 0, 0 - 0, w.2.1 * v.1 - v.2.1 * w.1) = _
  simp [mul_comm]

private def productInvariantField (v : HeisenbergPoint × ℝ) (p : HeisenbergPoint × ℝ) :
    HeisenbergPoint × ℝ :=
  (invariantField v.1 p.1, v.2)

private theorem heisenbergProduct_invariantField_coordinates (v : HeisenbergPoint × ℝ)
    (g : HeisenbergProductGroup) :
    mulInvariantVectorField (I := 𝓘(ℝ, HeisenbergPoint × ℝ)) v g =
      productInvariantField v (heisenbergProductCoordinates g) := by
  let D := (leftMulDerivative g.1.x).prodMap (ContinuousLinearMap.id ℝ ℝ)
  have h : HasMFDerivAt 𝓘(ℝ, HeisenbergPoint × ℝ) 𝓘(ℝ, HeisenbergPoint × ℝ)
      (g * ·) (1 : HeisenbergProductGroup) D := by
    apply hasMFDerivAt_global heisenbergProductCoordinatesHomeomorph _ _ _
      (continuous_const.mul continuous_id)
    have ha := leftMulDerivative_hasFDerivAt (HeisenbergGroup.coordinates g.1) (0, 0, 0)
    have hb := (hasFDerivAt_id (𝕜 := ℝ) (0 : ℝ)).const_add (Multiplicative.toAdd g.2)
    convert HasFDerivAt.prodMap (p := (((0, 0, 0) : HeisenbergPoint), (0 : ℝ))) ha hb using 1
  rw [mulInvariantVectorField, h.mfderiv]
  rfl

private theorem productInvariantField_hasFDerivAt (v p : HeisenbergPoint × ℝ) :
    HasFDerivAt (productInvariantField v)
      ((invariantFieldDerivative v.1).prodMap (0 : ℝ →L[ℝ] ℝ)) p :=
  HasFDerivAt.prodMap (p := p) (invariantField_hasFDerivAt v.1 p.1)
    (hasFDerivAt_const v.2 p.2)

/-- The real factor is central in the Lie algebra of the product group. -/
theorem heisenbergProduct_groupLie_bracket
    (v w : GroupLieAlgebra 𝓘(ℝ, HeisenbergPoint × ℝ) HeisenbergProductGroup) :
    ⁅v, w⁆ = ((0, 0, v.1.1 * w.1.2.1 - w.1.1 * v.1.2.1), 0) := by
  rw [GroupLieAlgebra.bracket_def, mlieBracket_global heisenbergProductCoordinatesHomeomorph]
  have h (a : HeisenbergPoint × ℝ) :
      mulInvariantVectorField (I := 𝓘(ℝ, HeisenbergPoint × ℝ)) (G := HeisenbergProductGroup) a ∘
        heisenbergProductCoordinatesHomeomorph.symm = productInvariantField a := by
    funext p
    rw [Function.comp_apply, heisenbergProduct_invariantField_coordinates]
    change productInvariantField a
      (heisenbergProductCoordinates (heisenbergProductCoordinates.symm p)) = _
    rw [Equiv.apply_symm_apply]
  rw [h, h, VectorField.lieBracket, (productInvariantField_hasFDerivAt _ _).fderiv,
    (productInvariantField_hasFDerivAt _ _).fderiv]
  change ((0 - 0, 0 - 0, w.1.2.1 * v.1.1 - v.1.2.1 * w.1.1), 0 - 0) = _
  simp [mul_comm]

end

end NilBohr
