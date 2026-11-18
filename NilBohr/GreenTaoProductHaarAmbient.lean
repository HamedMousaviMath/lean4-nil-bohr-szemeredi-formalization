import NilBohr.GreenTaoProductHaar

/-! Ambient Haar measure and the product right-lattice fundamental domain. -/

open MeasureTheory Set

namespace NilBohr

instance : MeasurableSpace (Multiplicative ℝ) := borel _

instance : BorelSpace (Multiplicative ℝ) := ⟨rfl⟩

/-- Lebesgue measure on the multiplicatively written real coordinate. -/
noncomputable def realLineHaarMeasure : Measure (Multiplicative ℝ) :=
  Measure.map realLineHomeomorph.symm volume

private theorem realLineHaarMeasure_map_mul_left (a : Multiplicative ℝ) :
    Measure.map (a * ·) realLineHaarMeasure = realLineHaarMeasure := by
  let e := realLineHomeomorph.symm
  have he := e.continuous.measurable
  have h := measurePreserving_add_left (volume : Measure ℝ) (Multiplicative.toAdd a)
  have ha : Measurable (fun x : Multiplicative ℝ => a * x) :=
    (continuous_const.mul continuous_id).measurable
  change Measure.map (a * ·) (Measure.map e volume) = _
  rw [Measure.map_map ha he]
  change Measure.map (e ∘ (Multiplicative.toAdd a + ·)) volume = realLineHaarMeasure
  rw [← Measure.map_map he h.measurable, h.map_eq]
  rfl

instance : realLineHaarMeasure.IsMulLeftInvariant where
  map_mul_left_eq_self := realLineHaarMeasure_map_mul_left

instance : realLineHaarMeasure.IsMulRightInvariant := inferInstance

instance : realLineHaarMeasure.IsHaarMeasure where
  toIsFiniteMeasureOnCompacts := IsFiniteMeasureOnCompacts.map volume realLineHomeomorph.symm
  toIsOpenPosMeasure := realLineHomeomorph.symm.continuous.isOpenPosMeasure_map
    realLineHomeomorph.symm.surjective

instance : SigmaFinite realLineHaarMeasure :=
  realLineHomeomorph.symm.toMeasurableEquiv.sigmaFinite_map

/-- Product Lebesgue Haar measure in the matrix and real coordinates. -/
noncomputable def heisenbergProductAmbientMeasure : Measure HeisenbergProductGroup :=
  heisenbergAmbientMeasure.prod realLineHaarMeasure

instance : heisenbergProductAmbientMeasure.IsHaarMeasure := by
  unfold heisenbergProductAmbientMeasure
  infer_instance

instance : heisenbergProductAmbientMeasure.IsMulRightInvariant := by
  unfold heisenbergProductAmbientMeasure
  infer_instance

private def realLineFundamentalInterval : Set (Multiplicative ℝ) :=
  realLineHomeomorph ⁻¹' Ico (0 : ℝ) 1

private theorem realLineFundamentalInterval_measurable : MeasurableSet realLineFundamentalInterval :=
  realLineHomeomorph.continuous.measurable measurableSet_Ico

/-- The half-open four-dimensional cube in the ambient product group. -/
def heisenbergProductFundamentalCube : Set HeisenbergProductGroup :=
  heisenbergFundamentalCube ×ˢ realLineFundamentalInterval

theorem heisenbergProductFundamentalCube_measurable :
    MeasurableSet heisenbergProductFundamentalCube :=
  heisenbergFundamentalCube_measurable.prod realLineFundamentalInterval_measurable

theorem existsUnique_heisenbergProductFundamentalCube_right (g : HeisenbergProductGroup) :
    ∃! γ : heisenbergProductLattice.op, γ • g ∈ heisenbergProductFundamentalCube := by
  obtain ⟨γ, hγ, hunique⟩ := existsUnique_heisenbergFundamentalCube_right g.1
  let k : ℤ := -⌊Multiplicative.toAdd g.2⌋
  let ξ : heisenbergProductLattice.op := ⟨MulOpposite.op
    (MulOpposite.unop γ.val, Multiplicative.ofAdd (k : ℝ)),
      (heisenbergProductLattice_mem_iff _).mpr ⟨γ.prop, k, rfl⟩⟩
  have hk : Multiplicative.toAdd g.2 + (k : ℝ) ∈ Ico 0 1 := by
    simpa [k, Int.fract, sub_eq_add_neg] using
      (show Int.fract (Multiplicative.toAdd g.2) ∈ Ico 0 1 from
        ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩)
  have hξ : ξ • g ∈ heisenbergProductFundamentalCube := ⟨hγ, hk⟩
  refine ⟨ξ, hξ, ?_⟩
  intro δ hδ
  obtain ⟨hδh, b, hb⟩ := (heisenbergProductLattice_mem_iff (MulOpposite.unop δ.val)).mp δ.prop
  let δh : HeisenbergGroup.lattice.op := ⟨MulOpposite.op (MulOpposite.unop δ.val).1, hδh⟩
  have hδhγ : δh = γ := hunique δh hδ.1
  apply Subtype.ext
  apply MulOpposite.unop_injective
  apply Prod.ext
  · exact congrArg (fun u : HeisenbergGroup.lattice.op => MulOpposite.unop u.val) hδhγ
  · change Multiplicative.toAdd (MulOpposite.unop δ.val).2 = (k : ℝ)
    rw [hb]
    have hmem : Multiplicative.toAdd g.2 + (b : ℝ) ∈ Ico 0 1 := by
      have hm : Multiplicative.toAdd g.2 + Multiplicative.toAdd (MulOpposite.unop δ.val).2 ∈
          Ico 0 1 := hδ.2
      simpa only [hb] using hm
    have hfloor := Int.floor_eq_zero_iff.mpr hmem
    rw [Int.floor_add_intCast] at hfloor
    have hk' : b = k := by dsimp [k]; omega
    exact_mod_cast hk'

theorem isFundamentalDomain_heisenbergProductFundamentalCube :
    IsFundamentalDomain heisenbergProductLattice.op heisenbergProductFundamentalCube
      heisenbergProductAmbientMeasure :=
  IsFundamentalDomain.mk' heisenbergProductFundamentalCube_measurable.nullMeasurableSet
    existsUnique_heisenbergProductFundamentalCube_right

private theorem realLineHaarMeasure_restrict_fundamentalInterval :
    realLineHaarMeasure.restrict realLineFundamentalInterval =
      Measure.map realLineHomeomorph.symm unitChartIntervalMeasure := by
  rw [realLineHaarMeasure, Measure.restrict_map realLineHomeomorph.symm.continuous.measurable
    realLineFundamentalInterval_measurable, unitChartIntervalMeasure]
  congr 1
  rw [← restrict_Ico_eq_restrict_Ioc (a := (0 : ℝ)) (b := 1)]
  rfl

theorem heisenbergProductAmbientMeasure_restrict_fundamentalCube :
    heisenbergProductAmbientMeasure.restrict heisenbergProductFundamentalCube =
      Measure.map heisenbergProductCoordinatesHomeomorph.symm
        (heisenbergCubeMeasure.prod unitChartIntervalMeasure) := by
  rw [heisenbergProductAmbientMeasure, heisenbergProductFundamentalCube, ← Measure.prod_restrict,
    heisenbergAmbientMeasure_restrict_fundamentalCube,
    realLineHaarMeasure_restrict_fundamentalInterval,
    Measure.map_prod_map _ _ HeisenbergGroup.continuous_coordinates_symm.measurable
      realLineHomeomorph.symm.continuous.measurable]
  rfl

theorem heisenbergProductFundamentalCube_mass :
    heisenbergProductAmbientMeasure heisenbergProductFundamentalCube = 1 := by
  rw [← Measure.restrict_apply_univ, heisenbergProductAmbientMeasure_restrict_fundamentalCube]
  exact (isProbabilityMeasure_map heisenbergProductCoordinatesHomeomorph.symm.continuous.measurable.aemeasurable
    (μ := heisenbergCubeMeasure.prod unitChartIntervalMeasure)).measure_univ

theorem heisenbergProductNilmanifoldMeasure_eq_fundamentalDomainPushforward :
    heisenbergProductNilmanifoldMeasure =
      (heisenbergProductAmbientMeasure.restrict heisenbergProductFundamentalCube).map
        (QuotientGroup.mk : HeisenbergProductGroup → HeisenbergProductNilmanifold) := by
  rw [heisenbergProductAmbientMeasure_restrict_fundamentalCube, Measure.map_map
    QuotientGroup.continuous_mk.measurable
    heisenbergProductCoordinatesHomeomorph.symm.continuous.measurable]
  exact measurePreserving_heisenbergProductQuotientProjection.map_eq.symm

/-- The product chart probability meets the normalized Haar hypothesis of
the quantitative Leibman interface. -/
theorem isLeibmanHaar_heisenbergProductNilmanifoldMeasure :
    IsLeibmanHaar heisenbergProductLattice heisenbergProductNilmanifoldMeasure :=
  ⟨heisenbergProductNilmanifoldMeasure_leftInvariant, heisenbergProductAmbientMeasure,
    heisenbergProductFundamentalCube, inferInstance, isFundamentalDomain_heisenbergProductFundamentalCube,
    heisenbergProductFundamentalCube_measurable, heisenbergProductFundamentalCube_mass,
    heisenbergProductNilmanifoldMeasure_eq_fundamentalDomainPushforward⟩

end NilBohr
