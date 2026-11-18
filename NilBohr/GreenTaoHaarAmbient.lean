import NilBohr.GreenTaoHaarQuotient
import NilBohr.GreenTaoLeibman
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.Haar.Quotient

/-! Matrix-coordinate Lebesgue measure is bi-invariant. -/

open MeasureTheory Set Function Filter

namespace NilBohr

instance : MeasurableSpace HeisenbergGroup := borel _
instance : BorelSpace HeisenbergGroup := ⟨rfl⟩

private theorem measurePreserving_heisenbergTriangular (a b : ℝ) {t : ℝ → ℝ → ℝ}
    (ht : Measurable (uncurry t)) :
    MeasurePreserving (fun p : HeisenbergPoint => (p.1 + a, p.2.1 + b, p.2.2 + t p.1 p.2.1))
      volume volume := by
  change MeasurePreserving _ ((volume : Measure ℝ).prod (volume.prod volume))
    ((volume : Measure ℝ).prod (volume.prod volume))
  refine (measurePreserving_add_right (volume : Measure ℝ) a).skew_product
    (g := fun x (p : ℝ × ℝ) => (p.1 + b, p.2 + t x p.1)) ?_ ?_
  · exact (measurable_snd.fst.add_const b).prodMk
      (measurable_snd.snd.add (ht.comp (measurable_fst.prodMk measurable_snd.fst)))
  · refine Eventually.of_forall fun x => MeasurePreserving.map_eq
      ((measurePreserving_add_right (volume : Measure ℝ) b).skew_product
        (g := fun y z => z + t x y) ?_ ?_)
    · exact measurable_snd.add (ht.comp (measurable_const.prodMk measurable_fst))
    · exact Eventually.of_forall fun y => (measurePreserving_add_right volume (t x y)).map_eq

theorem measurePreserving_heisenbergMul_left (a : HeisenbergPoint) :
    MeasurePreserving (heisenbergMul a) volume volume := by
  convert (measurePreserving_heisenbergTriangular a.1 a.2.1
    (t := fun _ y => a.2.2 + a.1 * y) (by fun_prop)) using 1
  funext p
  simp only [heisenbergMul, Prod.mk.injEq]
  refine ⟨add_comm _ _, add_comm _ _, ?_⟩
  ring

theorem measurePreserving_heisenbergMul_right (a : HeisenbergPoint) :
    MeasurePreserving (fun p => heisenbergMul p a) volume volume := by
  convert (measurePreserving_heisenbergTriangular a.1 a.2.1
    (t := fun x _ => a.2.2 + x * a.2.1) (by fun_prop)) using 1
  funext p
  simp [heisenbergMul, add_assoc]

/-- The unimodular Lebesgue normalization specified by matrix coordinates. -/
noncomputable def heisenbergAmbientMeasure : Measure HeisenbergGroup :=
  Measure.map HeisenbergGroup.coordinates.symm volume

private theorem measurePreserving_heisenbergAmbient_of_coordinates {L : HeisenbergGroup → HeisenbergGroup}
    {l : HeisenbergPoint → HeisenbergPoint} (hL : Measurable L)
    (hl : MeasurePreserving l volume volume)
    (hcomm : L ∘ HeisenbergGroup.coordinates.symm = HeisenbergGroup.coordinates.symm ∘ l) :
    MeasurePreserving L heisenbergAmbientMeasure heisenbergAmbientMeasure := by
  have hm := HeisenbergGroup.continuous_coordinates_symm.measurable
  refine ⟨hL, ?_⟩
  rw [heisenbergAmbientMeasure, Measure.map_map hL hm, hcomm, ← Measure.map_map hm hl.measurable,
    hl.map_eq]

theorem measurePreserving_heisenbergAmbient_left (a : HeisenbergGroup) :
    MeasurePreserving (a * ·) heisenbergAmbientMeasure heisenbergAmbientMeasure :=
  measurePreserving_heisenbergAmbient_of_coordinates (continuous_const.mul continuous_id).measurable
    (measurePreserving_heisenbergMul_left (HeisenbergGroup.coordinates a)) rfl

theorem measurePreserving_heisenbergAmbient_right (a : HeisenbergGroup) :
    MeasurePreserving (· * a) heisenbergAmbientMeasure heisenbergAmbientMeasure :=
  measurePreserving_heisenbergAmbient_of_coordinates (continuous_id.mul continuous_const).measurable
    (measurePreserving_heisenbergMul_right (HeisenbergGroup.coordinates a)) rfl

instance : heisenbergAmbientMeasure.IsMulLeftInvariant where
  map_mul_left_eq_self a := (measurePreserving_heisenbergAmbient_left a).map_eq

instance : heisenbergAmbientMeasure.IsMulRightInvariant where
  map_mul_right_eq_self a := (measurePreserving_heisenbergAmbient_right a).map_eq

instance : heisenbergAmbientMeasure.IsHaarMeasure where
  toIsFiniteMeasureOnCompacts :=
    IsFiniteMeasureOnCompacts.map volume HeisenbergGroup.coordinatesHomeomorph.symm
  toIsOpenPosMeasure := HeisenbergGroup.continuous_coordinates_symm.isOpenPosMeasure_map
    HeisenbergGroup.coordinates.symm.surjective

/-- The half-open matrix cube containing exactly one representative of each coset. -/
def heisenbergFundamentalCube : Set HeisenbergGroup :=
  HeisenbergGroup.coordinates ⁻¹' (Ico (0 : ℝ) 1 ×ˢ (Ico (0 : ℝ) 1 ×ˢ Ico (0 : ℝ) 1))

theorem heisenbergFundamentalCube_measurable : MeasurableSet heisenbergFundamentalCube :=
  HeisenbergGroup.continuous_coordinates.measurable (measurableSet_Ico.prod
    (measurableSet_Ico.prod measurableSet_Ico))

theorem existsUnique_heisenbergFundamentalCube_right (g : HeisenbergGroup) :
    ∃! γ : HeisenbergGroup.lattice.op, γ • g ∈ heisenbergFundamentalCube := by
  obtain ⟨h, ⟨⟨γ, hγ, hh⟩, hcube⟩, hunique⟩ := HeisenbergGroup.existsUnique_cube_representative g
  let γ₀ : HeisenbergGroup.lattice.op := ⟨MulOpposite.op γ, hγ⟩
  have hrepr : γ₀ • g = h := hh.symm
  have hγ₀ : γ₀ • g ∈ heisenbergFundamentalCube := by
    rw [hrepr]
    exact hcube
  refine ⟨γ₀, hγ₀, ?_⟩
  intro δ hδ
  have hreprδ : δ • g = h := hunique (δ • g) ⟨⟨(MulOpposite.unop δ.val), δ.prop, rfl⟩, hδ⟩
  apply Subtype.ext
  apply MulOpposite.unop_injective
  apply mul_left_cancel (a := g)
  exact hreprδ.trans hrepr.symm

theorem isFundamentalDomain_heisenbergFundamentalCube :
    IsFundamentalDomain HeisenbergGroup.lattice.op heisenbergFundamentalCube
      heisenbergAmbientMeasure :=
  IsFundamentalDomain.mk' heisenbergFundamentalCube_measurable.nullMeasurableSet
    existsUnique_heisenbergFundamentalCube_right

theorem heisenbergAmbientMeasure_restrict_fundamentalCube :
    heisenbergAmbientMeasure.restrict heisenbergFundamentalCube =
      Measure.map HeisenbergGroup.coordinates.symm heisenbergCubeMeasure := by
  have hcube : heisenbergCubeMeasure =
      volume.restrict (Ico (0 : ℝ) 1 ×ˢ (Ico (0 : ℝ) 1 ×ˢ Ico (0 : ℝ) 1)) := by
    change _ = ((volume : Measure ℝ).prod (volume.prod volume)).restrict _
    rw [← Measure.prod_restrict, ← Measure.prod_restrict, heisenbergCubeMeasure,
      unitChartIntervalMeasure, restrict_Ico_eq_restrict_Ioc]
  rw [heisenbergAmbientMeasure, Measure.restrict_map
    HeisenbergGroup.continuous_coordinates_symm.measurable heisenbergFundamentalCube_measurable, hcube]
  congr 1

theorem heisenbergNilmanifoldMeasure_eq_fundamentalDomainPushforward :
    heisenbergNilmanifoldMeasure =
      (heisenbergAmbientMeasure.restrict heisenbergFundamentalCube).map
        (QuotientGroup.mk : HeisenbergGroup → HeisenbergNilmanifold) := by
  rw [heisenbergAmbientMeasure_restrict_fundamentalCube, Measure.map_map
    QuotientGroup.continuous_mk.measurable HeisenbergGroup.continuous_coordinates_symm.measurable]
  rfl

private instance : Countable HeisenbergGroup.lattice.op := by
  let e : ℤ × ℤ × ℤ → HeisenbergGroup.lattice :=
    fun p => ⟨⟨p.1, p.2.1, p.2.2⟩, ⟨p.1, p.2.1, p.2.2, rfl⟩⟩
  have he : Surjective e := by
    rintro ⟨g, u, v, w, rfl⟩
    exact ⟨(u, v, w), rfl⟩
  letI : Countable HeisenbergGroup.lattice := he.countable
  exact HeisenbergGroup.lattice.equivOp.surjective.countable

private instance : MeasurableSMul HeisenbergGroup.lattice.op HeisenbergGroup where
  measurable_const_smul γ :=
    (continuous_id.mul (continuous_const (y := MulOpposite.unop γ.val))).measurable
  measurable_smul_const g := by
    change Measurable (fun γ : HeisenbergGroup.lattice.op => g * MulOpposite.unop γ.val)
    exact measurable_const.mul (measurable_mul_unop.comp measurable_subtype_coe)

/-- The probability agrees with the Haar-induced restriction formula on
every measurable fundamental domain of the lattice action. -/
theorem heisenbergNilmanifoldMeasure_eq_measure_preimage_inter {D : Set HeisenbergGroup}
    (hD : IsFundamentalDomain HeisenbergGroup.lattice.op D heisenbergAmbientMeasure)
    {s : Set HeisenbergNilmanifold} (hs : MeasurableSet s) :
    heisenbergNilmanifoldMeasure s =
      heisenbergAmbientMeasure ((QuotientGroup.mk : HeisenbergGroup → HeisenbergNilmanifold)
        ⁻¹' s ∩ D) := by
  have hπ : Measurable (QuotientGroup.mk : HeisenbergGroup → HeisenbergNilmanifold) :=
    QuotientGroup.continuous_mk.measurable
  rw [heisenbergNilmanifoldMeasure_eq_fundamentalDomainPushforward, Measure.map_apply hπ hs,
    Measure.restrict_apply (hπ hs)]
  apply isFundamentalDomain_heisenbergFundamentalCube.measure_set_eq hD (hπ hs)
  intro g
  ext x
  have hx : (QuotientGroup.mk (g • x) : HeisenbergNilmanifold) = QuotientGroup.mk x :=
    QuotientGroup.mk_mul_of_mem _ g.prop
  simp only [mem_preimage, hx]

theorem heisenbergFundamentalCube_mass :
    heisenbergAmbientMeasure heisenbergFundamentalCube = 1 := by
  rw [← Measure.restrict_apply_univ, heisenbergAmbientMeasure_restrict_fundamentalCube]
  exact (isProbabilityMeasure_map HeisenbergGroup.continuous_coordinates_symm.measurable.aemeasurable
    (μ := heisenbergCubeMeasure)).measure_univ

theorem heisenbergCovolume_eq_one :
    covolume HeisenbergGroup.lattice.op HeisenbergGroup heisenbergAmbientMeasure = 1 := by
  rw [isFundamentalDomain_heisenbergFundamentalCube.covolume_eq_volume,
    heisenbergFundamentalCube_mass]

/-- The scalar chart probability meets the normalized Haar hypothesis of
the quantitative Leibman interface. -/
theorem isLeibmanHaar_heisenbergNilmanifoldMeasure :
    IsLeibmanHaar HeisenbergGroup.lattice heisenbergNilmanifoldMeasure :=
  ⟨heisenbergNilmanifoldMeasure_leftInvariant, heisenbergAmbientMeasure, heisenbergFundamentalCube,
    inferInstance, isFundamentalDomain_heisenbergFundamentalCube, heisenbergFundamentalCube_measurable,
    heisenbergFundamentalCube_mass, heisenbergNilmanifoldMeasure_eq_fundamentalDomainPushforward⟩

end NilBohr
