import NilBohr.ArcApproximation
import NilBohr.BetaDensity
import NilBohr.GreenTaoHaarQuotient

/-!
# The open Heisenberg return window

The quotient window has horizontal coordinate off the integer seam
and reduced vertical coordinate in the specified open arc. Its
normalized Haar mass is the arc length.
-/

namespace NilBohr

open MeasureTheory Set
open scoped ENNReal

private def heisenbergWindowLift (J : OpenArc) : Set HeisenbergPoint :=
  {g | 0 < Int.fract g.2.1 ∧ J.Contains (reducedVertical g)}

/-- The open window described in the introduction. The horizontal
coordinate lies strictly between zero and one in its reduced chart. -/
def heisenbergWindow (J : OpenArc) : Set HeisenbergNilmanifold :=
  heisenbergQuotientProjection '' heisenbergWindowLift J

private theorem isOpen_heisenbergWindowLift (J : OpenArc) :
    IsOpen (heisenbergWindowLift J) := by
  let strip (m : ℤ) : Set HeisenbergPoint :=
    ((fun g : HeisenbergPoint => g.2.1) ⁻¹' Ioo (m : ℝ) ((m : ℝ) + 1)) ∩
      ((fun g : HeisenbergPoint => ((g.2.2 - g.1 * (m : ℝ) : ℝ) : Circle)) ⁻¹' J.carrier)
  have hstrip (m : ℤ) : IsOpen (strip m) := by
    apply IsOpen.inter
    · exact isOpen_Ioo.preimage (continuous_snd.fst)
    · have hJ : IsOpen J.carrier := J.carrier_eq_ball.symm ▸ Metric.isOpen_ball
      exact hJ.preimage ((AddCircle.continuous_mk' (1 : ℝ)).comp
        (continuous_snd.snd.sub (continuous_fst.mul continuous_const)))
  convert isOpen_iUnion hstrip using 1
  ext g
  simp only [heisenbergWindowLift, mem_setOf_eq, mem_iUnion, strip, mem_inter_iff,
    mem_preimage, mem_Ioo]
  constructor
  · rintro ⟨hy, hz⟩
    refine ⟨⌊g.2.1⌋, ⟨?_, Int.lt_floor_add_one _⟩, hz⟩
    exact sub_pos.mp hy
  · rintro ⟨m, ⟨hy₀, hy₁⟩, hz⟩
    have hfloor : ⌊g.2.1⌋ = m := Int.floor_eq_iff.mpr ⟨hy₀.le, hy₁⟩
    exact ⟨by simpa only [Int.fract, hfloor] using sub_pos.mpr hy₀,
      by simpa only [OpenArc.Contains, reducedVertical, hfloor] using hz⟩

theorem isOpen_heisenbergWindow (J : OpenArc) : IsOpen (heisenbergWindow J) :=
  (QuotientGroup.isOpenMap_coe.comp HeisenbergGroup.coordinatesHomeomorph.symm.isOpenMap)
    _ (isOpen_heisenbergWindowLift J)

private theorem heisenbergWindowLift_mul_lattice (J : OpenArc) (g : HeisenbergPoint)
    (u v w : ℤ) :
    heisenbergMul g ((u : ℝ), (v : ℝ), (w : ℝ)) ∈ heisenbergWindowLift J ↔
      g ∈ heisenbergWindowLift J := by
  obtain ⟨hy, hz⟩ := heisenberg_chart_right_lattice g u v w
  have hvertical : ((reducedVertical (heisenbergMul g ((u : ℝ), (v : ℝ), (w : ℝ))) :
      ℝ) : Circle) = (reducedVertical g : Circle) := by
    rw [← AddCircle.coe_fract (reducedVertical (heisenbergMul g ((u : ℝ), (v : ℝ), (w : ℝ)))),
      hz, AddCircle.coe_fract]
  simp only [heisenbergWindowLift, mem_setOf_eq, OpenArc.Contains, hy, hvertical]

/-- The two coordinates in the window membership test are independent
of the chosen right-lattice representative. -/
theorem heisenbergQuotientProjection_mem_window (J : OpenArc) (g : HeisenbergPoint) :
    heisenbergQuotientProjection g ∈ heisenbergWindow J ↔
      0 < Int.fract g.2.1 ∧ J.Contains (reducedVertical g) := by
  change heisenbergQuotientProjection g ∈ heisenbergWindow J ↔ g ∈ heisenbergWindowLift J
  constructor
  · rintro ⟨g', hg', heq⟩
    have hγ : (HeisenbergGroup.coordinates.symm g')⁻¹ * HeisenbergGroup.coordinates.symm g ∈
        HeisenbergGroup.lattice := QuotientGroup.eq.mp heq
    obtain ⟨u, v, w, hγ⟩ := hγ
    have hprod : HeisenbergGroup.coordinates.symm g = HeisenbergGroup.coordinates.symm g' *
        (⟨u, v, w⟩ : HeisenbergGroup) := by rw [← hγ, mul_inv_cancel_left]
    have hg : g = heisenbergMul g' ((u : ℝ), (v : ℝ), (w : ℝ)) := by
      simpa only [HeisenbergGroup.coordinates_mul, Equiv.apply_symm_apply] using
        congrArg HeisenbergGroup.coordinates hprod
    rw [hg, heisenbergWindowLift_mul_lattice]
    exact hg'
  · intro hg
    exact mem_image_of_mem _ hg

private theorem heisenbergWindowLift_inter_cube (J : OpenArc) :
    heisenbergWindowLift J ∩
      (Ioc (0 : ℝ) 1 ×ˢ (Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1)) =
      Ioc (0 : ℝ) 1 ×ˢ (Ioo (0 : ℝ) 1 ×ˢ
        (((fun z : ℝ => (z : Circle)) ⁻¹' J.carrier) ∩ Ioc (0 : ℝ) 1)) := by
  ext ⟨x, y, z⟩
  simp only [heisenbergWindowLift, mem_inter_iff, mem_setOf_eq, mem_prod, mem_preimage]
  have hfloor (hy : y ∈ Ioo (0 : ℝ) 1) : ⌊y⌋ = 0 :=
    Int.floor_eq_iff.mpr (by simpa only [Int.cast_zero, zero_add] using
      (show 0 ≤ y ∧ y < 1 from ⟨hy.1.le, hy.2⟩))
  constructor
  · rintro ⟨⟨hfract, hvert⟩, hx, hy, hz⟩
    have hy₁ : y < 1 := lt_of_le_of_ne hy.2 (by
      intro heq
      subst y
      norm_num [Int.fract] at hfract)
    have hy' : y ∈ Ioo (0 : ℝ) 1 := ⟨hy.1, hy₁⟩
    refine ⟨hx, hy', ?_, hz⟩
    simpa only [OpenArc.Contains, reducedVertical, hfloor hy', Int.cast_zero, mul_zero,
      sub_zero] using hvert
  · rintro ⟨hx, hy, hv, hz⟩
    refine ⟨⟨?_, ?_⟩, hx, ⟨hy.1, hy.2.le⟩, hz⟩
    · simpa only [Int.fract, hfloor hy, Int.cast_zero, sub_zero] using hy.1
    · simpa only [OpenArc.Contains, reducedVertical, hfloor hy, Int.cast_zero, mul_zero,
        sub_zero] using hv

/-- The quotient probability of the open window is the arc length.
The seam is omitted from the horizontal coordinate and has mass zero. -/
theorem heisenbergWindow_measure (J : OpenArc) :
    heisenbergNilmanifoldMeasure (heisenbergWindow J) = ENNReal.ofReal J.length := by
  have hpre : heisenbergQuotientProjection ⁻¹' heisenbergWindow J =
      heisenbergWindowLift J := by
    ext g
    exact heisenbergQuotientProjection_mem_window J g
  have hJ : MeasurableSet J.carrier := J.carrier_eq_ball.symm ▸ Metric.isOpen_ball.measurableSet
  have hV : MeasurableSet ((fun z : ℝ => (z : Circle)) ⁻¹' J.carrier) :=
    (AddCircle.continuous_mk' (1 : ℝ)).measurable hJ
  have hm : MeasurePreserving (fun z : ℝ => (z : Circle)) unitChartIntervalMeasure volume := by
    simpa only [unitChartIntervalMeasure, zero_add] using
      AddCircle.measurePreserving_mk (1 : ℝ) 0
  have hvert : volume (((fun z : ℝ => (z : Circle)) ⁻¹' J.carrier) ∩ Ioc 0 1) =
      ENNReal.ofReal J.length := by
    have h := hm.measure_preimage hJ.nullMeasurableSet
    rw [unitChartIntervalMeasure, Measure.restrict_apply hV, AddCircle.volume_eq_smul_haarAddCircle
      (T := (1 : ℝ))] at h
    simpa [J.haar_carrier] using h
  rw [heisenbergNilmanifoldMeasure, heisenbergChartPushforward,
    Measure.map_apply continuous_heisenbergQuotientProjection.measurable
      (isOpen_heisenbergWindow J).measurableSet,
    hpre, heisenbergCubeMeasure_eq, Measure.restrict_apply (isOpen_heisenbergWindowLift J).measurableSet,
    heisenbergWindowLift_inter_cube, Measure.volume_eq_prod, Measure.prod_prod,
    Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioc,
    Real.volume_Ioo, hvert]
  simp

/-- Exact membership for every integer time, including the seam condition. -/
theorem heisenbergOrbit_mem_window_iff (α β : ℝ) (J : OpenArc) (n : ℤ) :
    heisenbergQuotientProjection (heisenbergOrbit α β n) ∈ heisenbergWindow J ↔
      0 < Int.fract ((n : ℝ) * β) ∧ J.Contains (heisenbergPhase α β n) := by
  rw [heisenbergQuotientProjection_mem_window, reducedVertical_orbit]
  rfl

/-- For irrational horizontal frequency, the orbit at every nonzero
integer time avoids the seam. Its window membership is precisely the selector. -/
theorem heisenbergOrbit_mem_window_iff_of_irrational (α : ℝ) {β : ℝ} (hβ : Irrational β)
    (J : OpenArc) {n : ℤ} (hn : n ≠ 0) :
    heisenbergQuotientProjection (heisenbergOrbit α β n) ∈ heisenbergWindow J ↔
      J.Contains (heisenbergPhase α β n) := by
  have hβn := irrational_intCast_mul_iff.mpr ⟨hn, hβ⟩
  have hfract : 0 < Int.fract ((n : ℝ) * β) :=
    lt_of_le_of_ne (Int.fract_nonneg _) (fun h => hβn.ne_int _ (sub_eq_zero.mp h.symm))
  rw [heisenbergOrbit_mem_window_iff, and_iff_right hfract]

/-- Matrix coordinates of the signed powers of the translation generator. -/
theorem coordinates_heisenbergTranslation_zpow (α β : ℝ) (n : ℤ) :
    HeisenbergGroup.coordinates ((⟨α, β, 0⟩ : HeisenbergGroup) ^ n) =
      heisenbergOrbit α β n := by
  have hg : HeisenbergGroup.coordinates (⟨α, β, 0⟩ : HeisenbergGroup) =
      heisenbergOrbit α β 1 := by
    norm_num [HeisenbergGroup.coordinates, heisenbergOrbit]
  have hg_inv : HeisenbergGroup.coordinates (⟨α, β, 0⟩ : HeisenbergGroup)⁻¹ =
      heisenbergOrbit α β (-1) := by
    simp [HeisenbergGroup.coordinates, heisenbergOrbit]
    ring
  refine Int.induction_on n ?_ ?_ ?_
  · simp [HeisenbergGroup.coordinates, heisenbergOrbit]
  · intro i ih
    rw [zpow_add_one, HeisenbergGroup.coordinates_mul, ih, hg, ← heisenbergOrbit_add]
  · intro i ih
    rw [zpow_sub_one, HeisenbergGroup.coordinates_mul, ih, hg_inv,
      ← heisenbergOrbit_add, ← sub_eq_add_neg]

/-- The selector at nonzero times equals the return condition of the left
translation on the nilmanifold, starting from the identity coset. -/
theorem heisenbergRotation_mem_window_iff (α : ℝ) {β : ℝ} (hβ : AdmissibleBeta β)
    (J : OpenArc) {n : ℤ} (hn : n ≠ 0) :
    (⟨α, β, 0⟩ : HeisenbergGroup) ^ n • heisenbergQuotientProjection (0, 0, 0) ∈
        heisenbergWindow J ↔ J.Contains (heisenbergPhase α β n) := by
  rw [heisenbergQuotientProjection_left, coordinates_heisenbergTranslation_zpow]
  have hzero : heisenbergMul (heisenbergOrbit α β n) (0, 0, 0) = heisenbergOrbit α β n := by
    simp [heisenbergMul]
  rw [hzero]
  exact heisenbergOrbit_mem_window_iff_of_irrational α hβ.liouville.irrational J hn

/-- The parameter (p-1) of a prime never meets the horizontal seam
under the paper's admissibility hypotheses. -/
theorem heisenbergPrime_mem_window_iff (α : ℝ) {β : ℝ} (hβ : AdmissibleBeta β)
    (J : OpenArc) {p : ℕ} (hp : p.Prime) :
    heisenbergQuotientProjection (heisenbergOrbit α β ((p : ℤ) - 1)) ∈ heisenbergWindow J ↔
      J.Contains (heisenbergPhase α β ((p : ℤ) - 1)) := by
  apply heisenbergOrbit_mem_window_iff_of_irrational α hβ.liouville.irrational
  have := hp.two_le
  omega

end NilBohr
