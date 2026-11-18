import NilBohr.GreenTaoLiterature
import NilBohr.GreenTaoCharacters
import NilBohr.GreenTaoHaarAmbient
import NilBohr.GreenTaoProductHaarAmbient
import NilBohr.GreenTaoContinuous
import NilBohr.GreenTaoProductMetricTopology
import NilBohr.GreenTaoMalcev

/-! Specialization of the general quantitative Leibman theorem.
The two character obstructions used in the manuscript have independent
checked adapters. -/

open MeasureTheory Polynomial
open scoped Manifold ContDiff

namespace NilBohr

noncomputable section

private theorem rational_one_relax {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Group G] [TopologicalSpace G] [ChartedSpace E G] {Γ : Subgroup G}
    {F : ℕ → Subgroup G} {m : ℕ} {X : LeibmanMalcevBasis E G Γ F m}
    (hX : X.IsRational 1) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1/2) :
    X.IsRational (1/δ) := by
  have h : 1 ≤ (1:ℝ)/δ := (le_div_iff₀ hδ).mpr (by linarith)
  intro i j k
  obtain ⟨c, hc, hnum, hden⟩ := hX i j k
  exact ⟨c, hc, hnum.trans h, hden.trans h⟩

private theorem dilatedHeisenbergOrbit_at_one (α β : ℝ) (n : ℤ) :
    dilatedHeisenbergOrbit α β 1 n = heisenbergOrbit α β n := by
  simp [dilatedHeisenbergOrbit]

private theorem scalarObstruction_of_certificates (hGT : GreenTaoQuantitativeLeibman)
    (X : LeibmanMalcevBasis HeisenbergPoint HeisenbergGroup
      HeisenbergGroup.lattice HeisenbergGroup.lowerCentral 3)
    (hX : X.IsRational 1)
    (hF : IsLeibmanFiltration HeisenbergGroup.lowerCentral 2)
    (hmetric : ∀ g h : HeisenbergGroup,
      malcevQuotientChainDistance HeisenbergGroup.lattice X.coordinates g h =
        heisenbergQuotientDistance (HeisenbergGroup.coordinates g) (HeisenbergGroup.coordinates h))
    (hcoord : X.coordinates = heisenbergMalcevFinCoordinates) :
    ScalarHeisenbergObstruction := by
  obtain ⟨C,D,hC,hD,hGT⟩ := hGT 3 2 (by decide) (by decide)
  refine ⟨C,D,hC,hD,?_⟩
  intro α β a v s K _ hs hK Φ U δ hδ hδ' hΦ hdev
  let g (t : ℤ) := HeisenbergGroup.coordinates.symm
    (dilatedHeisenbergOrbit α β s (a + (v:ℤ)*t))
  let test := heisenbergLipschitzTest Φ hΦ
  have htest (x : HeisenbergGroup) :
      test (QuotientGroup.mk x) = Φ (HeisenbergGroup.coordinates x) := rfl
  have hav : leibmanOrbitAverage g K test = heisenbergOrbitAverage α β a v s K Φ := by
    simp [leibmanOrbitAverage, heisenbergOrbitAverage, g, htest]
  have hint : (∫ q, test q ∂heisenbergNilmanifoldMeasure) = heisenbergChartMean Φ :=
    integral_heisenbergLipschitzTest Φ hΦ
  have hg : IsFilteredPolynomial HeisenbergGroup.lowerCentral g :=
    HeisenbergGroup.dilatedProgression_isFilteredPolynomial α β s (Nat.ne_of_gt hs) a v
  obtain ⟨S, L, hS, hL, hU, hsup, hlip⟩ := hΦ.2
  have hsup' (q : HeisenbergNilmanifold) : ‖test q‖ ≤ S := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rw [htest]
    exact hsup _
  have hlip' (x y : HeisenbergGroup) :
      ‖test (QuotientGroup.mk x) - test (QuotientGroup.mk y)‖ ≤
        L * malcevQuotientChainDistance HeisenbergGroup.lattice X.coordinates x y := by
    simpa only [htest, hmetric] using hlip (HeisenbergGroup.coordinates x) (HeisenbergGroup.coordinates y)
  have hbad : δ * (S+L) < ‖leibmanOrbitAverage g K test - ∫ q, test q ∂heisenbergNilmanifoldMeasure‖ := by
    rw [hav, hint]
    exact (mul_le_mul_of_nonneg_left hU hδ.le).trans_lt hdev
  obtain ⟨η,k,_,hk,hne,hbound,hdiff⟩ := hGT HeisenbergPoint HeisenbergGroup
    HeisenbergGroup.lattice HeisenbergGroup.lowerCentral X heisenbergNilmanifoldMeasure
    hF isLeibmanHaar_heisenbergNilmanifoldMeasure δ hδ hδ' (rational_one_relax hX hδ hδ')
    K hK g hg test S L hS hL hsup' hlip' hbad
  rw [hcoord] at hk
  obtain ⟨hz, hform⟩ := leibmanScalarCharacter hk
  refine ⟨k 0, k 1, ?_, max_le (hbound 0) (hbound 1), ?_⟩
  · by_contra! hn
    rw [max_le_iff] at hn
    have h₀ := abs_nonpos_iff.mp hn.1
    have h₁ := abs_nonpos_iff.mp hn.2
    obtain ⟨j,hj⟩ := hne
    apply hj
    fin_cases j
    · exact_mod_cast h₀
    · exact_mod_cast h₁
    · exact hz
  · have h := hdiff 0 (by decide)
    have hlin : leibmanCircleDifference 1
        (fun n : ℕ => Multiplicative.toAdd (η (g (n : ℤ)))) 0 =
        ((((v:ℝ)*((k 0:ℝ)*α+(k 1:ℝ)*β)/s) : ℝ) : Circle) := by
      have H := congrArg (fun z : ℝ => (z : Circle))
        (dilated_horizontal_character_difference α β s a (v:ℤ) (k 0) (k 1) 0)
      simp only [leibmanCircleDifference, hform, Nat.cast_zero, Nat.cast_one, zero_add]
      exact (AddCircle.coe_sub (1 : ℝ) _ _).symm.trans H
    simpa [hlin, torusNorm] using h

private theorem mul_Rpow_div_negative {δ A D : ℝ} (hδ : 0 < δ) (hA : 0 < A) :
    (δ/A)^(-D) = A^D * δ^(-D) := by
  rw [Real.div_rpow hδ.le hA.le, Real.rpow_neg hA.le, div_inv_eq_mul, mul_comm]

private theorem productObstruction_of_certificates
    (hGT : GreenTaoQuantitativeLeibman)
    (X : ∀ d : ℕ, 0 < d → LeibmanMalcevBasis (HeisenbergPoint × ℝ) HeisenbergProductGroup
      heisenbergProductLattice (heisenbergProductFiltration d) 4)
    (hX : ∀ d hd, (X d hd).IsRational 1)
    (hF : ∀ d : ℕ, 0 < d → IsLeibmanFiltration (heisenbergProductFiltration d) (max 2 d))
    (hmetric : ∀ d hd (g h : HeisenbergProductGroup),
      malcevQuotientChainDistance heisenbergProductLattice (X d hd).coordinates g h =
        heisenbergProductQuotientDistance (heisenbergProductCoordinates g) (heisenbergProductCoordinates h))
    (hcoord : ∀ d hd, (X d hd).coordinates = heisenbergProductMalcevFinCoordinates d) :
    ProductHeisenbergObstruction := by
  letI : SimplyConnectedSpace HeisenbergProductGroup := heisenbergProductGroup_simplyConnected
  intro d hd
  obtain ⟨C,D,hC,hD,hGT⟩ := hGT 4 (max 2 d) (by decide) (by omega)
  obtain ⟨A,hA,hAlip⟩ := heisenbergTwist_productLipschitzBound
  have hA₀ : 0 < A := zero_lt_one.trans_le hA
  have hpow : 1 ≤ A^D := Real.one_le_rpow hA hD.le
  refine ⟨C*A^D,D,by simpa only [one_mul] using mul_le_mul hC hpow zero_le_one (zero_le_one.trans hC),hD,?_⟩
  intro α β a v K _ hK Φ U δ hδ hδ' hΦ p hp hdev
  let ε := δ/A
  have hε : 0 < ε := div_pos hδ hA₀
  have hε' : ε < 1/2 := (div_le_self hδ.le hA).trans_lt hδ'
  let g (n : ℤ) : HeisenbergProductGroup :=
    (HeisenbergGroup.coordinates.symm (heisenbergOrbit α β (a+(v:ℤ)*n)),
      Multiplicative.ofAdd (p.eval (n : ℝ)))
  have hg : IsFilteredPolynomial (heisenbergProductFiltration d) g := by
    simpa only [g, dilatedHeisenbergOrbit_at_one] using
      heisenbergProductOrbit_isFilteredPolynomial α β 1 (by decide) a (v:ℤ) hp
  let test (q : HeisenbergProductNilmanifold) : ℂ :=
    heisenbergLipschitzTest Φ hΦ (heisenbergProductNilmanifoldHomeomorph q).1 *
      fourier (T := 1) (-1) (heisenbergProductNilmanifoldHomeomorph q).2
  have htest (x : HeisenbergProductGroup) : test (QuotientGroup.mk x) =
      Φ (heisenbergProductCoordinates x).1 * phase (-(heisenbergProductCoordinates x).2) := by
    simp only [test, heisenbergProductNilmanifoldHomeomorph_apply_mk]
    have hcircle (u : ℝ) : fourier (T := 1) (-1) (u : Circle) = phase (-u) := by
      rw [fourier_coe_apply, phase]
      congr 1
      push_cast
      ring
    rw [hcircle]
    rfl
  have hcont : Continuous test := by
    apply ((continuous_heisenbergLipschitzTest Φ hΦ).comp
      heisenbergProductNilmanifoldHomeomorph.continuous.fst).mul
    exact (map_continuous (fourier (T := 1) (-1))).comp
      heisenbergProductNilmanifoldHomeomorph.continuous.snd
  have hint : (∫ q, test q ∂heisenbergProductNilmanifoldMeasure) = 0 := by
    rw [integral_heisenbergProductNilmanifoldMeasure_continuous _ hcont,
      show test ∘ heisenbergProductQuotientProjection =
          (fun x => Φ x.1 * phase (-x.2)) by
        funext x
        simpa [heisenbergProductQuotientProjection, heisenbergProductCoordinates] using
          htest (heisenbergProductCoordinates.symm x)]
    exact heisenbergProductChartMean_twist_eq_zero Φ
  have hav : leibmanOrbitAverage g K test =
      heisenbergTwistedSum Φ α β a (v:ℤ) K (fun t => p.eval (t:ℝ))/(K:ℂ) := by
    simp only [leibmanOrbitAverage, heisenbergTwistedSum, sum_positiveInterval_eq_zero_prefix]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [htest]
    simp [g, heisenbergProductCoordinates, Int.cast_add, Nat.cast_add]
  obtain ⟨S,L,hS,hL,hSL,hsup,hlip⟩ := hAlip Φ U hΦ
  have hsup' (q : HeisenbergProductNilmanifold) : ‖test q‖ ≤ S := by
    obtain ⟨x,rfl⟩ := QuotientGroup.mk_surjective q
    rw [htest]
    exact hsup _
  have hlip' (x y : HeisenbergProductGroup) :
      ‖test (QuotientGroup.mk x) - test (QuotientGroup.mk y)‖ ≤
        L*malcevQuotientChainDistance heisenbergProductLattice (X d hd).coordinates x y := by
    simpa only [htest, hmetric] using hlip (heisenbergProductCoordinates x) (heisenbergProductCoordinates y)
  have hbad : ε*(S+L) < ‖leibmanOrbitAverage g K test -
      ∫ q, test q ∂heisenbergProductNilmanifoldMeasure‖ := by
    rw [hav, hint, sub_zero]
    have heq : ε*(A*U) = δ*U := by dsimp [ε]; field_simp; ring
    exact ((mul_le_mul_of_nonneg_left hSL hε.le).trans_eq heq).trans_lt hdev
  obtain ⟨η,k,_,hk,hne,hbound,hdiff⟩ := hGT (HeisenbergPoint × ℝ) HeisenbergProductGroup
    heisenbergProductLattice (heisenbergProductFiltration d) (X d hd)
    heisenbergProductNilmanifoldMeasure (hF d hd) isLeibmanHaar_heisenbergProductNilmanifoldMeasure
    ε hε hε' (rational_one_relax (hX d hd) hε hε') K hK g hg test S L hS hL hsup' hlip' hbad
  rw [hcoord] at hk
  obtain ⟨hz, hform⟩ := leibmanProductCharacter hd hk
  let m : ℤ := k (if d = 1 then 2 else 3)
  let c : ℝ := (v:ℝ)*((k 0:ℝ)*α+(k 1:ℝ)*β)
  obtain ⟨b₀,b,hb⟩ := exists_mixedBinomialPhase hd hp c (m:ℝ)
  have hscale : C*ε^(-D) = (C*A^D)*δ^(-D) := by
    dsimp [ε]
    rw [mul_Rpow_div_negative hδ hA₀, mul_assoc]
  refine ⟨k 0,k 1,m,b₀,b,leibmanProductCharacter_nonzero hz hne,?_,hb,?_⟩
  · rw [← hscale]
    exact max_le (hbound 0) (max_le (hbound 1) (hbound _))
  · intro i hi
    have hi' : i < d := Finset.mem_range.mp hi
    have H := hdiff i (hi'.trans_le (le_max_right _ _))
    have hphase : (fun n : ℕ => Multiplicative.toAdd (η (g (n:ℤ)))) =
        fun n => ((((a:ℝ)*((k 0:ℝ)*α+(k 1:ℝ)*β) + b₀ +
          realBinomialPhase d b n) : ℝ) : Circle) := by
      funext n
      rw [add_assoc, ← hb n, hform]
      apply congrArg (fun z : ℝ => (z : Circle))
      simp [g, m, c, heisenbergOrbit, HeisenbergGroup.coordinates, Int.cast_add, Int.cast_mul]
      ring
    rw [← hscale]
    simpa only [hphase, leibmanCircleDifference_binomial d _ b hi', torusNorm] using H

/-- The scalar chart obstruction is a certified application of
Green–Tao's general quantitative Leibman theorem. -/
theorem scalarHeisenbergObstruction_of_greenTao (hGT : GreenTaoQuantitativeLeibman) :
    ScalarHeisenbergObstruction := by
  have hcoord : heisenbergLeibmanBasis.coordinates = heisenbergMalcevFinCoordinates :=
    Equiv.ext heisenbergLeibmanBasis_coordinates
  refine scalarObstruction_of_certificates hGT heisenbergLeibmanBasis
    heisenbergLeibmanBasis_rational heisenbergLeibmanFiltration (fun g h => ?_) hcoord
  rw [hcoord]
  exact malcevQuotientChainDistance_eq_heisenbergQuotientDistance g h

/-- The twisted product obstruction is a certified application of
Green–Tao's general quantitative Leibman theorem. -/
theorem productHeisenbergObstruction_of_greenTao (hGT : GreenTaoQuantitativeLeibman) :
    ProductHeisenbergObstruction := by
  have hcoord (d : ℕ) (hd : 0 < d) :
      (heisenbergProductLeibmanBasis d hd).coordinates = heisenbergProductMalcevFinCoordinates d :=
    Equiv.ext (heisenbergProductLeibmanBasis_coordinates d hd)
  refine productObstruction_of_certificates hGT heisenbergProductLeibmanBasis
    heisenbergProductLeibmanBasis_rational heisenbergProductLeibmanFiltration
    (fun d hd g h => ?_) hcoord
  rw [hcoord]
  exact malcevQuotientChainDistance_eq_heisenbergProductQuotientDistance d g h

end

end NilBohr
