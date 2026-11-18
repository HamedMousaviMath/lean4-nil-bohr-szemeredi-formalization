import NilBohr.SeparatingGowers
import NilBohr.SeparatingQuadraticLimit
import NilBohr.SeparatingLocal
import NilBohr.SeparatingComparison

/-! Appendix A.1 on the actual sequence of smooth moduli. -/

open Filter
open scoped Topology NNReal

namespace NilBohr

/-- The scale and all three estimates in Proposition A.1. The scale
(N_j=q_j M_j^2) is exact. Each bound is eventually uniform over
the tests and progressions named in its conclusion. -/
structure SeparatingFamilyClaims (α β : ℝ) (F : Circle → ℂ)
    (r w q M : ℕ → ℕ) : Prop where
  parameterGrows : Tendsto M atTop atTop
  parameterLength : ∀ᶠ j : ℕ in atTop,
    0 < q j ∧ 0 < M j ∧ parameterLength (q j*(M j)^2) (q j) 2 = M j
  relativeRange : ∀ (c₀ cRel : ℝ), 0 < c₀ → 0 < cRel → ∀ w₀ : ℕ,
    ∀ᶠ j : ℕ in atTop, RelativeModulus c₀ cRel w₀ (q j*(M j)^2) (q j) (w j)
  scaleWindow : ∀ᶠ j : ℕ in atTop, RelativeScaleWindow 2 (q j*(M j)^2) (M j)
  modulusSize : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ j : ℕ in atTop,
    c*(Real.log (r j : ℝ))^2 ≤ Real.log (q j : ℝ) ∧
    Real.log (q j : ℝ) ≤ C*(Real.log (r j : ℝ))^2
  globalPhaseLower : ∃ c : ℝ, 0 < c ∧ ∀ᶠ j : ℕ in atTop,
    c/(r j : ℝ) ≤ phaseNorm 3 (positiveInterval (M j)) (separatingWeight α β F (q j))
  localPhaseUpper : SeparatingLocalPhaseDecay α β F q M
  gowersLower : ∀ S : ℕ, 3 ≤ S → ∃ c : ℝ, 0 < c ∧ ∀ᶠ j : ℕ in atTop,
    c ≤ normalizedGowers S 1 (M j : ℤ) (separatingWeight α β F (q j))

/-- Proposition A.1 for any fixed admissible denominator witness. The
quantitative nilmanifold inputs are the same explicit obstructions as
in Proposition 4.3. The global phase lower bound uses only the
badly approximable and positive one-sided approximation hypotheses. -/
theorem separatingFamily_of_obstructions
    (hGT : ProductHeisenbergObstruction) (hScalar : ScalarHeisenbergObstruction)
    (hBernstein : BernsteinCircleLipschitzFourier)
    (hG : ∀ S : ℕ, 3 ≤ S → NormalizedGowersLaws S)
    {α β : ℝ} (hα : BadlyApproximable α) {r : ℕ → ℕ}
    (hr : AdmissibleBetaDenominators β r) (F : C(Circle, ℂ))
    {κ : ℝ≥0} (hF : LipschitzWith κ F)
    (hNonconstant : ∃ x y : Circle, F x ≠ F y) :
    SeparatingFamilyClaims α β F r (fun j => separatingW (r j))
      (fun j => separatingModulus (r j)) (fun j => separatingLength (r j) (r (j+1))) := by
  let q : ℕ → ℕ := fun j => separatingModulus (r j)
  let M : ℕ → ℕ := fun j => separatingLength (r j) (r (j+1))
  let H : ℕ → ℕ := fun j => separatingLengthQuotient (r j) (r (j+1))
  have hS := eventually_separatingScale hr
  have hApproximation := hr
  obtain ⟨_,a,_,hPrime,_,_,D,_,_,hD,hApprox⟩ := hApproximation
  have hPr (j : ℕ) : (r j).Prime := (hPrime j).1
  have hBelow (j : ℕ) : 0 ≤ β - (a j : ℝ)/(r j : ℝ) := (hApprox j).2.2.1.le
  refine ⟨tendsto_separatingLength hr, ?_, ?_, eventually_separatingRelativeScaleWindow hr,
    ?_, ?_, separatingLocalPhase_of_obstructions hGT hScalar hα hr F hF, ?_⟩
  · exact hS.mono fun j hj =>
      ⟨hj.q_pos, hj.M_pos, parameterLength_separatingFamily (M j) hj.q_pos⟩
  · intro c₀ cRel hc₀ hcRel w₀
    exact eventually_separatingRelativeModulus hr hc₀ hcRel w₀
  · refine ⟨1/8, 1, by norm_num, by norm_num, ?_⟩
    filter_upwards [hS] with j hj
    have hp : (1 : ℝ) ≤ r j := by exact_mod_cast (hPr j).one_lt.le
    have hW : (separatingW (r j) : ℝ) ≤ Real.log (r j : ℝ) :=
      Nat.floor_le (Real.log_nonneg hp)
    constructor
    · simpa [div_eq_mul_inv, mul_comm] using hj.log_q_lower
    · rw [one_mul]
      exact hj.log_q_upper.trans (pow_le_pow_left₀ (Nat.cast_nonneg _) hW 2)
  · have hPos : ∀ᶠ j : ℕ in atTop, 0 < a j ∧ 0 < r j ∧ 0 < q j :=
      hS.mono fun j hj => ⟨(hPrime j).2.1,(hPr j).pos,hj.q_pos⟩
    have hSize := tendsto_separatingCoefficient_div_lengthQuotient hr a (fun j => (hPrime j).2.2.le)
    have hErr := tendsto_separatingApproximation hr a hD.le hBelow (fun j => (hApprox j).2.2.2)
    exact separatingGlobalPhase_lower_bound α β hα F hF hNonconstant a r q H
      (tendsto_separatingLengthQuotient hr) hPos (Eventually.of_forall hBelow) hSize hErr
  · intro S hOrder
    obtain ⟨C,hC,hLower⟩ := separating_gowers_lower_bound hScalar hBernstein α β hα hr
      F hF hNonconstant S hOrder (hG S hOrder)
    refine ⟨C,hC,?_⟩
    let X : ℕ → ℕ := fun j => separatingScaleX (r j) (r (j+1))
    have hXt : Tendsto (fun j => (X j : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_separatingScaleX hr)
    filter_upwards [hS, eventually_separatingStep hr 0, hXt.eventually hLower] with j hj hStep hLower
    have hStep' : (q j : ℝ) ≤ (X j : ℝ)^(1/10000 : ℝ) := by
      simpa only [q, X, zero_add, pow_one, separatingScaleX, Nat.cast_mul] using hStep
    exact hLower j (q j) (M j) hj.bracket_left hj.bracket_right hj.q_pos hStep'
      ((hPr j).coprime_iff_not_dvd.mp hj.coprime.symm) hj.sqrt_X_le_length

/-- Existential form of Proposition A.1 under the paper's admissibility
predicate. The proof chooses the exact floored sequence in the paper. -/
theorem appendixA_separating_family
    (hGT : ProductHeisenbergObstruction) (hScalar : ScalarHeisenbergObstruction)
    (hBernstein : BernsteinCircleLipschitzFourier)
    (hG : ∀ S : ℕ, 3 ≤ S → NormalizedGowersLaws S)
    {α β : ℝ} (hα : BadlyApproximable α) (hβ : AdmissibleBeta β)
    (F : Circle → ℂ) {κ : ℝ≥0} (hF : LipschitzWith κ F)
    (hNonconstant : ∃ x y : Circle, F x ≠ F y) :
    ∃ r w q M : ℕ → ℕ, AdmissibleBetaDenominators β r ∧
      SeparatingFamilyClaims α β F r w q M := by
  obtain ⟨_,_,r,hr⟩ := (admissibleBeta_iff_exists_denominators β).mp hβ
  let Fc : C(Circle, ℂ) := ⟨F,hF.continuous⟩
  exact ⟨r,_,_,_,hr,
    separatingFamily_of_obstructions hGT hScalar hBernstein hG hα hr Fc hF hNonconstant⟩

/-- The direct local estimate and both fixed-family comparisons on
one sequence. Divergence here is a statement about the displayed
upper bounds. The actual weighted counts tend uniformly to zero. -/
structure SeparatingCountComparison (α β : ℝ) (F : Circle → ℂ) (q M : ℕ → ℕ) : Prop where
  directBound : ∃ C : ℝ, 0 < C ∧ ∀ᶠ j : ℕ in atTop,
    let N := q j*(M j)^2
    ∀ f : Fin 3 → ℤ → ℂ,
      (∀ i, OneBoundedOn (spatialInterval 1 N) (f i)) →
      (∀ i, SupportedOn (spatialInterval 1 N) (f i)) →
      ‖countingForm N (M j) (spatialInterval 1 N) (separatingFamily (q j))
        (separatingWeight α β F (q j)) f‖ ≤ C*(Real.log (M j : ℝ))⁻¹
  fixedShiftBounds : ∃ K C : ℝ, 1 ≤ K ∧ 0 < C ∧ ∀ᶠ j : ℕ in atTop,
    let N := q j*(M j)^2
    let v := separatingWeight α β F (q j)
    let E := fixedDilationPhaseBound (q j) (M j) v
    ∀ f : Fin 3 → ℤ → ℂ,
      (∀ i, OneBoundedOn (spatialInterval 1 N) (f i)) →
      (∀ i, SupportedOn (spatialInterval 1 N) (f i)) →
      let T := countingForm N (M j) (spatialInterval 1 N) (separatingFamily (q j)) v f
      (‖T‖ ≤ C*(q j : ℝ)^2*E^(1/K)) ∧ (‖T‖ ≤ C*(q j : ℝ)*E^(1/K))
  modulusLossDiverges : ∀ c σ : ℝ, 0 < c → 0 < σ →
    Tendsto (fun j => (q j : ℝ)^c *
      (phaseNorm 3 (positiveInterval (M j)) (separatingWeight α β F (q j)))^σ) atTop atTop
  zeroExtensionDiverges : ∀ K : ℝ, 1 ≤ K →
    Tendsto (fun j => (q j : ℝ)^2 *
      (fixedDilationPhaseBound (q j) (M j) (separatingWeight α β F (q j)))^(1/K)) atTop atTop
  repeatedExtensionDiverges : ∀ K : ℝ, 1 < K →
    Tendsto (fun j => (q j : ℝ) *
      (fixedDilationPhaseBound (q j) (M j) (separatingWeight α β F (q j)))^(1/K)) atTop atTop
  repeatedEndpoint :
    Tendsto (fun j => (q j : ℝ) *
      (fixedDilationPhaseBound (q j) (M j) (separatingWeight α β F (q j)))^(1/(1 : ℝ)))
      atTop (𝓝 0)

/-- The comparison of the bounds following Proposition A.1. Both
fixed-shift estimates are obtained from the same Teräväinen exponent,
and the repeated-input estimate is treated separately at its endpoint. -/
theorem appendixA_count_comparison
    (hKMTT : KMTTLocalInverse) (hTer : TeravainenFixedFamily)
    (hGT : ProductHeisenbergObstruction) (hScalar : ScalarHeisenbergObstruction)
    (hBernstein : BernsteinCircleLipschitzFourier)
    (hG : ∀ S : ℕ, 3 ≤ S → NormalizedGowersLaws S)
    {α β : ℝ} (hα : BadlyApproximable α) {r : ℕ → ℕ}
    (hr : AdmissibleBetaDenominators β r) (F : C(Circle, ℂ))
    {κ : ℝ≥0} (hF : LipschitzWith κ F) (hNonconstant : ∃ x y : Circle, F x ≠ F y) :
    SeparatingCountComparison α β F (fun j => separatingModulus (r j))
      (fun j => separatingLength (r j) (r (j+1))) := by
  let q : ℕ → ℕ := fun j => separatingModulus (r j)
  let M : ℕ → ℕ := fun j => separatingLength (r j) (r (j+1))
  let v : ℕ → ℤ → ℂ := fun j => separatingWeight α β F (q j)
  let E : ℕ → ℝ := fun j => fixedDilationPhaseBound (q j) (M j) (v j)
  have hScale := eventually_separatingScale hr
  have hM := tendsto_separatingLength hr
  have hClaims := separatingFamily_of_obstructions hGT hScalar hBernstein hG hα hr F hF hNonconstant
  obtain ⟨L,hL,hLower⟩ := hClaims.globalPhaseLower
  have hsizes : ∀ᶠ j : ℕ in atTop, 0 < q j ∧
      (Real.log (r j : ℝ))^2/8 ≤ Real.log (q j : ℝ) :=
    hScale.mono fun _ hj => ⟨hj.q_pos,hj.log_q_lower⟩
  refine ⟨separatingCount_of_kmtt hKMTT hGT hScalar hα hr F hF, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨D₀,hD₀⟩ := (isCompact_univ (X := Circle)).exists_bound_of_continuousOn
      ((F.continuous.sub continuous_const :
        Continuous (fun z => F z-circleMean F)).continuousOn)
    let D := max 1 D₀
    have hD : 1 ≤ D := le_max_left _ _
    have hBound (j : ℕ) (y : ℤ) : ‖v j y‖ ≤ D :=
      (hD₀ _ (Set.mem_univ _)).trans (le_max_right _ _)
    obtain ⟨K,C,hK,hC,hBoth⟩ := separatingFixedFamily_bounds_of_bounded hTer
    refine ⟨K,C*D,hK,by positivity,?_⟩
    filter_upwards [hScale] with j hj
    exact hBoth (q j) (M j) hj.q_pos hj.M_pos D (v j) hD (fun y _ => hBound j y)
  · intro c σ hc hσ
    exact separating_phaseNorm_loss_tendsto q M r v hr.1.tendsto_atTop
      hsizes hL hc hσ hLower
  · intro K hK
    have hK' : 0 < K := zero_lt_one.trans_le hK
    have hk : 1/K < (2 : ℝ) := ((div_le_one hK').mpr hK).trans_lt (by norm_num)
    simpa only [Real.rpow_two] using
      separating_fixedDilationBound_tendsto q M r v hr.1.tendsto_atTop hsizes hL hK hk hLower
  · intro K hK
    have hK' : 0 < K := zero_lt_one.trans hK
    have hk : 1/K < (1 : ℝ) := (div_lt_one hK').mpr hK
    simpa only [Real.rpow_one] using
      separating_fixedDilationBound_tendsto q M r v hr.1.tendsto_atTop hsizes hL hK.le hk hLower
  · have hNormZero := separatingGlobalPhase_tendsto_zero hClaims.localPhaseUpper
      (hScale.mono fun _ hj => hj.q_le_M) hM
    have hInv : Tendsto (fun j : ℕ => (M j : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hM)
    have hEq : (fun j => (q j : ℝ)*(E j)^(1/(1 : ℝ))) =ᶠ[atTop]
        (fun j => (M j : ℝ)⁻¹+phaseNorm 3 (positiveInterval (M j)) (v j)) :=
      hScale.mono fun j hj => repeatedDilationPhaseBound_one hj.q_pos (v j)
    apply (tendsto_congr' hEq).mpr
    simpa only [zero_add] using hInv.add hNormZero

end NilBohr
