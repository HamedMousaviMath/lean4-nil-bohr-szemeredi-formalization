import NilBohr.HeisenbergCutoff
import NilBohr.RelativeSelectorProof

/-! Removal of the horizontal seam cutoff in the centered phase estimate. -/

open Filter AddCircle MeasureTheory Metric Polynomial Set
open scoped BigOperators NNReal Topology

namespace NilBohr

set_option maxHeartbeats 1800000 in
/-- Removing the chart seam from the twisted estimate gives the centered
part, equation (24) of the manuscript. The three input properties describe
the localized test before any arithmetic averaging. -/
theorem centeredHeisenbergPhaseEstimate_of_chart_test
    (hGT : ProductHeisenbergObstruction) (hScalar : ScalarHeisenbergObstruction)
    {α β : ℝ} (hα : BadlyApproximable α) {r : ℕ → ℕ} (hr : AdmissibleBetaDenominators β r)
    (d : ℕ) (F : Circle → ℂ) (hF : Continuous F)
    (Φ : ℝ → HeisenbergPoint → ℂ)
    (hLip : ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε →
      HeisenbergLipschitzNormLE (Φ ε) (C*(1+ε⁻¹)))
    (hMean : ∀ ε x y, (∫ z in (0 : ℝ)..1, Φ ε (x,y,z)) = 0)
    (hOrbit : ∀ ε n, Φ ε (heisenbergOrbit α β n) =
      (min 1 (max 0 ((‖((β*(n:ℝ):ℝ):Circle)‖-ε)/ε)) : ℝ) *
        (F (heisenbergPhase α β n : Circle) - circleMean F)) :
    CenteredHeisenbergPhaseEstimate d (heisenbergPhase α β) F r := by
  obtain ⟨C, hC, hLip⟩ := hLip
  obtain ⟨B₀, hB₀⟩ := (isCompact_univ (X := Circle)).exists_bound_of_continuousOn
    ((hF.sub continuous_const : Continuous (fun x => F x - circleMean F)).continuousOn)
  let B := max 1 B₀
  have hB : 0 ≤ B := zero_le_one.trans (le_max_left _ _)
  intro A hA
  obtain ⟨D, hD, hAperture⟩ := heisenberg_seamAverage_of_horizontal
    (horizontalCircleEstimate_of_scalar hScalar α β hα hr) (show 0 < A+1 by positivity)
  have hTwist := twisted_heisenberg_log_saving hGT hScalar hα hr d hA
    (show 0 < A+2 by positivity)
  refine ⟨2+B*D, by positivity, ?_⟩
  filter_upwards [hAperture, hTwist, Real.tendsto_log_atTop.eventually_ge_atTop 1,
    Real.tendsto_log_atTop.eventually_ge_atTop (2*C)] with xScale hs ht hLog hLogC
  intro j hjlo hjhi a v K hv hvX hvCop hK
  let logX := Real.log xScale
  let ε := logX^(-(A+1))
  have hlog : 1 ≤ logX := hLog
  have hlog₀ : 0 < logX := zero_lt_one.trans_le hlog
  have hε : 0 < ε := Real.rpow_pos_of_pos hlog₀ _
  have heq_inv : ε⁻¹ = logX^(A+1) := by
    dsimp [ε]
    rw [Real.rpow_neg hlog₀.le, inv_inv]
  have hLipBound : C*(1+ε⁻¹) ≤ logX^(A+2) := by
    have hpow : 1 ≤ logX^(A+1) := Real.one_le_rpow hlog (by positivity)
    calc
      C*(1+ε⁻¹) ≤ C*2*logX^(A+1) := by
        rw [heq_inv, mul_assoc]
        exact mul_le_mul_of_nonneg_left (by linarith only [hpow]) hC.le
      _ ≤ logX*logX^(A+1) := by
        exact mul_le_mul_of_nonneg_right (by linarith only [hLogC]) (Real.rpow_nonneg hlog₀.le _)
      _ = _ := by rw [show A+2 = 1+(A+1) by ring, Real.rpow_add hlog₀ 1 (A+1), Real.rpow_one]
  have hTest : HeisenbergLipschitzNormLE (Φ ε) (logX^(A+2)) := by
    obtain ⟨hInvariant, S, M, hS, hM, hSM, hSup, hDist⟩ := hLip ε hε
    exact ⟨hInvariant, S, M, hS, hM, hSM.trans hLipBound, hSup, hDist⟩
  let ψ (x : Circle) : ℝ := 1 - heisenbergSeamCutoff ε x
  let z (t : ℤ) := ((β*((a+(v:ℤ)*t : ℤ):ℝ) : ℝ) : Circle)
  let ν := (∑ t ∈ positiveInterval K, ψ (z t))/(K:ℝ)
  have hAperture : ν ≤ D*ε := hs j hjlo hjhi a v K hv hvX hvCop hK
  let w (t : ℤ) := F (heisenbergPhase α β (a+(v:ℤ)*t) : Circle) - circleMean F
  let τ (t : ℤ) := Φ ε (heisenbergOrbit α β (a+(v:ℤ)*t))
  have hw (t : ℤ) : ‖w t - τ t‖ ≤ B*ψ (z t) := by
    have hb : ‖w t‖ ≤ B := (hB₀ _ (Set.mem_univ _)).trans (le_max_right _ _)
    have ht : w t - τ t = (ψ (z t) : ℂ) * w t := by
      dsimp only [τ]
      rw [hOrbit]
      dsimp only [ψ, heisenbergSeamCutoff, z, w]
      push_cast
      ring
    have hψ₀ : 0 ≤ ψ (z t) := sub_nonneg.mpr (heisenbergSeamCutoff_bounds _ _).2
    rw [ht, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hψ₀, mul_comm B]
    exact mul_le_mul_of_nonneg_left hb hψ₀
  have hrem (P : Polynomial ℝ) :
      ‖phaseAverage (positiveInterval K) (fun t => w t - τ t) P‖ ≤ B*ν := by
    refine (norm_phaseAverage_le _ _).trans ?_
    rw [card_positiveInterval]
    refine (div_le_div_of_nonneg_right (Finset.sum_le_sum fun t _ => hw t) (Nat.cast_nonneg _)).trans_eq ?_
    rw [← Finset.mul_sum, mul_div_assoc]
  have hε_A : ε ≤ logX^(-A) := Real.rpow_le_rpow_of_exponent_le hlog (by linarith)
  change phaseNorm (d+1) (positiveInterval K) w ≤ _
  unfold phaseNorm
  apply Real.sSup_le _ (by positivity)
  rintro b ⟨P, hp, rfl⟩
  have hMain := ht j hjlo hjhi a v K hv hvX hvCop hK (Φ ε) hTest (hMean ε) P (by omega)
  have hMain' : ‖phaseAverage (positiveInterval K) τ P‖ ≤ 2*logX^(-A) := by
    change ‖phaseAverage (positiveInterval K)
      (fun t => Φ ε (heisenbergOrbit α β (a+(v:ℤ)*t))) P‖ ≤ _
    rwa [phaseAverage_eq_heisenbergTwistedSum]
  have hsplit : phaseAverage (positiveInterval K) w P =
      phaseAverage (positiveInterval K) τ P + phaseAverage (positiveInterval K) (fun t => w t - τ t) P := by
    simp only [phaseAverage, sub_mul, Finset.sum_sub_distrib, sub_div]
    abel
  rw [hsplit]
  have hremBound : B*ν ≤ B*(D*logX^(-A)) :=
    mul_le_mul_of_nonneg_left (hAperture.trans
      (mul_le_mul_of_nonneg_left hε_A (by positivity))) hB
  calc
    _ ≤ ‖phaseAverage (positiveInterval K) τ P‖ +
        ‖phaseAverage (positiveInterval K) (fun t => w t - τ t) P‖ := norm_add_le _ _
    _ ≤ 2*logX^(-A) + B*(D*logX^(-A)) :=
      add_le_add hMain' ((hrem P).trans hremBound)
    _ = _ := by change _ = (2+B*D)*logX^(-A); ring

/-- Equation (24) of Proposition 4.3 for every natural degree bound and
fixed Lipschitz circle test, from the specialized scalar and product forms
of the quantitative horizontal obstruction. -/
theorem centeredHeisenbergPhaseEstimate_of_obstructions
    (hGT : ProductHeisenbergObstruction) (hScalar : ScalarHeisenbergObstruction)
    {α β : ℝ} (hα : BadlyApproximable α) {r : ℕ → ℕ} (hr : AdmissibleBetaDenominators β r)
    (d : ℕ) (F : Circle → ℂ) {κ : ℝ≥0} (hF : LipschitzWith κ F) :
    CenteredHeisenbergPhaseEstimate d (heisenbergPhase α β) F r :=
  centeredHeisenbergPhaseEstimate_of_chart_test hGT hScalar hα hr d F hF.continuous
    (heisenbergCenteredTest F) (heisenbergCenteredTest_lipschitz F hF)
    (heisenbergCenteredTest_verticalMean_zero F hF) (heisenbergCenteredTest_orbit F · α β)

/-- Theorem 3.2 from the cited quantitative inputs, including the product
form of the Green–Tao obstruction. -/
theorem relativeSelectorComparison_of_obstructions {c₀ C : ℝ}
    (hc₀ : 0 < c₀) (hc₀' : c₀ < 1/11) (hC : 1 ≤ C)
    {d ℓ : ℕ} (hd : 0 < d) (hℓ : 0 < ℓ) (hExt : SelectorLiteratureInputs c₀)
    (hGT : ProductHeisenbergObstruction)
    {α β : ℝ} (hα : BadlyApproximable α) (hβ : AdmissibleBeta β)
    (F : C(Circle, ℂ)) (κF : ℝ≥0) (hF : LipschitzWith κF F) :
    RelativeSelectorComparison c₀ C d ℓ (heisenbergPhase α β) F := by
  obtain ⟨_, _, r, hr⟩ := (admissibleBeta_iff_exists_denominators β).mp hβ
  exact relativeSelectorComparison_of_centered_phase hc₀ hc₀' hC hd hℓ hExt hα hr F κF hF
    (centeredHeisenbergPhaseEstimate_of_obstructions hGT hExt.scalarObstruction hα hr d F hF)

/-- Theorem 1.2 conditional on the explicitly stated literature inputs and
specialized Green–Tao obstruction interfaces. -/
theorem heisenbergRecurrence_of_obstructions {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hc₀' : c₀ < 1/11) (hExt : SelectorLiteratureInputs c₀)
    (hWeak : KMTTLocalWeakRegularity) (hGT : ProductHeisenbergObstruction) :
    HeisenbergRecurrence := by
  apply heisenbergRecurrence_of_centered_phase hc₀ hc₀' hExt hWeak
  intro d α β _ hα hβ F κ hF
  obtain ⟨_, _, r, hr⟩ := (admissibleBeta_iff_exists_denominators β).mp hβ
  exact ⟨r, hr, centeredHeisenbergPhaseEstimate_of_obstructions hGT hExt.scalarObstruction hα hr d F hF⟩

/-- Corollary 1.3 under the same explicit inputs. -/
theorem bracketRecurrence_of_obstructions {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hc₀' : c₀ < 1/11) (hExt : SelectorLiteratureInputs c₀)
    (hWeak : KMTTLocalWeakRegularity) (hGT : ProductHeisenbergObstruction) :
    BracketRecurrence :=
  bracket_recurrence_of_heisenberg_recurrence
    (heisenbergRecurrence_of_obstructions hc₀ hc₀' hExt hWeak hGT)

end NilBohr
