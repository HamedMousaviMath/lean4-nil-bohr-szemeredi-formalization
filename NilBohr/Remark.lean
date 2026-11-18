import NilBohr.CenteredHeisenbergEstimate
import NilBohr.LocalGeneralized

/-! The fixed-factor proof of the centered count used in density increment. -/

open scoped NNReal

namespace NilBohr

/-- Remark 1.6 on the moduli reached by the density iteration. An initial
lcm divisor supplies the common step in all unweighted inverse calls. -/
theorem centeredSelectorComparison_on_lcm_moduli (hInv : KMTTLocalInverse)
    {c₀ cRel C : ℝ}
    (hc₀ : 0 < c₀) (hc₀' : c₀ < 1/11) (hcRel : 0 < cRel) (hcRel' : cRel ≤ 1/10)
    (hC : 1 ≤ C) {d ℓ : ℕ} (hd : 0 < d) (hℓ : 0 < ℓ)
    {α β : ℝ} (F : Circle → ℂ) (hF : Continuous F)
    (hphase : ∃ r : ℕ → ℕ, AdmissibleBetaDenominators β r ∧
      CenteredHeisenbergPhaseEstimate d (heisenbergPhase α β) F r) :
    ∃ (A : ℝ) (w₀ : ℕ), 0 < A ∧ 16 ≤ w₀ ∧
      CenteredSelectorComparisonAt (fun q w => initialModulus w ∣ q)
        c₀ cRel C w₀ d ℓ (heisenbergPhase α β) F A := by
  obtain ⟨U,E,η,A₁,A₂,K,B,hU,hE,hη,hA₁,hA₂,hK,hVN⟩ :=
    localGeneralizedVonNeumann_on_lcm_moduli hInv C d ℓ hC hd hℓ
  let A := (2*E)⁻¹
  have hA : 0 < A := by dsimp [A]; positivity
  let w₀ := max 16 ⌈max (U^2) ((2 : ℝ)^A⁻¹)⌉₊
  have hw₀ : 16 ≤ w₀ := le_max_left _ _
  have hLower (w : ℕ) (hw : w₀ ≤ w) :
      max (U^2) ((2 : ℝ)^A⁻¹) ≤ (w : ℝ) := by
    have h := (le_max_right 16 ⌈max (U^2) ((2 : ℝ)^A⁻¹)⌉₊).trans hw
    exact (Nat.le_ceil _).trans (by exact_mod_cast h)
  refine ⟨A,w₀,hA,hw₀,?_⟩
  apply centeredSelectorComparison_using_local_phase (LcmCutoff U E)
    (fun q w => initialModulus w ∣ q) hc₀ hc₀' hcRel hcRel' hC hw₀ hd hℓ
    hη hA₁ hA₂ hK hVN A hA (fun w => (w : ℝ)^(-A)) ?_ ?_ F hF hphase
  · intro w hw
    have hw₁ : (1 : ℝ) ≤ w := by exact_mod_cast (show 1 ≤ w by omega)
    have hwPos := zero_lt_one.trans_le hw₁
    refine ⟨by positivity,?_,Real.rpow_le_rpow_of_exponent_le hw₁ (by linarith),le_rfl⟩
    have hPower := Real.rpow_le_rpow (by positivity : 0 ≤ (2 : ℝ)^A⁻¹)
      ((le_max_right _ _).trans (hLower w hw)) hA.le
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), inv_mul_cancel₀ hA.ne',
      Real.rpow_one] at hPower
    change (w : ℝ)^(-A) ≤ 1/2
    rw [Real.rpow_neg hwPos.le, one_div]
    exact (inv_le_inv₀ (by positivity) (by norm_num)).mpr hPower
  · intro q w hw hDiv
    have hw₁ : (1 : ℝ) ≤ w := by exact_mod_cast (show 1 ≤ w by omega)
    have hwPos := zero_lt_one.trans_le hw₁
    have hHalf : A*E = 1/2 := by
      dsimp [A]
      field_simp
      ring
    have hSq : ((w : ℝ)^(1/2 : ℝ))^2 = w := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hwPos.le]
      norm_num
    have hRoot : U ≤ (w : ℝ)^(1/2 : ℝ) := by
      apply le_of_pow_le_pow_left₀ (n := 2) (by omega) (by positivity)
      rw [hSq]
      exact (le_max_left _ _).trans (hLower w hw)
    apply lcmCutoff_of_le_cutoff (by positivity) _ hDiv
    rw [← Real.rpow_mul hwPos.le, neg_mul_neg, hHalf]
    exact (mul_le_mul_of_nonneg_right hRoot (by positivity)).trans_eq (by simpa only [pow_two] using hSq)

/-- Remark 1.6 with the centered phase estimates supplied by the explicit
scalar and product quantitative obstruction inputs. -/
theorem centeredSelectorComparison_on_lcm_moduli_of_obstructions
    (hInv : KMTTLocalInverse) (hGT : ProductHeisenbergObstruction)
    (hScalar : ScalarHeisenbergObstruction)
    {c₀ cRel C : ℝ}
    (hc₀ : 0 < c₀) (hc₀' : c₀ < 1/11) (hcRel : 0 < cRel) (hcRel' : cRel ≤ 1/10)
    (hC : 1 ≤ C) {d ℓ : ℕ} (hd : 0 < d) (hℓ : 0 < ℓ)
    {α β : ℝ} (hα : BadlyApproximable α) (hβ : AdmissibleBeta β)
    (F : Circle → ℂ) {κ : ℝ≥0} (hF : LipschitzWith κ F) :
    ∃ (A : ℝ) (w₀ : ℕ), 0 < A ∧ 16 ≤ w₀ ∧
      CenteredSelectorComparisonAt (fun q w => initialModulus w ∣ q)
        c₀ cRel C w₀ d ℓ (heisenbergPhase α β) F A := by
  obtain ⟨_, _, r, hr⟩ := (admissibleBeta_iff_exists_denominators β).mp hβ
  exact centeredSelectorComparison_on_lcm_moduli hInv hc₀ hc₀' hcRel hcRel' hC hd hℓ
    F hF.continuous ⟨r,hr,centeredHeisenbergPhaseEstimate_of_obstructions hGT hScalar hα hr d F hF⟩

end NilBohr
