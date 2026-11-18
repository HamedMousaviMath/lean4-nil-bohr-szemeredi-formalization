import NilBohr.CenteredHeisenbergEstimate
import NilBohr.GreenTaoObstructions

open Filter MeasureTheory
open scoped NNReal Topology

namespace NilBohr

/-- Proposition 4.3, equations (22)–(24), on the same admissible sequence
of denominators. The chart mean equals the nilmanifold Haar mean, and the
unit chart condition represents zero vertical mean. The first two bounds
hold for every natural degree bound, including zero. -/
theorem heisenbergPhaseEstimates_of_quantitativeLeibman
    (hGT : GreenTaoQuantitativeLeibman) {α β : ℝ}
    (hα : BadlyApproximable α) (hβ : AdmissibleBeta β) :
    ∃ r : ℕ → ℕ, AdmissibleBetaDenominators β r ∧
      (∀ᶠ X : ℝ in atTop, ∃ j : ℕ,
        (r j : ℝ) ≤ X^(1/100 : ℝ) ∧ X^(1/100 : ℝ) < (r (j+1) : ℝ)) ∧
      (∀ (d : ℕ) (A L : ℝ), 0 < A → 0 < L → ∀ᶠ X : ℝ in atTop,
        ∀ j : ℕ, (r j : ℝ) ≤ X^(1/100 : ℝ) → X^(1/100 : ℝ) < (r (j+1) : ℝ) →
        ∀ (a : ℤ) (v K : ℕ), (v : ℝ) ≤ X^(1/10000 : ℝ) → ¬ r j ∣ v →
        X^(1/2 : ℝ) ≤ (K : ℝ) →
        ∀ Φ : HeisenbergPoint → ℂ, HeisenbergLipschitzNormLE Φ (Real.log X ^ L) →
        ‖heisenbergOrbitAverage α β a v 1 K Φ - heisenbergChartMean Φ‖ ≤ Real.log X ^ (-A) ∧
        ((∀ x ∈ Set.Ico (0 : ℝ) 1, ∀ y ∈ Set.Ico (0 : ℝ) 1,
          (∫ z in (0 : ℝ)..1, Φ (x,y,z)) = 0) →
          phaseNorm (d+1) (positiveInterval K)
            (fun t => Φ (heisenbergOrbit α β (a+(v : ℤ)*t))) ≤ 2*Real.log X ^ (-A))) ∧
      ∀ (d : ℕ) (F : Circle → ℂ) (κ : ℝ≥0), LipschitzWith κ F →
        CenteredHeisenbergPhaseEstimate d (heisenbergPhase α β) F r := by
  obtain ⟨_, _, r, hr⟩ := (admissibleBeta_iff_exists_denominators β).mp hβ
  have hScalar := scalarHeisenbergObstruction_of_greenTao hGT
  have hProduct := productHeisenbergObstruction_of_greenTao hGT
  refine ⟨r, hr, (heisenberg_horizontal_for_denominators α β hα hr).1, ?_, ?_⟩
  · intro d A L hA hL
    filter_upwards [eventually_ge_atTop (2 : ℝ),
      scalar_heisenberg_equidistribution_for_denominators hScalar α β hα hr
        (A+L) 0 (add_pos hA hL),
      twisted_heisenberg_phaseNorm hProduct hScalar hα hr d hA hL]
      with X hX hEquidistribution hTwist
    intro j hj₀ hj₁ a v K hvX hvr hK Φ hΦ
    have hv : 0 < v := by
      apply Nat.pos_of_ne_zero
      intro hv₀
      exact hvr (hv₀ ▸ dvd_zero (r j))
    refine ⟨?_, fun hMean => hTwist j hj₀ hj₁ a v K hv hvX hvr hK Φ hΦ hMean⟩
    have hXone : 1 ≤ X := by linarith
    have hlog : 0 < Real.log X := Real.log_pos (by linarith)
    have hv' := hvX.trans (Real.rpow_le_rpow_of_exponent_le hXone
      (by norm_num : (1/10000 : ℝ) ≤ 1/5000))
    have hK' := (Real.rpow_le_rpow_of_exponent_le hXone
      (by norm_num : (1/3 : ℝ) ≤ 1/2)).trans hK
    have h := hEquidistribution j hj₀ hj₁ a v 1 K hv hv' hvr
      (by decide) (by simp) hK' Φ _ hΦ
    rwa [← Real.rpow_add hlog, show -(A+L)+L = -A by ring] at h
  · exact fun d F _ hF => centeredHeisenbergPhaseEstimate_of_obstructions
      hProduct hScalar hα hr d F hF

end NilBohr
