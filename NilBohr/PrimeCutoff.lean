import NilBohr.HeisenbergCutoff
import NilBohr.GowersComparison
import NilBohr.PrimeProgressions

/-! The Mangoldt-weighted error from removing a shrinking horizontal seam. -/

open Filter Polynomial
open scoped BigOperators Topology

namespace NilBohr

set_option maxHeartbeats 1200000 in
/-- In the shifted prime variable `m = qy + 1`, the shrinking seam contributes
at most a prescribed logarithmic error to the Mangoldt-weighted phase test.
The polynomial phase is arbitrary since this part uses only its modulus. -/
theorem primeProgression_mangoldt_seam_error
    (hScalar : ScalarHeisenbergObstruction)
    {α β : ℝ} (hα : BadlyApproximable α) {denom : ℕ → ℕ}
    (hβ : AdmissibleBetaDenominators β denom)
    {d : ℕ} (hd : 0 < d) (B K L A : ℝ)
    (hB : 0 ≤ B) (hK : 0 ≤ K) (hL : 0 < L) (hA : 0 < A)
    (F : Circle → ℂ) (hF : Continuous F) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ {q b : ℕ} {l r u : ℤ}, 0 < q →
      (q : ℝ) ≤ (Real.log N)^L → (b : ℝ) ≤ B →
      let M := parameterLength N q d
      let X := q*M+1
      Finset.Icc l r ⊆ positiveInterval M →
      (M : ℝ)*(Real.log N)^(-K) ≤ ((Finset.Icc l r).card : ℝ) →
      let P' := (localProgression l r u (q^b)).image (fun y => (q : ℤ)*y+1)
      let ε := (Real.log (X : ℝ))^(-(A+2))
      ∀ p : Polynomial ℝ,
        ‖phaseAverage P' (fun m => mangoldtWeight m *
          ((F (heisenbergPhase α β (m-1) : Circle) - circleMean F) -
            heisenbergCenteredTest F ε (heisenbergOrbit α β (m-1)))) p‖ ≤
          C*(Real.log (X : ℝ))^(-A) := by
  obtain ⟨D, hD, hSeam⟩ := heisenberg_seamAverage_of_horizontal
    (horizontalCircleEstimate_of_scalar hScalar α β hα hβ) (show 0 < A+2 by positivity)
  obtain ⟨V₀, hV₀⟩ := (isCompact_univ (X := Circle)).exists_bound_of_continuousOn
    ((hF.sub continuous_const : Continuous (fun x => F x - circleMean F)).continuousOn)
  let V := max 1 V₀
  have hV : 0 < V := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨V*D, mul_pos hV hD, ?_⟩
  obtain ⟨hDenom, hLarge, _⟩ := heisenberg_horizontal_for_denominators α β hα hβ
  have hConst : 0 < (2*(d : ℝ))^L := by positivity
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.1 (hDenom.and ((hLarge L _ hL hConst).and
    (hSeam.and (Real.tendsto_log_atTop.eventually_ge_atTop 1))))
  obtain ⟨_, _, hSizes⟩ := primeProgression_sieve_scales hd B K L hB hK hL.le
  have hNt : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hPrime : ∀ j, (denom j).Prime := by
    obtain ⟨_, _, _, hp, _⟩ := hβ
    exact fun j => (hp j).1
  filter_upwards [hSizes, hNt.eventually_ge_atTop (2*(d : ℝ)*Real.log (max 1 X₀)),
    hNt.eventually_ge_atTop 1] with N hSizes hNlarge hNpos
  intro q b l r u hq hqL hb
  let M := parameterLength N q d
  let X := q*M+1
  let P' := (localProgression l r u (q^b)).image (fun y => (q : ℤ)*y+1)
  let ε := (Real.log (X : ℝ))^(-(A+2))
  change Finset.Icc l r ⊆ positiveInterval M → _
  intro hI hIc
  dsimp only
  intro p
  obtain ⟨_, hSub, hScale, _, _, hSieve⟩ := hSizes hq hqL hb hI hIc
  change Real.log (N : ℝ)/(2*(d : ℝ)) ≤ Real.log (X : ℝ) at hScale
  have hXR : (0 : ℝ) < X := by change (0 : ℝ) < ((q*M+1 : ℕ) : ℝ); positivity
  have hX₁ : (1 : ℝ) ≤ X := by
    change (1 : ℝ) ≤ ((q*M+1 : ℕ) : ℝ)
    exact_mod_cast (by omega : 1 ≤ q*M+1)
  have hT : Real.log (N : ℝ) ≤ 2*(d : ℝ)*Real.log (X : ℝ) := by
    convert (div_le_iff₀ (show 0 < 2*(d : ℝ) by positivity)).mp hScale using 1
    ring
  have hXlarge : X₀ ≤ (X : ℝ) := by
    have h₁ : (0 : ℝ) < max 1 X₀ := zero_lt_one.trans_le (le_max_left _ _)
    apply (le_max_right (1 : ℝ) X₀).trans
    apply (Real.log_le_log_iff h₁ hXR).mp
    apply le_of_mul_le_mul_left _ (show 0 < 2*(d : ℝ) by positivity)
    exact hNlarge.trans hT
  obtain ⟨⟨j, hj₁, hj₂⟩, hDenomLarge, hSeamX, hLog⟩ := hX₀ (X : ℝ) hXlarge
  have hqr : q < denom j := by
    have hqBound : (q : ℝ) ≤ (2*(d : ℝ))^L * (Real.log (X : ℝ))^L := by
      apply hqL.trans
      have htpos : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hNpos
      have hLogPos : 0 < Real.log (X : ℝ) := zero_lt_one.trans_le hLog
      convert Real.rpow_le_rpow htpos.le hT hL.le using 1
      rw [Real.mul_rpow (by positivity : 0 ≤ 2*(d : ℝ)) hLogPos.le]
    exact_mod_cast hqBound.trans_lt (hDenomLarge j hj₁ hj₂)
  let v := q^(b+1)
  have hv : 0 < v := pow_pos hq _
  have hNoDiv : ¬ denom j ∣ v := by
    simpa only [mul_one] using (prime_not_dvd_sieve_step (b := b) (D := 1) hq
      (hPrime j) hqr (fun h => (hPrime j).ne_one (Nat.dvd_one.mp h)))
  have hOne : ((1 : ℕ) : ℝ) ≤ (X : ℝ)^(1/20000 : ℝ) := by
    simpa only [Nat.cast_one] using (Real.one_le_rpow hX₁ (by positivity : 0 ≤ (1/20000 : ℝ)))
  obtain ⟨hStep, hLength, z, hId⟩ := hSieve (D := 1) Nat.one_pos hOne (Nat.coprime_one_right _)
  simp only [Nat.cast_one, Int.one_dvd, Finset.filter_True, mul_one] at hStep hLength hId
  change P' = (positiveInterval P'.card).image (fun t => z + (v : ℤ)*t) at hId
  let ξ (m : ℤ) : ℝ := 1 - heisenbergSeamCutoff ε ((β * ((m-1 : ℤ) : ℝ) : ℝ) : Circle)
  have hAperture : (∑ m ∈ P', ξ m)/(P'.card : ℝ) ≤ D*ε := by
    have hvZ : (v : ℤ) ≠ 0 := by exact_mod_cast hv.ne'
    have hInject : Function.Injective (fun t : ℤ => z + (v : ℤ)*t) :=
      fun _ _ he => mul_left_cancel₀ hvZ (add_left_cancel he)
    have hSum : (∑ m ∈ P', ξ m) = ∑ t ∈ positiveInterval P'.card, ξ (z+(v:ℤ)*t) := by
      conv_lhs => rw [hId]
      rw [Finset.sum_image (fun _ _ _ _ he => hInject he)]
    rw [hSum]
    simpa only [ξ, show ∀ t : ℤ, z+(v:ℤ)*t-1 = z-1+(v:ℤ)*t by intro t; ring] using
      hSeamX j hj₁ hj₂ (z-1) v P'.card hv hStep hNoDiv hLength
  let w (m : ℤ) := F (heisenbergPhase α β (m-1) : Circle) - circleMean F
  let τ (m : ℤ) := heisenbergCenteredTest F ε (heisenbergOrbit α β (m-1))
  have hξ (m : ℤ) : 0 ≤ ξ m := sub_nonneg.mpr (heisenbergSeamCutoff_bounds _ _).2
  have hrem (m : ℤ) : ‖w m - τ m‖ ≤ V*ξ m := by
    have hwm : ‖w m‖ ≤ V := (hV₀ _ (Set.mem_univ _)).trans (le_max_right _ _)
    have hEq : w m - τ m = (ξ m : ℂ) * w m := by
      dsimp only [τ, ξ]
      rw [heisenbergCenteredTest_orbit]
      dsimp only [w]
      push_cast
      ring
    rw [hEq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hξ m), mul_comm V]
    exact mul_le_mul_of_nonneg_left hwm (hξ m)
  have hMangoldt (m : ℤ) (hm : m ∈ P') : ‖mangoldtWeight m‖ ≤ Real.log (X : ℝ) := by
    obtain ⟨hm₁, hmX⟩ := Finset.mem_Icc.mp (hSub hm)
    have hmcast : (m.toNat : ℝ) = (m : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg (show 0 ≤ m by omega)
    rw [mangoldtWeight, Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    apply ArithmeticFunction.vonMangoldt_le_log.trans
    rw [hmcast]
    exact Real.log_le_log (by exact_mod_cast (show 0 < m by omega)) (by exact_mod_cast hmX)
  change ‖phaseAverage P' (fun m => mangoldtWeight m * (w m - τ m)) p‖ ≤ _
  apply (norm_phaseAverage_le _ _).trans
  calc
    _ ≤ (∑ m ∈ P', Real.log (X : ℝ)*V*ξ m)/(P'.card : ℝ) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro m hm
      rw [norm_mul, mul_assoc]
      exact mul_le_mul (hMangoldt m hm) (hrem m) (norm_nonneg _)
        (zero_le_one.trans hLog)
    _ = Real.log (X : ℝ)*V*((∑ m ∈ P', ξ m)/(P'.card : ℝ)) := by
      rw [← Finset.mul_sum, mul_div_assoc]
    _ ≤ Real.log (X : ℝ)*V*(D*ε) :=
      mul_le_mul_of_nonneg_left hAperture (by positivity)
    _ ≤ V*D*(Real.log (X : ℝ))^(-A) := by
      have hεpow : Real.log (X : ℝ)*ε = (Real.log (X : ℝ))^(-A-1) := by
        dsimp only [ε]
        rw [show -A-1 = 1 + -(A+2) by ring,
          Real.rpow_add (zero_lt_one.trans_le hLog), Real.rpow_one]
      rw [show Real.log (X : ℝ)*V*(D*ε) = V*D*(Real.log (X : ℝ)*ε) by ring, hεpow]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hLog (by linarith))
        (mul_nonneg hV.le hD.le)

end NilBohr
