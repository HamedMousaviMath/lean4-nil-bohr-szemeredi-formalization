import NilBohr.PrimeProgressions
import NilBohr.TwistedEstimates

/-! The good-divisor progression application in Proposition 6.2. -/

open Filter MeasureTheory
open scoped Topology BigOperators

namespace NilBohr

/-- Changing from the divisor-progression average to the ambient progression
average contributes exactly the divisor-progression density. -/
theorem norm_phaseAverage_divisor_indicator_le {D : ℕ} (P : Finset ℤ)
    (g : ℤ → ℂ) (p : Polynomial ℝ) {ε : ℝ}
    (h : ‖phaseAverage (P.filter (fun m => (D : ℤ) ∣ m)) g p‖ ≤ ε) :
    ‖phaseAverage P (fun m => if (D : ℤ) ∣ m then g m else 0) p‖ ≤
      ((P.filter (fun m => (D : ℤ) ∣ m)).card : ℝ)/(P.card : ℝ)*ε := by
  classical
  let P₀ := P.filter (fun m => (D : ℤ) ∣ m)
  have hs : (∑ m ∈ P, (if (D : ℤ) ∣ m then g m else 0)*phase (-p.eval (m : ℝ))) =
      ∑ m ∈ P₀, g m*phase (-p.eval (m : ℝ)) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro m _
    split_ifs <;> simp
  change _ ≤ (P₀.card : ℝ)/(P.card : ℝ)*ε
  by_cases hEmpty : P₀.card = 0
  · rw [phaseAverage, hs, Finset.card_eq_zero.mp hEmpty]
    simp [hEmpty]
  · have hZero : (P₀.card : ℂ) ≠ 0 := by exact_mod_cast hEmpty
    have heq : phaseAverage P (fun m => if (D : ℤ) ∣ m then g m else 0) p =
        ((P₀.card : ℂ)/(P.card : ℂ))*phaseAverage P₀ g p := by
      simp only [phaseAverage, hs]
      rw [mul_comm ((P₀.card : ℂ)/(P.card : ℂ)), div_mul_div_comm,
        mul_comm (P₀.card : ℂ) (P.card : ℂ),
        mul_div_mul_right _ _ hZero]
    rw [heq, norm_mul, norm_div, Complex.norm_natCast, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left h (by positivity)

/-- Evaluation of the test under the integer reindexing of the sifted interval. -/
theorem phaseAverage_primeDivisor_eq_heisenbergTwistedSum
    (α β : ℝ) (Φ : HeisenbergPoint → ℂ) (z : ℤ) {v : ℕ} (hv : 0 < v)
    (H : ℕ) (p : Polynomial ℝ) :
    let L : Polynomial ℝ := Polynomial.C (z : ℝ) + Polynomial.C (v : ℝ)*Polynomial.X
    phaseAverage ((positiveInterval H).image (fun t => z+(v : ℤ)*t))
      (fun m => Φ (heisenbergOrbit α β (m-1))) p =
      heisenbergTwistedSum Φ α β (z-1) (v : ℤ) H
        (fun t => (p.comp L).eval (t : ℝ)) / (H : ℂ) := by
  let f : ℤ → ℤ := fun t => z+(v : ℤ)*t
  let L : Polynomial ℝ := Polynomial.C (z : ℝ) + Polynomial.C (v : ℝ)*Polynomial.X
  have hvZ : (v : ℤ) ≠ 0 := by exact_mod_cast hv.ne'
  have hinj : Function.Injective f := fun t u h => mul_left_cancel₀ hvZ (add_left_cancel h)
  change phaseAverage ((positiveInterval H).image f) _ p =
    heisenbergTwistedSum Φ α β (z-1) (v : ℤ) H
      (fun t => (p.comp L).eval (t : ℝ)) / (H : ℂ)
  rw [phaseAverage, Finset.card_image_of_injective _ hinj, card_positiveInterval,
    Finset.sum_image (fun _ _ _ _ h => hinj h), sum_positiveInterval_eq_zero_prefix]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  have hOrbit : f ((t : ℤ)+1)-1 = z-1+(v : ℤ)*((t : ℤ)+1) := by dsimp [f]; ring
  have hPoly : L.eval ((t+1 : ℕ) : ℝ) = ((f ((t : ℤ)+1) : ℤ) : ℝ) := by
    simp [L,f, Int.cast_add, Int.cast_mul, Nat.cast_add]
  simp only [heisenbergTwistedSum, hOrbit, Polynomial.eval_comp, hPoly]

set_option maxHeartbeats 1000000 in
/-- For the denominator selected at the prime scale, all sieve divisors
coprime to the original step and indivisible by that denominator inherit
the twisted Heisenberg saving. The input function is a chart test with the
already established quotient Lipschitz bound and zero vertical mean. -/
theorem primeDivisors_heisenberg_log_saving
    (hGT : ProductHeisenbergObstruction) (hScalar : ScalarHeisenbergObstruction)
    {α β : ℝ} (hα : BadlyApproximable α) {denom : ℕ → ℕ}
    (hβ : AdmissibleBetaDenominators β denom)
    {d : ℕ} (hd : 0 < d) {B K L A E : ℝ}
    (hB : 0 ≤ B) (hK : 0 ≤ K) (hL : 0 < L) (hA : 0 < A) (hE : 0 < E) :
    ∀ᶠ N : ℕ in atTop, ∀ {q b : ℕ} {l r u : ℤ}, 0 < q →
      (q : ℝ) ≤ (Real.log N)^L → (b : ℝ) ≤ B →
      let M := parameterLength N q d
      let X := q*M+1
      Finset.Icc l r ⊆ positiveInterval M →
      (M : ℝ)*(Real.log N)^(-K) ≤ ((Finset.Icc l r).card : ℝ) →
      let P' := (localProgression l r u (q^b)).image (fun y => (q : ℤ)*y+1)
      ∃ j : ℕ, (denom j : ℝ) ≤ (X : ℝ)^(1/100 : ℝ) ∧
        (X : ℝ)^(1/100 : ℝ) < (denom (j+1) : ℝ) ∧
        ∀ {D : ℕ}, 0 < D → (D : ℝ) ≤ (X : ℝ)^(1/20000 : ℝ) →
          (q^(b+1)).Coprime D → ¬ denom j ∣ D →
          ∀ Φ : HeisenbergPoint → ℂ, HeisenbergLipschitzNormLE Φ ((Real.log X)^E) →
          (∀ x y, (∫ z in (0 : ℝ)..1, Φ (x,y,z)) = 0) →
          ∀ p : Polynomial ℝ, p.natDegree ≤ d →
          let P₀ := P'.filter (fun m => (D : ℤ) ∣ m)
          ‖phaseAverage P₀ (fun m => Φ (heisenbergOrbit α β (m-1))) p‖ ≤
            2*(Real.log (X : ℝ))^(-A) := by
  obtain ⟨hExist,hLarge,_⟩ := heisenberg_horizontal_for_denominators α β hα hβ
  have hConst : 0 < (2*(d : ℝ))^L := by positivity
  have hTwist := twisted_heisenberg_log_saving_for_denominators hGT hScalar hα hβ hd hA hE
  obtain ⟨X₀,hX₀⟩ := eventually_atTop.1 (hExist.and ((hLarge L _ hL hConst).and hTwist))
  obtain ⟨_,_,hSizes⟩ := primeProgression_sieve_scales hd B K L hB hK hL.le
  have hNt : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hPrime : ∀ j, (denom j).Prime := by
    obtain ⟨_,_,_,hp,_⟩ := hβ
    exact fun j => (hp j).1
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  filter_upwards [hSizes, hNt.eventually_ge_atTop (2*(d : ℝ)*Real.log (max 1 X₀)),
    hNt.eventually_ge_atTop 1] with N hSizes hNlarge hNpos
  intro q b l r u hq hqL hb
  let M := parameterLength N q d
  let X := q*M+1
  change Finset.Icc l r ⊆ positiveInterval M → _
  intro hI hIc
  obtain ⟨_,_,hScale,_,_,hSieve⟩ := hSizes hq hqL hb hI hIc
  change Real.log (N : ℝ)/(2*(d : ℝ)) ≤ Real.log (X : ℝ) at hScale
  have hXR : (0 : ℝ) < X := by change (0 : ℝ) < ((q*M+1 : ℕ) : ℝ); positivity
  have hT : Real.log (N : ℝ) ≤ 2*(d : ℝ)*Real.log (X : ℝ) := by
    convert (div_le_iff₀ (show 0 < 2*(d : ℝ) by positivity)).mp hScale using 1
    ring
  have hXlarge : X₀ ≤ (X : ℝ) := by
    have h₁ : (0 : ℝ) < max 1 X₀ := zero_lt_one.trans_le (le_max_left _ _)
    apply (le_max_right (1 : ℝ) X₀).trans
    apply (Real.log_le_log_iff h₁ hXR).mp
    apply le_of_mul_le_mul_left _ (show 0 < 2*(d : ℝ) by positivity)
    exact hNlarge.trans hT
  obtain ⟨⟨j,hj₁,hj₂⟩,hDenom,hTwist⟩ := hX₀ (X : ℝ) hXlarge
  have hqr : q < denom j := by
    have hqBound : (q : ℝ) ≤ (2*(d : ℝ))^L * (Real.log (X : ℝ))^L := by
      apply hqL.trans
      have htpos : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hNpos
      have hLogPos : 0 < Real.log (X : ℝ) := (div_pos htpos (by positivity)).trans_le hScale
      convert Real.rpow_le_rpow htpos.le hT hL.le using 1
      rw [Real.mul_rpow (by positivity : 0 ≤ 2*(d : ℝ)) hLogPos.le]
    exact_mod_cast hqBound.trans_lt (hDenom j hj₁ hj₂)
  refine ⟨j,hj₁,hj₂,?_⟩
  intro D hD hDupper hCo hDiv Φ hΦ hMean p hp
  obtain ⟨hStep,hLength,z,hId⟩ := hSieve hD hDupper hCo
  let v := q^(b+1)*D
  let P' := (localProgression l r u (q^b)).image (fun y => (q : ℤ)*y+1)
  let P₀ := P'.filter (fun m => (D : ℤ) ∣ m)
  let H := P₀.card
  let F : Polynomial ℝ := Polynomial.C (z : ℝ) + Polynomial.C (v : ℝ)*Polynomial.X
  change P₀ = (positiveInterval H).image (fun t => z+(v : ℤ)*t) at hId
  change ‖phaseAverage P₀ (fun m => Φ (heisenbergOrbit α β (m-1))) p‖ ≤ _
  have hF : F.natDegree ≤ 1 := Polynomial.natDegree_add_le_of_degree_le (by simp)
    ((Polynomial.natDegree_C_mul_le (v : ℝ) Polynomial.X).trans (by simp))
  have hpF : (p.comp F).natDegree ≤ d := Polynomial.natDegree_comp_le.trans
    ((Nat.mul_le_mul_left p.natDegree hF).trans (by simpa using hp))
  have hv : 0 < v := Nat.mul_pos (pow_pos hq _) hD
  have hnot : ¬ denom j ∣ v := prime_not_dvd_sieve_step hq (hPrime j) hqr hDiv
  rw [hId, phaseAverage_primeDivisor_eq_heisenbergTwistedSum α β Φ z hv H p]
  exact hTwist j hj₁ hj₂ (z-1) v H hv hStep hnot hLength Φ hΦ hMean (p.comp F) hpF

end NilBohr
