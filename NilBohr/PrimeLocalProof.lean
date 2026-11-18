import NilBohr.PrimeCramerPhase
import NilBohr.PrimeCutoff
import NilBohr.PrimeModelReplacement
import NilBohr.ConditionalPointwise

/-! Assembly of the prime-weighted phase estimate and its pointwise consequences. -/

open Filter MeasureTheory
open scoped Topology BigOperators NNReal ENNReal

namespace NilBohr

/-- The literature inputs used in the prime-weighted phase estimate.
The chart forms of the two Green–Tao obstructions are stated separately
in the assumption catalogue. -/
structure PrimePhaseLiteratureInputs (c₀ : ℝ) : Prop where
  banks : BanksRealZeroBound
  ambient : KMTTAmbientPrimeModel c₀
  gowers : ∀ S, 3 ≤ S → NormalizedGowersLaws S
  bernstein : BernsteinCircleLipschitzFourier
  mertens : MertensIntervalProductBound
  sieve : FundamentalSieveLemma
  scalarObstruction : ScalarHeisenbergObstruction
  productObstruction : ProductHeisenbergObstruction

private theorem log_neg_rpow_prime_variable_le {d : ℕ} (hd : 0 < d)
    {T U A : ℝ} (hT : 0 < T) (hA : 0 ≤ A) (h : T/(2*(d : ℝ)) ≤ U) :
    U^(-A) ≤ (2*(d : ℝ))^A*T^(-A) := by
  have hd' : 0 < 2*(d : ℝ) := by positivity
  refine (Real.rpow_le_rpow_of_exponent_nonpos (div_pos hT hd') h (neg_nonpos.mpr hA)).trans_eq ?_
  rw [Real.div_rpow hT.le hd'.le, Real.rpow_neg hd'.le, div_inv_eq_mul, mul_comm]

private theorem phaseAverage_add_weight (P : Finset ℤ) (f g : ℤ → ℂ) (p : Polynomial ℝ) :
    phaseAverage P (fun m => f m+g m) p = phaseAverage P f p+phaseAverage P g p := by
  simp only [phaseAverage, add_mul, Finset.sum_add_distrib, add_div]

set_option maxHeartbeats 1400000 in
/-- Proposition 6.2, with the three analytic contributions assembled before
taking the supremum over ordinary polynomial phases. The constants and
large-scale cutoff are independent of the interval, residue and phase. -/
theorem primeLocalPhase_of_literature {c₀ : ℝ} (hc₀ : 0 < c₀) (hc₁ : c₀ < 1/11)
    (hLit : PrimePhaseLiteratureInputs c₀)
    {α β : ℝ} (hα : BadlyApproximable α) {denom : ℕ → ℕ}
    (hβ : AdmissibleBetaDenominators β denom) {d : ℕ} (hd : 0 < d)
    (F : Circle → ℂ) {κ : ℝ≥0} (hF : LipschitzWith κ F) :
    PrimeLocalPhase d (heisenbergPhase α β) F := by
  intro A K L B hA hK hL
  have hB : (0 : ℝ) ≤ B := Nat.cast_nonneg _
  let E := A+2
  have hE : 0 < E := by dsimp [E]; positivity
  have hc₁' : c₀ < 1 := hc₁.trans (by norm_num)
  let Fc : C(Circle, ℂ) := ⟨F, hF.continuous⟩
  obtain ⟨C₁,hC₁,hSeam⟩ := primeProgression_mangoldt_seam_error hLit.scalarObstruction
    hα hβ hd B K L A hB hK.le hL hA F hF.continuous
  obtain ⟨C₂,hC₂,hReplace⟩ := primeModelReplacement_log_saving_of_kmtt hc₀ hc₁
    hLit.banks hLit.ambient hLit.bernstein hd (hLit.gowers _ (le_max_left _ _)) Fc κ hF
    (B := (B : ℝ)) hB hK.le hL.le hA hE
  obtain ⟨C₃,hC₃,hCramer⟩ := primeCramerPhase_log_saving hLit.mertens hLit.sieve
    hLit.productObstruction hLit.scalarObstruction hα hβ hc₀ hc₁' hd hB hK.le hL hA hE F hF
  obtain ⟨c,hc,hSizes⟩ := primeProgression_sieve_scales hd B K L hB hK.le hL.le
  have hLogN : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  let C := (C₁+C₂+C₃)*(2*(d : ℝ))^A
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp
    (hSeam.and (hReplace.and (hCramer.and (hSizes.and (hLogN.eventually_ge_atTop 1)))))
  refine ⟨N₀,?_⟩
  intro N q hN hq hqL
  have hq' : 0 < q := hq
  obtain ⟨hSeam,hReplace,hCramer,hSizes,hLogN'⟩ := hN₀ N hN
  let M := parameterLength N q d
  let X := q*M+1
  change ∀ (l r u : ℤ) (b : ℕ), b ≤ B → _ 
  intro l r u b hb hI hIcard
  have hb' : (b : ℝ) ≤ B := by exact_mod_cast hb
  let P := localProgression l r u (q^b)
  let P' := P.image (fun y => (q : ℤ)*y+1)
  let t := Real.log (X : ℝ)
  let ε := t^(-E)
  let f : ℤ → ℂ := fun m => F (heisenbergPhase α β (m-1) : Circle)-circleMean F
  let ucut : ℤ → ℂ := fun m => heisenbergCenteredTest F ε (heisenbergOrbit α β (m-1))
  let Q := cramerCutoff c₀ X
  let g : ℤ → ℂ := fun m => mangoldtWeight m * f m
  obtain ⟨hCard,_,hLogLow,_,hCardLower,_⟩ := hSizes hq' hqL hb' hI hIcard
  have ht : 0 < t := (div_pos (zero_lt_one.trans_le hLogN') (by positivity)).trans_le hLogLow
  have hPos : 0 < (P'.card : ℝ) :=
    (show 0 < c*(X : ℝ)*t^(-(K+((B : ℝ)+1)*L)) by dsimp [X]; positivity).trans_le hCardLower
  have hPos' : 0 < P'.card := by exact_mod_cast hPos
  have hP : P.Nonempty := by
    apply Finset.card_pos.mp
    rw [← hCard]
    exact hPos'
  refine ⟨hP,?_⟩
  have hTests (p : Polynomial ℝ) (hp : p.natDegree ≤ d) :
      ‖phaseAverage P' g p‖ ≤ (C₁+C₂+C₃)*t^(-A) := by
    let term₁ : ℤ → ℂ := fun m => mangoldtWeight m * (f m - ucut m)
    let term₂ : ℤ → ℂ := fun m => (mangoldtWeight m-cramerWeight Q m)*ucut m
    let term₃ : ℤ → ℂ := fun m => cramerWeight Q m*ucut m
    have hSplit : g = fun m => term₁ m + (term₂ m + term₃ m) := by
      funext m
      dsimp [g,term₁,term₂,term₃]
      ring
    have h₁ : ‖phaseAverage P' term₁ p‖ ≤ C₁*t^(-A) :=
      hSeam hq' hqL hb' hI hIcard p
    have h₂ : ‖phaseAverage P' term₂ p‖ ≤ C₂*t^(-A) :=
      hReplace hq' hqL hb' hI hIcard α β p hp
    have h₃ : ‖phaseAverage P' term₃ p‖ ≤ C₃*t^(-A) :=
      hCramer hq' hqL hb' hI hIcard p hp
    rw [hSplit, phaseAverage_add_weight, phaseAverage_add_weight]
    calc
      _ ≤ ‖phaseAverage P' term₁ p‖ +
        (‖phaseAverage P' term₂ p‖ + ‖phaseAverage P' term₃ p‖) :=
        (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
      _ ≤ _ := by linarith only [h₁,h₂,h₃]
  have hNorm : phaseNorm (d+1) P' g ≤ (C₁+C₂+C₃)*t^(-A) := by
    unfold phaseNorm
    refine csSup_le ⟨‖phaseAverage P' g 0‖,0,by simp,rfl⟩ ?_
    rintro v ⟨p,hp,rfl⟩
    exact hTests p (Nat.le_of_lt_succ hp)
  have hPull : phaseNorm (d+1) P (fun y => g ((q : ℤ)*y+1)) ≤ _ :=
    (primeProgression_phaseNorm_le_affine_image (by omega) hq' P g).trans hNorm
  have hWeight : (fun y : ℤ => (lambdaModulus q y : ℂ) *
        (selectorWeight (heisenbergPhase α β) F q y - circleMean F)) =
      fun y => (totientNormalize q : ℂ)*g ((q : ℤ)*y+1) := by
    funext y
    simp only [lambdaModulus_cast_eq, g, f, add_sub_cancel_right, selectorWeight, mul_assoc]
  rw [hWeight]
  refine (phaseNorm_const_mul_le (by omega) P _ _).trans ?_
  rw [Complex.norm_real, Real.norm_of_nonneg (totientNormalize_nonneg q)]
  calc
    _ ≤ phaseNorm (d+1) P (fun y => g ((q : ℤ)*y+1)) :=
      mul_le_of_le_one_left (phaseNorm_nonneg_of_pos (by omega) P _) (totientNormalize_le_one hq')
    _ ≤ (C₁+C₂+C₃)*t^(-A) := hPull
    _ ≤ C*(Real.log N)^(-A) := by
      have h := log_neg_rpow_prime_variable_le hd (zero_lt_one.trans_le hLogN') hA.le hLogLow
      simpa only [C,mul_assoc] using mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ C₁+C₂+C₃)

/-- The uniform Proposition 6.2 with the admissibility predicate from the
manuscript, in the form used by the ergodic deductions. -/
theorem heisenbergPrimeLocalPhase_of_literature
    {c₀ : ℝ} (hc₀ : 0 < c₀) (hc₁ : c₀ < 1/11) (hLit : PrimePhaseLiteratureInputs c₀) :
    ∀ α β : ℝ, BadlyApproximable α → AdmissibleBeta β →
      ∀ d : ℕ, 0 < d → ∀ F : Circle → ℂ,
        (∃ κ : ℝ≥0, LipschitzWith κ F) → PrimeLocalPhase d (heisenbergPhase α β) F := by
  rintro α β hα hβ d hd F ⟨κ,hF⟩
  obtain ⟨_,_,r,hr⟩ := (admissibleBeta_iff_exists_denominators β).mp hβ
  exact primeLocalPhase_of_literature hc₀ hc₁ hLit hα hr hd F hF

/-- Proposition 7.1 from the same prime-phase literature and the ergodic inputs. -/
theorem smoothErgodicComparison_of_literature
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    {c₀ : ℝ} (hc₀ : 0 < c₀) (hc₁ : c₀ < 1/11) (hLit : PrimePhaseLiteratureInputs c₀)
    (hTer : TeravainenFixedFamily) (hPNT : PrimeNumberTheorem)
    {α β : ℝ} (hα : BadlyApproximable α) (hβ : AdmissibleBeta β)
    {ℓ d : ℕ} (hd : 0 < d) (P : Fin ℓ → Polynomial ℤ) (hP : ErgodicPolynomialFamily P)
    (hdeg : ∀ i, (P i).natDegree ≤ d) (htop : ∃ i, (P i).natDegree = d)
    (F : Circle → ℂ) {κ : ℝ≥0} (hF : LipschitzWith κ F)
    (T : ProbabilitySystem X μ) (f : Fin ℓ → X → ℂ) (hf : ∀ i, MemLp (f i) ∞ μ) :
    SmoothErgodicComparison T P f (heisenbergPhase α β) F :=
  smoothErgodicComparison_of_primeLocalPhase hTer hPNT hd P hP hdeg htop
    (heisenbergPhase α β) F hF.continuous
    (heisenbergPrimeLocalPhase_of_literature hc₀ hc₁ hLit α β hα hβ d hd F ⟨κ,hF⟩) T f hf

/-- Theorem 1.4 with all original prime-phase deductions discharged. -/
theorem heisenberg_pointwise_of_literature
    (X : Type*) [MeasurableSpace X] {c₀ : ℝ} (hc₀ : 0 < c₀) (hc₁ : c₀ < 1/11)
    (hLit : PrimePhaseLiteratureInputs c₀)
    (hPNT : PrimeNumberTheorem) (hMWW : MirekWanWrightPointwise X)
    (hTer : TeravainenFixedFamily) :
    PrimePointwiseFor X heisenbergPhase :=
  primePointwiseFor_of_primeLocalPhase hPNT hMWW hTer heisenbergPhase
    (heisenbergPrimeLocalPhase_of_literature hc₀ hc₁ hLit)

/-- Corollary 1.5 with all original prime-phase deductions discharged. -/
theorem bracket_pointwise_of_literature
    (X : Type*) [MeasurableSpace X] {c₀ : ℝ} (hc₀ : 0 < c₀) (hc₁ : c₀ < 1/11)
    (hLit : PrimePhaseLiteratureInputs c₀) (hV : VinogradovPrimeEquidistribution)
    (hPNT : PrimeNumberTheorem) (hMWW : MirekWanWrightPointwise X)
    (hTer : TeravainenFixedFamily) :
    PrimePointwiseFor X bracketPhase :=
  bracket_pointwise_of_primeLocalPhase X hV hPNT hMWW hTer
    (heisenbergPrimeLocalPhase_of_literature hc₀ hc₁ hLit)

end NilBohr
