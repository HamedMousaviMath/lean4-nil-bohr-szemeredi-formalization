import NilBohr.PrimeSiftedAverage
import NilBohr.SieveLiterature
import NilBohr.HeisenbergCutoff
import NilBohr.PrimeDivisorOscillation

/-! The Cramér-weighted full centered selector at polylogarithmic moduli. -/

open Filter MeasureTheory
open scoped Topology BigOperators NNReal

namespace NilBohr

/-- Eventual bounds at the prime-variable scale remain uniform over all
polylogarithmic original moduli. -/
theorem eventually_primeScale {d : ℕ} (hd : 0 < d) {L : ℝ} (hL : 0 ≤ L)
    {P : ℕ → Prop} (hP : ∀ᶠ X : ℕ in atTop, P X) :
    ∀ᶠ N : ℕ in atTop, ∀ q : ℕ, 0 < q → (q : ℝ) ≤ (Real.log N)^L →
      P (q*parameterLength N q d+1) := by
  obtain ⟨X₀, hStart⟩ := eventually_atTop.mp hP
  let Y := max X₀ 1
  have hY : 0 < Y := lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)
  have hLogN : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [primeProgression_log_scales hd 0 0 L le_rfl le_rfl hL,
    hLogN.eventually_ge_atTop (2*(d : ℝ)*Real.log (Y : ℝ))] with N hScale hLarge
  intro q hq hqL
  let X := q*parameterLength N q d+1
  have hX : (0 : ℝ) < X := by dsimp [X]; positivity
  have hYreal : (0 : ℝ) < Y := by exact_mod_cast hY
  have hdreal : (0 : ℝ) < 2*(d : ℝ) := by positivity
  have hscale := (hScale (b := 0) hq hqL (by simp)).2.2.2.1
  have hlog : Real.log (Y : ℝ) ≤ Real.log (X : ℝ) := by
    apply le_trans _ hscale
    apply (le_div_iff₀ hdreal).mpr
    simpa only [mul_comm (Real.log (Y : ℝ))] using hLarge
  have hYX : Y ≤ X := by
    exact_mod_cast (Real.log_le_log_iff hYreal hX).mp hlog
  exact hStart X ((le_max_left X₀ 1).trans hYX)

set_option maxHeartbeats 1600000 in
/-- The sifted contribution to Proposition 6.2. The full centered cutoff
test has zero vertical mean, so good-divisor cancellation is uniform in
the polynomial phase without a truncation of the vertical Fourier series. -/
theorem primeCramerPhase_log_saving
    (hMertens : MertensIntervalProductBound) (hSieve : FundamentalSieveLemma)
    (hGT : ProductHeisenbergObstruction) (hScalar : ScalarHeisenbergObstruction)
    {α β : ℝ} (hα : BadlyApproximable α) {denom : ℕ → ℕ}
    (hβ : AdmissibleBetaDenominators β denom)
    {c₀ : ℝ} (hc₀ : 0 < c₀) (hc₁ : c₀ < 1)
    {d : ℕ} (hd : 0 < d) {B K L A E : ℝ}
    (hB : 0 ≤ B) (hK : 0 ≤ K) (hL : 0 < L) (hA : 0 < A) (hE : 0 < E)
    (F : Circle → ℂ) {κ : ℝ≥0} (hF : LipschitzWith κ F) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop, ∀ {q b : ℕ} {l r u : ℤ}, 0 < q →
        (q : ℝ) ≤ (Real.log N)^L → (b : ℝ) ≤ B →
        let M := parameterLength N q d
        let X := q*M+1
        Finset.Icc l r ⊆ positiveInterval M →
        (M : ℝ)*(Real.log N)^(-K) ≤ ((Finset.Icc l r).card : ℝ) →
        let P' := (localProgression l r u (q^b)).image (fun y => (q : ℤ)*y+1)
        let δ := (Real.log (X : ℝ))^(-E)
        ∀ p : Polynomial ℝ, p.natDegree ≤ d →
          ‖phaseAverage P' (fun m =>
            cramerWeight (cramerCutoff c₀ X) m *
              heisenbergCenteredTest F δ (heisenbergOrbit α β (m-1))) p‖ ≤
            C*(Real.log (X : ℝ))^(-A) := by
  obtain ⟨CM, hCM, hMertens'⟩ := hMertens.eulerProduct_le_log
  obtain ⟨CL, hCL, hF'⟩ := heisenbergCenteredTest_lipschitz F hF
  obtain ⟨R₀, hBound⟩ := (isCompact_univ (X := Circle)).exists_bound_of_continuousOn
    ((hF.continuous.sub continuous_const :
      Continuous (fun z => F z-circleMean F)).continuousOn)
  let R := max 1 R₀
  have hR : 1 ≤ R := le_max_left _ _
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hSup (z : Circle) : ‖F z-circleMean F‖ ≤ R :=
    (hBound z (Set.mem_univ _)).trans (le_max_right _ _)
  have hFixed (δ : ℝ) (g : HeisenbergPoint) : ‖heisenbergCenteredTest F δ g‖ ≤ R := by
    rw [heisenbergCenteredTest, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (heisenbergSeamCutoff_bounds δ _).1]
    exact (mul_le_mul (heisenbergSeamCutoff_bounds δ _).2 (hSup _)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  obtain ⟨_, hDenom, _⟩ := heisenberg_horizontal_for_denominators α β hα hβ
  obtain ⟨c, hc, hSizes⟩ := primeProgression_sieve_scales hd B K L hB hK hL.le
  have hCof := eventually_cramerSieve_coefficients hMertens hSieve hc₀ hc₁
    (show 0 < A+1 by positivity)
  have hDenomNat := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (hDenom (A+2) 1 (by positivity) one_pos)
  have hLogNat : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hScale := eventually_primeScale hd hL.le
    (((hCof.and (eventually_siftedPhase_error hA)).and hDenomNat).and
      (hLogNat.eventually_ge_atTop (2*CL)))
  have hTwist := primeDivisors_heisenberg_log_saving hGT hScalar hα hβ hd hB hK hL
    (A := A+2) (E := E+1) (by positivity) (by positivity)
  refine ⟨22*CM*R, by positivity, ?_⟩
  filter_upwards [hScale,hSizes,hTwist] with N hScale hSizes hTwist
  intro q b l r u hq hqL hb
  let M := parameterLength N q d
  let X := q*M+1
  change Finset.Icc l r ⊆ positiveInterval M → _
  intro hI hLength
  let P := localProgression l r u (q^b)
  let P' := P.image (fun y => (q : ℤ)*y+1)
  let t := Real.log (X : ℝ)
  let δ := t^(-E)
  let Φ := heisenbergCenteredTest F δ
  let g : ℤ → ℂ := fun m => Φ (heisenbergOrbit α β (m-1))
  let Q := cramerCutoff c₀ X
  let D := ⌊(X : ℝ)^(1/20000 : ℝ)⌋₊
  let W := cramerSieveModulus Q q
  let s := q^(b+1)
  let ε := 2*t^(-(A+2))
  have hs : 0 < s := pow_pos hq _
  obtain ⟨⟨⟨hCof, ht, hError⟩, hDenom'⟩, htL⟩ := hScale q hq hqL
  obtain ⟨hCard,hSub,_,_,hLower,hDivSize⟩ := hSizes hq hqL hb hI hLength
  obtain ⟨j,hj₁,hj₂,hCancel⟩ := hTwist hq hqL hb hI hLength
  change 1 ≤ t at ht
  have htpos := zero_lt_one.trans_le ht
  have hX : (0 : ℝ) < X := by dsimp [X]; positivity
  have hX₁ : (1 : ℝ) ≤ X := by
    exact_mod_cast (show 1 ≤ X by dsimp [X]; omega)
  have hPpos : 0 < (P'.card : ℝ) :=
    (show 0 < c*(X : ℝ)*t^(-(K+(B+1)*L)) by positivity).trans_le hLower
  have hP' : 0 < P'.card := by exact_mod_cast hPpos
  have hP : P.Nonempty := by
    apply Finset.card_pos.mp
    rw [← hCard]
    exact hP'
  obtain ⟨_,_,_,_,_,a,hAP⟩ := primeProgression_as_affine hq hI hP
  obtain ⟨hOff,hAP'⟩ := positiveProgression_eq_natImage hP'
    (fun z hz => (Finset.mem_Icc.mp (hSub hz)).1) hAP
  let off := (a+(s : ℤ)).toNat
  have hReduced (m : ℤ) (hm : m ∈ P') : m.toNat.Coprime q :=
    primeProgression_value_coprime
      (fun y hy => zero_le_one.trans (Finset.mem_Icc.mp (hI (Finset.mem_filter.mp hy).1)).1) hm
  have hCardRoot : (X : ℝ)^(1/2 : ℝ) ≤ (P'.card : ℝ) := by
    have hOne : ((1 : ℕ) : ℝ) ≤ (X : ℝ)^(1/20000 : ℝ) :=
      by simpa only [Nat.cast_one] using
        Real.one_le_rpow hX₁ (by norm_num : 0 ≤ (1/20000 : ℝ))
    obtain ⟨_, hD₁, _⟩ := hDivSize (D := 1) (by decide)
      hOne (by simp)
    change (X : ℝ)^(1/2 : ℝ) ≤ ((P'.filter (fun m => ((1 : ℕ) : ℤ) ∣ m)).card : ℝ) at hD₁
    have hFilter : P'.filter (fun m => ((1 : ℕ) : ℤ) ∣ m) = P' := by
      ext m
      simp
    rwa [hFilter] at hD₁
  have hD : (D : ℝ) ≤ (X : ℝ)^(1/20000 : ℝ) := Nat.floor_le (by positivity)
  have hr : t^(A+2) ≤ (denom j : ℝ) := by
    exact le_of_lt (by simpa only [one_mul] using hDenom' j hj₁ hj₂)
  have hr' : 0 < denom j := by exact_mod_cast (Real.rpow_pos_of_pos htpos (A+2)).trans_le hr
  obtain ⟨hQpos,hQlo,hQup⟩ := cramerCutoff_log_bounds hc₀.le (N := X) ht
  change 0 < (Q : ℝ) at hQpos
  have hQ : 2 ≤ Q := by
    by_cases h : 2 ≤ Q
    · exact h
    have h₀ : 0 < Q := by exact_mod_cast hQpos
    have he : Q = 1 := by omega
    have h₁ : 1 ≤ Real.log (Q : ℝ) := (Real.one_le_rpow ht hc₀.le).trans hQlo
    rw [he, Nat.cast_one, Real.log_one] at h₁
    norm_num at h₁
  obtain ⟨lo,hi,hWeights⟩ := hCof q
  let ds := sieveWeightDivisors W D
  have hds : ds.card ≤ D := card_sieveWeightDivisors_le W D
  have hδ : 0 < δ := Real.rpow_pos_of_pos htpos _
  have hInv : δ⁻¹ = t^E := by dsimp [δ]; rw [Real.rpow_neg htpos.le, inv_inv]
  have hLipschitz : HeisenbergLipschitzNormLE Φ (t^(E+1)) := by
    obtain ⟨hInv',S,T,hS,hT,hST,hBound',hDist⟩ := hF' δ hδ
    refine ⟨hInv',S,T,hS,hT,hST.trans ?_,hBound',hDist⟩
    have h₁ : 1 ≤ t^E := Real.one_le_rpow ht hE.le
    have h₂ : CL*(1+δ⁻¹) ≤ (2*CL)*t^E := by
      rw [hInv]
      nlinarith only [mul_nonneg hCL.le (sub_nonneg.mpr h₁)]
    calc
      _ ≤ (2*CL)*t^E := h₂
      _ ≤ t*t^E := mul_le_mul_of_nonneg_right htL (by positivity)
      _ = t^(1 : ℝ)*t^E := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add htpos, add_comm]
  have hMean (x y : ℝ) : (∫ z in (0 : ℝ)..1, Φ (x,y,z)) = 0 :=
    heisenbergCenteredTest_verticalMean_zero F hF δ x y
  change ∀ p : Polynomial ℝ, p.natDegree ≤ d →
    ‖phaseAverage P' (fun m => cramerWeight Q m * g m) p‖ ≤ (22*CM*R)*t^(-A)
  intro p hp
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hGood (l₀ : ℕ) (hl : l₀ ∈ ds) (hf : ¬denom j ∣ l₀) :
      ‖phaseAverage (P'.filter (fun m => (l₀ : ℤ) ∣ m)) g p‖ ≤ R*ε := by
    have hldiv := (mem_sieveWeightDivisors hl).1
    have hlD : (l₀ : ℝ) ≤ (X : ℝ)^(1/20000 : ℝ) :=
      (by exact_mod_cast (mem_sieveWeightDivisors hl).2 : (l₀ : ℝ) ≤ D).trans hD
    have hlpos := Nat.pos_of_dvd_of_pos hldiv (cramerSieveModulus_pos Q q)
    have hlCo := (primeStep_coprime_cramerSieveModulus Q q (b+1)).coprime_dvd_right hldiv
    exact (hCancel hlpos hlD hlCo hf Φ hLipschitz hMean p hp).trans
      (le_mul_of_one_le_left hε hR)
  have hFin := norm_cramerPhaseAverage_le_of_sieve Q q s off P'.card W D (denom j)
    hQ hs hOff hP' rfl hr' (primeStep_coprime_cramerSieveModulus Q q (b+1))
    ds (fun _ hl => mem_sieveWeightDivisors hl) lo hi g p
    (R := R) (ε := ε) (gap := t^(-(A+1))) hRpos
    hε hWeights.lowerBound hWeights.upperBound
    hWeights.bracket hWeights.gap hAP' hReduced (fun _ _ => hFixed δ _) hGood
  let w : ℝ := ∏ l ∈ primesThrough Q, (1-(l : ℝ)⁻¹)⁻¹
  have hw : 0 ≤ w := by dsimp [w]; rw [← cramerModulus_div_totient hQ]; positivity
  have hw' : w ≤ 2*CM*t := by
    refine (hMertens' Q hQ).trans ?_
    calc
      _ ≤ CM*(2*t^c₀) := mul_le_mul_of_nonneg_left hQup hCM.le
      _ ≤ CM*(2*t) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (by
          simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le ht hc₁.le) (by norm_num)) hCM.le
      _ = _ := by ring
  have htMul : t * t^(-(A+1)) = t^(-A) := by
    calc
      _ = t^(1 : ℝ)*t^(-(A+1)) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add htpos, show 1 + (-(A+1)) = -A by ring]
  refine hFin.trans ?_
  refine le_trans (mul_le_mul_of_nonneg_left
    (hError D P'.card (denom j) ds.card hD hCardRoot hr hds) (mul_nonneg hw hRpos.le)) ?_
  calc
    _ ≤ (2*CM*t)*R*(11*t^(-(A+1))) := by gcongr
    _ = _ := by
      rw [← htMul]
      ring

end NilBohr
