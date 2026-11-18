import NilBohr.DensityIncrementProof
import NilBohr.LocalBlocks
import NilBohr.ReplacementRates
import NilBohr.WeightedLocalInverse

/-! Uniform passage from the weighted local inverse to a count with all
shifted inputs replaced by spatial block phases. -/

open Polynomial
open scoped BigOperators

namespace NilBohr

noncomputable def localShiftBound (C : ℝ) (d : ℕ) : ℝ :=
  C^2 * ((d : ℝ)+1) * d

theorem mem_spatialInterval_iff {C : ℝ} {N : ℕ} {x : ℤ} :
    x ∈ spatialInterval C N ↔ |(x : ℝ)| ≤ C * N := by
  simp only [spatialInterval,Finset.mem_Icc,Int.ceil_le,Int.le_floor,abs_le,neg_mul]

theorem hasCoefficients_enlarge {C C' : ℝ} {q : ℕ} {P : Polynomial ℤ}
    (h : HasCoefficients C q P) (hle : C ≤ C') : HasCoefficients C' q P := by
  obtain ⟨hC,hq,hd,ha,hb,x,hx,hx',hP⟩ := h
  exact ⟨hC.trans hle,hq,hd,ha,fun j hj he => (hb j hj he).trans
    (mul_le_mul_of_nonneg_right hle (abs_nonneg _)),x,hx,hx'.trans hle,hP⟩

theorem local_shift_mem_enlarged {C : ℝ} {q N d : ℕ} {P : Polynomial ℤ}
    (hq : 0 < q) (hd : 0 < d)
    (hP : HasCoefficients C q P) (hdeg : P.natDegree ≤ d)
    (hM : 0 < parameterLength N q d)
    {x y : ℤ} (hx : x ∈ spatialInterval C N) (hy : y ∈ positiveInterval (parameterLength N q d)) :
    x + P.eval y ∈ spatialInterval (C + localShiftBound C d) N := by
  let M := parameterLength N q d
  let e := P.natDegree
  have hC : 1 ≤ C := hP.1
  have he : 1 ≤ e := hP.2.2.1
  have hdQ : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hdM : (1 : ℝ) ≤ M := by exact_mod_cast hM
  obtain ⟨hy1,hy2⟩ := Finset.mem_Icc.mp hy
  have hyAbs : |(y : ℝ)| ≤ M := by
    rw [abs_of_nonneg (by exact_mod_cast (show 0 ≤ y by omega))]
    exact_mod_cast hy2
  have h0 : P.eval 0 = 0 := by rw [← Polynomial.coeff_zero_eq_eval_zero]; exact hP.2.2.2.1
  have h := abs_eval_sub_le_of_hasCoefficients hP hdeg hM y 0 hyAbs (by simp)
  simp only [h0, Int.cast_zero, sub_zero] at h
  have hp : (q : ℝ)^(e-1) * (M : ℝ)^e ≤ N := by
    refine (mul_le_mul (pow_le_pow_right₀ hdQ (by omega : e-1 ≤ d-1))
      (pow_le_pow_right₀ hdM hdeg) (by positivity) (by positivity)).trans ?_
    exact parameterLength_power_le hq hd
  have heq : (M : ℝ)^(e-1) * M = (M : ℝ)^e := by
    rw [← pow_succ,(show e-1+1=e by omega)]
  have hb : |((P.eval y : ℤ) : ℝ)| ≤ localShiftBound C d * N := by
    refine h.trans ?_
    calc
      _ ≤ localShiftBound C d * (q : ℝ)^(e-1) * (M : ℝ)^(e-1) * M :=
        mul_le_mul_of_nonneg_left hyAbs (by dsimp [localShiftBound]; positivity)
      _ = localShiftBound C d * ((q : ℝ)^(e-1) * (M : ℝ)^e) := by
        dsimp [localShiftBound]
        simp [mul_assoc, heq]
      _ ≤ _ := mul_le_mul_of_nonneg_left hp (by dsimp [localShiftBound]; positivity)
  apply mem_spatialInterval_iff.mpr
  rw [Int.cast_add, add_mul]
  exact (abs_add_le _ _).trans (add_le_add (mem_spatialInterval_iff.mp hx) hb)

def LocalPhaseSubstitutionOn (Hguard : ℕ → ℝ → Prop) (C : ℝ) (d ℓ : ℕ)
    (Ksmall Dsmall c₁ D₁ a vexp : ℝ) (B : ℕ) : Prop :=
  ∀ (N q : ℕ), 3 ≤ N → 0 < q → (q : ℝ) ≤ Real.exp ((Real.log N)^(1/10 : ℝ)) →
    let M := parameterLength N q d
    0 < M →
    ∀ (P : Fin (ℓ+1) → Polynomial ℤ), FixedPolynomialFamily P →
    (P (Fin.last ℓ)).natDegree = d →
    (∀ i, i ≠ 0 → HasCoefficients C q (P i)) →
    ∀ (v : ℤ → ℂ) (f : Fin (ℓ+1) → ℤ → ℂ),
    OneBoundedOn (positiveInterval M) v →
    (∀ i, OneBoundedOn (spatialInterval C N) (f i)) →
    (∀ i, SupportedOn (spatialInterval C N) (f i)) →
    ∀ δ : ℝ, 0 < δ → δ < 1/2 → δ ≤ ‖countingForm N M (spatialInterval C N) P v f‖ →
    Hguard q δ →
    let r := a*δ^vexp
    (N : ℝ) ≤ Ksmall * δ^(-Dsmall) ∨
      0 < r ∧ r ≤ 1 ∧
      ∃ (g : Fin (ℓ+1) → ℤ → ℂ) (V : Fin ℓ → ℕ)
        (b γ : Fin ℓ → (ℤ × ℤ) → ℝ),
        g 0 = f 0 ∧
        r ≤ ‖countingForm N M (spatialInterval C N) P v g‖ ∧
        (∀ i, 0 < V i ∧ c₁*(M : ℝ)^((P i.succ).natDegree)*((q : ℝ)/r)^(-D₁) ≤ V i ∧
          q^B*V i ≤ N ∧
          g i.succ = supportedBlockPhase (spatialInterval (C + localShiftBound C d) N)
            (q^B) (V i) (b i) (γ i))

/-- Phase replacement only uses a lower threshold through the final
replacement rate. A monotone guard lets each preceding inverse call use
the same divisibility information. -/
theorem local_phase_substitution_using_inverse
    (Hguard : ℕ → ℝ → Prop) (hGuardMono : ∀ q, Monotone (Hguard q))
    (C : ℝ) (d ℓ : ℕ) (hC : 1 ≤ C) (hd : 0 < d)
    (S Ds c₁ D₁ c₂ D₂ : ℝ) (B : ℕ)
    (hS : 0 < S) (hDs : 0 < Ds) (hc₁ : 0 < c₁) (hD₁ : 0 < D₁) (hc₂ : 0 < c₂) (_hD₂ : 0 < D₂)
    (hInv : WeightedLocalInverseEstimateOn Hguard (C + localShiftBound C d) d ℓ B S Ds c₁ D₁ c₂ D₂) :
    ∃ (Ksmall Dsmall a vexp : ℝ),
      0 < Ksmall ∧ 0 < Dsmall ∧ 0 < a ∧ 0 < vexp ∧
      LocalPhaseSubstitutionOn (fun q δ => Hguard q (a*δ^vexp))
        C d ℓ Ksmall Dsmall c₁ D₁ a vexp B := by
  let C' := C + localShiftBound C d
  have hCC : C ≤ C' := by
    dsimp [C',localShiftBound]
    nlinarith [show 0 ≤ C^2 * ((d : ℝ)+1) * (d : ℝ) by positivity]
  have hC' : 1 ≤ C' := hC.trans hCC
  let K := 3*C'
  have hK : 1 ≤ K := by dsimp [K]; linarith
  have hK0 : 0 < K := by linarith
  let a₁ := min 1 c₂
  let D := max 1 D₂
  have ha₁ : 0 < a₁ := lt_min (by norm_num) hc₂
  have ha₁' : a₁ ≤ 1 := min_le_left _ _
  have ha₂ : a₁ ≤ c₂ := min_le_right _ _
  have hD : 1 ≤ D := le_max_left _ _
  have hD₂' : D₂ ≤ D := le_max_right _ _
  let a := phaseReplacementCoefficient a₁ K D ℓ
  let vexp := (2*D)^ℓ
  have ha : 0 < a := phaseReplacementCoefficient_pos ha₁ hK0 _
  have hvexp : 0 < vexp := by dsimp [vexp]; positivity
  refine ⟨S*a^(-Ds),vexp*Ds,a,vexp,by positivity,by positivity,ha,hvexp,?_⟩
  intro N q hN hq hqLog M hM P hP htop hcoeff v f hv hf hfs δ hδ hδ' hT hGuard r
  let X := spatialInterval C N
  let U := spatialInterval C' N
  have hSub : X ⊆ U := by
    intro x hx
    exact mem_spatialInterval_iff.mpr ((mem_spatialInterval_iff.mp hx).trans
      (mul_le_mul_of_nonneg_right hCC (Nat.cast_nonneg N)))
  let rates := phaseReplacementRate a₁ K D δ
  have hRates0 : ∀ j, 0 < rates j := phaseReplacementRate_pos ha₁ hK0 hδ
  have hRatesMono : Antitone rates := phaseReplacementRate_antitone ha₁ ha₁' hK hD hδ (by linarith)
  have hrEq : rates ℓ = r := rfl
  have hrpos : 0 < r := hrEq ▸ hRates0 ℓ
  have hrle : r ≤ 1 := hrEq ▸ phaseReplacementRate_le_one ha₁ ha₁' hK hD hδ (by linarith) ℓ
  have hsmEq : S*a^(-Ds)*δ^(-(vexp*Ds)) = S*r^(-Ds) := by
    change S*a^(-Ds)*δ^(-(vexp*Ds)) = S*(a*δ^vexp)^(-Ds)
    rw [Real.mul_rpow ha.le (by positivity), ← Real.rpow_mul hδ.le]
    rw [mul_neg, mul_assoc]
  rw [hsmEq]
  by_cases hsmall : (N : ℝ) ≤ S*r^(-Ds)
  · exact Or.inl hsmall
  refine Or.inr ⟨hrpos,hrle,?_⟩
  have hNorm (i : Fin (ℓ+1)) : (P i).natDegree ≤ d := by
    rw [← htop]
    exact hP.2.2.2.monotone (Fin.le_last i)
  have hZ : ∀ i, i ≠ 0 → ∀ x ∈ X, ∀ y ∈ positiveInterval M, x + (P i).eval y ∈ U := by
    intro i hi x hx y hy
    exact local_shift_mem_enlarged hq hd (hcoeff i hi) (hNorm i) hM hx hy
  let lengthCondition := fun (i : Fin (ℓ+1)) (V : ℕ) =>
    0 < V ∧ c₁*(M : ℝ)^((P i).natDegree)*((q : ℝ)/r)^(-D₁) ≤ V ∧ q^B*V ≤ N
  have hCard : (U.card : ℝ) ≤ K*N := (card_spatialInterval_bounds hC' (by omega)).2
  have hRes := replace_shifted_inputs_by_phases (by omega : 0 < N) X U P v f (q^B)
    hZ (fun i => oneBounded_of_supported (hf i) (hfs i))
    (fun i x h => hfs i x (fun hx => h (hSub hx)))
    hv hK0 hCard rates (fun j => (hRates0 j).le)
    (by simpa only [rates,phaseReplacementRate_zero] using hT) lengthCondition
  obtain ⟨g,hg₀,hgUnit,hgSupp,hgT,hgPh⟩ := hRes (by
    intro j hj G hG₀ hGUnit hGSupp hGCount i hi
    let σ := (rates j)^2/K
    have hσ : 0 < σ := div_pos (sq_pos_of_pos (hRates0 j)) hK0
    have hDual := phaseReplacementRate_succ_le_dual ha₁ ha₁' hK hD hδ (by linarith) j
    have hσlt : σ < 1/2 := by
      refine (hDual.2.trans (hRatesMono (Nat.zero_le j))).trans_lt ?_
      simpa [rates,phaseReplacementRate_zero] using hδ'
    have hσr : r ≤ σ := by
      rw [← hrEq]
      exact (hRatesMono (by omega : j+1 ≤ ℓ)).trans hDual.1
    have hSmallσ : ¬ (N : ℝ) ≤ S*σ^(-Ds) := by
      intro h
      exact hsmall (h.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_nonpos hrpos hσr (by linarith)) hS.le))
    have hEquality : countingForm N M X P v G = countingForm N M U P v G :=
      countingForm_mono_window N M hSub P hP.2.1 v G (hG₀.symm ▸ hfs 0)
    have hG' : σ ≤ ‖countingForm N M U P v G‖ := hEquality ▸ hGCount
    obtain ⟨V,b,γ,hV,hL,hVhi,hVN,hCorr⟩ := ((hInv N q hN hq hqLog hM P hP htop
      (fun i hi => hasCoefficients_enlarge (hcoeff i hi) hCC) v G
      hv (fun i x _ => hGUnit i x) hGSupp σ hσ hσlt hG'
      (hGuardMono q hσr hGuard)).resolve_left hSmallσ) i hi
    refine ⟨V,b,γ,⟨hV,?_,hVN⟩,?_⟩
    · apply le_trans _ hL
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.rpow_le_rpow_of_exponent_nonpos (div_pos (Nat.cast_pos.mpr hq) hσ)
        (div_le_div_of_nonneg_left (Nat.cast_nonneg q) hrpos hσr) (by linarith)
    · apply le_trans _ hCorr
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg N)
      rw [show rates (j+1) = a₁*σ^D from phaseReplacementRate_succ ha₁ hK0 hδ j]
      exact mul_le_mul ha₂ (Real.rpow_le_rpow_of_exponent_ge hσ (hσlt.le.trans (by norm_num))
        hD₂') (by positivity) hc₂.le)
  choose V b γ hL hG using fun i : Fin ℓ => hgPh i.succ (Fin.succ_ne_zero i)
  exact ⟨g,V,b,γ,hg₀,hrEq ▸ hgT,
    fun i => ⟨(hL i).1,(hL i).2.1,(hL i).2.2,hG i⟩⟩

/-- A large count either has small spatial scale or survives simultaneous
replacement by phases on spatial blocks. A single explicit power of the
initial threshold controls both the output count and the block lengths. -/
theorem local_phase_substitution_of_kmtt (hInv : KMTTLocalInverse)
    (C : ℝ) (d ℓ : ℕ) (hC : 1 ≤ C) (hd : 0 < d) (hℓ : 0 < ℓ) :
    ∃ (Ksmall Dsmall c₁ D₁ a vexp : ℝ) (B : ℕ),
    0 < Ksmall ∧ 0 < Dsmall ∧ 0 < c₁ ∧ 0 < D₁ ∧ 0 < a ∧ 0 < vexp ∧
    ∀ (N q : ℕ), 3 ≤ N → 0 < q → (q : ℝ) ≤ Real.exp ((Real.log N)^(1/10 : ℝ)) →
      let M := parameterLength N q d
      0 < M →
      ∀ (P : Fin (ℓ+1) → Polynomial ℤ), FixedPolynomialFamily P →
      (P (Fin.last ℓ)).natDegree = d →
      (∀ i, i ≠ 0 → HasCoefficients C q (P i)) →
      ∀ (v : ℤ → ℂ) (f : Fin (ℓ+1) → ℤ → ℂ),
      OneBoundedOn (positiveInterval M) v →
      (∀ i, OneBoundedOn (spatialInterval C N) (f i)) →
      (∀ i, SupportedOn (spatialInterval C N) (f i)) →
      ∀ δ : ℝ, 0 < δ → δ < 1/2 → δ ≤ ‖countingForm N M (spatialInterval C N) P v f‖ →
      let r := a*δ^vexp
      (N : ℝ) ≤ Ksmall * δ^(-Dsmall) ∨
        0 < r ∧ r ≤ 1 ∧
        ∃ (g : Fin (ℓ+1) → ℤ → ℂ) (V : Fin ℓ → ℕ)
          (b γ : Fin ℓ → (ℤ × ℤ) → ℝ),
          g 0 = f 0 ∧
          r ≤ ‖countingForm N M (spatialInterval C N) P v g‖ ∧
          (∀ i, 0 < V i ∧ c₁*(M : ℝ)^((P i.succ).natDegree)*((q : ℝ)/r)^(-D₁) ≤ V i ∧
            q^B*V i ≤ N ∧
            g i.succ = supportedBlockPhase (spatialInterval (C + localShiftBound C d) N)
              (q^B) (V i) (b i) (γ i)) := by
  have hC' : 1 ≤ C + localShiftBound C d := by
    have h : 0 ≤ localShiftBound C d := by dsimp [localShiftBound]; positivity
    linarith
  obtain ⟨S,Ds,c₁,D₁,c₂,D₂,B,hS,hDs,hc₁,hD₁,hc₂,hD₂,hInv⟩ :=
    weighted_local_inverse_of_kmtt hInv hC' hd hℓ
  obtain ⟨Ks,Ds',a,vexp,hKs,hDs',ha,hvexp,hSub⟩ :=
    local_phase_substitution_using_inverse (fun _ _ => True) (fun _ _ _ _ _ => trivial)
      C d ℓ hC hd S Ds c₁ D₁ c₂ D₂ B hS hDs hc₁ hD₁ hc₂ hD₂ (by
        intro N q hN hq hqLog M hM P hP htop hcoeff v f hv hf hfs δ hδ hδ' hT _
        exact hInv N q hN hq hqLog hM P hP htop hcoeff v f hv hf hfs δ hδ hδ' hT)
  refine ⟨Ks,Ds',c₁,D₁,a,vexp,B,hKs,hDs',hc₁,hD₁,ha,hvexp,?_⟩
  intro N q hN hq hqLog M hM P hP htop hcoeff v f hv hf hfs δ hδ hδ' hT
  exact hSub N q hN hq hqLog hM P hP htop hcoeff v f hv hf hfs δ hδ hδ' hT trivial

/-- The fixed-step branch of phase replacement, with one lcm guard for all
inverse calls. Its cutoff is a fixed power of the incoming count threshold. -/
theorem local_phase_substitution_on_lcm_moduli (hInv : KMTTLocalInverse)
    (C : ℝ) (d ℓ : ℕ) (hC : 1 ≤ C) (hd : 0 < d) (hℓ : 0 < ℓ) :
    ∃ (U E Ksmall Dsmall c₁ D₁ a vexp : ℝ) (B : ℕ),
      0 < U ∧ 0 < E ∧ 0 < Ksmall ∧ 0 < Dsmall ∧ 0 < c₁ ∧ 0 < D₁ ∧ 0 < a ∧ 0 < vexp ∧
      LocalPhaseSubstitutionOn (LcmCutoff U E) C d ℓ Ksmall Dsmall c₁ D₁ a vexp B := by
  have hC' : 1 ≤ C + localShiftBound C d := by
    have h : 0 ≤ localShiftBound C d := by dsimp [localShiftBound]; positivity
    linarith
  obtain ⟨a₀,A₀,b₀,B₀,b,h_a₀,h_A₀,h_b₀,h_B₀,hInv⟩ :=
    hInv (C + localShiftBound C d) d ℓ hC' hℓ
  obtain ⟨U,E,S,Ds,c₁,D₁,c₂,D₂,hU,hE,hS,hDs,hc₁,hD₁,hc₂,hD₂,hInverse⟩ :=
    weighted_local_inverse_on_lcm_moduli hC' hd
      (show KMTTLocalInverseWithExponent (C + localShiftBound C d) d ℓ b from
        ⟨a₀,A₀,b₀,B₀,h_a₀,h_A₀,h_b₀,h_B₀,hInv⟩)
  obtain ⟨Ks,Ds',a,vexp,hKs,hDs',ha,hvexp,hSub⟩ :=
    local_phase_substitution_using_inverse (LcmCutoff U E) (lcmCutoff_mono hU.le hE.le)
      C d ℓ hC hd S Ds c₁ D₁ c₂ D₂ (b+1) hS hDs hc₁ hD₁ hc₂ hD₂ (by
        intro N q hN hq hqLog M hM P hP htop hcoeff v f hv hf hfs δ hδ hδ' hT hDiv
        exact hInverse N q hN hq hqLog hM P hP htop hcoeff v f hv hf hfs δ hδ hδ' hT hDiv.2)
  refine ⟨U*a^(-E),vexp*E,Ks,Ds',c₁,D₁,a,vexp,b+1,by positivity,by positivity,
    hKs,hDs',hc₁,hD₁,ha,hvexp,?_⟩
  intro N q hN hq hqLog M hM P hP htop hcoeff v f hv hf hfs δ hδ hδ' hT hDiv
  exact hSub N q hN hq hqLog hM P hP htop hcoeff v f hv hf hfs δ hδ hδ' hT
    (lcmCutoff_at_replacementRate ha hDiv)

end NilBohr
