import NilBohr.InverseTestBound
import NilBohr.LocalPhaseSubstitution
import NilBohr.ParameterPartition
import NilBohr.ShortIntervalChoice

/-! The full local generalized von Neumann estimate from KMTT Lemma 3.4. -/

open Polynomial
open scoped BigOperators

namespace NilBohr

theorem one_le_localShiftBound {C : ℝ} (hC : 1 ≤ C) {d : ℕ} (hd : 0 < d) :
    1 ≤ localShiftBound C d := by
  have hC2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hC 2
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  unfold localShiftBound
  simpa using mul_le_mul
    (mul_le_mul (show (1 : ℝ) ≤ C^2 by simpa using hC2)
      (show (1 : ℝ) ≤ (d : ℝ)+1 by linarith only [hd1]) (by norm_num) (by positivity))
    hd1 (by norm_num) (by positivity)

theorem largeCountLocalTest_using_substitution
    (Hguard : ℕ → ℝ → Prop)
    (C : ℝ) (d k : ℕ) (hC : 1 ≤ C) (hd' : 0 < d) (_hk' : 0 < k)
    (Ks Ds c₁ D₁ A Vexp : ℝ) (B : ℕ)
    (hKs : 0 < Ks) (hDs : 0 < Ds) (hc₁ : 0 < c₁) (hD₁ : 0 < D₁)
    (hA : 0 < A) (hVexp : 0 < Vexp)
    (hSub : LocalPhaseSubstitutionOn Hguard C d k Ks Ds c₁ D₁ A Vexp B) :
    ∃ (K D c : ℝ), 0 < K ∧ 0 < D ∧ 0 < c ∧ LargeCountLocalTestOn Hguard C d k K D c B := by
  classical
  let Kdel := max (3*C) (5*(2*C+4)*localShiftBound C d)
  have hKdelC : 3*C ≤ Kdel := le_max_left _ _
  have hKdel : 0 ≤ Kdel := (by positivity : 0 ≤ 3*C).trans (le_max_left _ _)
  have hKdel' : 5*(2*C+4)*localShiftBound C d ≤ Kdel := le_max_right _ _
  obtain ⟨a,c,D,ha,hc,hD,hChoice⟩ :=
    choose_short_parameter_interval (ι:=Fin k) d k Kdel c₁ D₁ A Vexp A Vexp
      hKdel hc₁ hD₁.le hA hVexp.le hA hVexp.le
  obtain ⟨Ksp,hKsp,hSpace⟩ := space_bound_of_small_parameterLength d D c⁻¹
    (inv_pos.mpr hc) hd'
  let K := max Ks Ksp
  let Dmax := max Ds (max ((2*D*d : ℕ) : ℝ) (max (D : ℝ) Vexp))
  let cmax := min c (A/(12*C))
  have hK : 0 < K := hKs.trans_le (le_max_left _ _)
  have hDmax : 0 < Dmax := hDs.trans_le (le_max_left _ _)
  have hDmaxE : ((2*D*d : ℕ) : ℝ) ≤ Dmax := (le_max_left _ _).trans (le_max_right _ _)
  have hDmaxD : (D : ℝ) ≤ Dmax := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hDmaxV : Vexp ≤ Dmax := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hcmax : 0 < cmax := lt_min hc (by positivity)
  refine ⟨K,Dmax,cmax,hK,hDmax,hcmax,?_⟩
  intro N q hN hq hqLog M hM P hP htop hcoeff v f hv hf hfs δ hδ hδ' hLarge hGuard
  have hN₀ : 0 < N := by omega
  have hδ₁ : δ ≤ 1 := by linarith
  let r := A*δ^Vexp
  have hRpow {s : ℝ} (hs : s ≤ Dmax) : δ^(-s) ≤ δ^(-Dmax) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ₁ (neg_le_neg hs)
  rcases hSub N q hN hq hqLog hM P hP htop hcoeff v f hv hf hfs δ hδ hδ' hLarge hGuard with
    hSmall | ⟨hr₀,hr₁,g,V,b,γ,hg₀,hgLarge,hV⟩
  · exact Or.inl (hSmall.trans (mul_le_mul (le_max_left _ _)
      (hRpow (le_max_left _ _)) (by positivity) hK.le))
  let L := q^B
  let e := fun i : Fin k => (P i.succ).natDegree
  have hL : 0 < L := pow_pos hq _
  have he₀ (i : Fin k) : 0 < e i := (hcoeff i.succ (Fin.succ_ne_zero i)).2.2.1
  have he_d (i : Fin k) : e i ≤ d := by
    dsimp [e]
    rw [← htop]
    exact hP.2.2.2.monotone (Fin.le_last _)
  rcases hChoice q M L hq hM hL δ hδ hδ₁ hr₁ hr₁ Finset.univ
      (by simp) e V (fun i _ => ⟨he₀ i,he_d i⟩) (fun i _ => (hV i).2.1) with
      hms | ⟨H,hHeq,hH,hHM,hHlen,hDel⟩
  · have h := hSpace N q δ hN₀ hq hδ hqLog hM hms
    exact Or.inl (h.trans (mul_le_mul (le_max_right _ _)
      (hRpow hDmaxE) (by positivity) hK.le))
  refine Or.inr ?_
  let E := r/(12*C)
  have hEp : 0 < E := div_pos hr₀ (by positivity)
  have hQ : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hM₁ : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hH₁ : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hXlen : cmax*(M : ℝ)*(q : ℝ)^(-Dmax)*δ^Dmax ≤ (H : ℝ) := by
    refine le_trans (b := c*(M : ℝ)*(q : ℝ)^(-(D : ℝ))*δ^(D : ℝ)) ?_ hHlen
    have hqExp : (q : ℝ)^(-Dmax) ≤ (q : ℝ)^(-(D : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hQ (neg_le_neg hDmaxD)
    have hδExp : δ^Dmax ≤ δ^(D : ℝ) := Real.rpow_le_rpow_of_exponent_ge hδ hδ₁ hDmaxD
    have hc' : cmax ≤ c := min_le_left _ _
    have h₁ := mul_le_mul_of_nonneg_right hc' (Nat.cast_nonneg M : (0:ℝ) ≤ M)
    have h₂ := mul_le_mul h₁ hqExp (by positivity) (by positivity)
    exact mul_le_mul h₂ hδExp (by positivity) (by positivity)
  have hLower : cmax*δ^Dmax ≤ E := by
    have hc' : cmax ≤ A/(12*C) := min_le_right _ _
    calc
      _ ≤ (A/(12*C))*δ^Vexp := mul_le_mul hc'
        (Real.rpow_le_rpow_of_exponent_ge hδ hδ₁ hDmaxV) (by positivity) (by positivity)
      _ = _ := by dsimp [E,r]; ring
  apply Classical.byContradiction
  intro hBad
  have hTests : ∀ j ∈ Finset.range (M/H), ∀ a : ℤ,
      (localProgression (parameterBlockLow H j) (parameterBlockHigh H j) a L).Nonempty →
      phaseNorm (d+1) (localProgression (parameterBlockLow H j) (parameterBlockHigh H j) a L) v ≤ E := by
    intro j hj a ha
    apply le_of_not_gt
    intro he
    apply hBad
    refine ⟨parameterBlockLow H j,parameterBlockHigh H j,a,B,le_rfl,
      fullParameterBlock_subset hj,?_,ha,hLower.trans he.le⟩
    change cmax*(M : ℝ)*(q : ℝ)^(-Dmax)*δ^Dmax ≤ ((fullParameterBlock H j).card : ℝ)
    rwa [fullParameterBlock_card]
  let X := spatialInterval C N
  let U := spatialInterval (C+localShiftBound C d) N
  let R := fun i : Fin k => localShiftBound C d * (q : ℝ)^(e i - 1) *
    (M : ℝ)^(e i - 1) * (H : ℝ)
  have hSshift : 0 ≤ localShiftBound C d := zero_le_one.trans (one_le_localShiftBound hC hd')
  have hR (i : Fin k) : 1 ≤ R i := by
    dsimp [R]
    have h1 : (1 : ℝ) ≤ (q : ℝ)^(e i - 1) := one_le_pow₀ hQ
    have h2 : (1 : ℝ) ≤ (M : ℝ)^(e i - 1) := one_le_pow₀ hM₁
    calc
      _ ≤ localShiftBound C d * 1 * 1 * 1 := by simpa using one_le_localShiftBound hC hd'
      _ ≤ _ := by gcongr
  have hmove : ∀ j ∈ Finset.range (M/H), ∀ y ∈ fullParameterBlock H j, ∀ i : Fin k,
      |(((P i.succ).eval y : ℤ) : ℝ) - (((P i.succ).eval (parameterBlockLow H j) : ℤ) : ℝ)| ≤ R i := by
    intro j hj y hy i
    have hlo := parameterBlockLow_mem hH j
    exact abs_eval_sub_le_on_short_interval (hcoeff i.succ (Fin.succ_ne_zero i)) (he_d i) hM
      (fullParameterBlock_subset hj hy) (fullParameterBlock_subset hj hlo)
      (fullParameterBlock_abs_sub_le hy hlo)
  have hshift : ∀ x ∈ X, ∀ y ∈ positiveInterval M, ∀ i : Fin k,
      x + (P i.succ).eval y ∈ U := by
    intro x hx y hy i
    exact local_shift_mem_enlarged hq hd' (hcoeff i.succ (Fin.succ_ne_zero i)) (he_d i) hM hx hy
  have hBnd := norm_countingForm_le_local_tests_after_replacement hN₀ hM hH (by linarith : 0 ≤ C)
    X U (fun _ hx => hx) P hP.2.1 d L hL he_d v g hv
    (by rw [hg₀]; exact hf 0) V (fun i => (hV i).1) (fun i => (hV i).2.2.1) b γ R hR
    (fun i => (hV i).2.2.2) hmove hshift E hEp.le hTests
  have hXC : (X.card : ℝ)/(N : ℝ) ≤ 3*C := by
    apply (div_le_iff₀ (by positivity)).mpr
    exact (card_spatialInterval_bounds hC hN₀).2
  have hBoundary : (∑ i : Fin k, (5*(2*C+4))*R i / ((L*V i : ℕ) : ℝ)) ≤
      Kdel*(∑ i : Fin k, (q : ℝ)^(e i-1)*(M : ℝ)^(e i-1)*(H : ℝ)/((L : ℝ)*(V i : ℝ))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    push_cast
    dsimp [R]
    rw [show 5*(2*C+4)*(localShiftBound C d*(q : ℝ)^(e i - 1)*(M : ℝ)^(e i - 1)*(H : ℝ)) =
        (5*(2*C+4)*localShiftBound C d)*
          ((q : ℝ)^(e i - 1)*(M : ℝ)^(e i - 1)*(H : ℝ)) by ring,
      mul_div_assoc]
    exact mul_le_mul_of_nonneg_right hKdel' (by positivity)
  have hTailBoundary := add_le_add
    (mul_le_mul_of_nonneg_right (hXC.trans hKdelC)
      (by positivity : 0 ≤ (H : ℝ)/(M : ℝ))) hBoundary
  have hCost := hTailBoundary.trans hDel
  change (X.card : ℝ)/(N : ℝ)*((H : ℝ)/(M : ℝ)) +
    (∑ i : Fin k, 5*(2*C+4)*R i / ((L*V i : ℕ) : ℝ)) ≤ r/2 at hCost
  have hMain : (X.card : ℝ)/(N : ℝ)*E ≤ r/4 := by
    refine (mul_le_mul_of_nonneg_right hXC hEp.le).trans_eq ?_
    dsimp [E]
    field_simp
    ring
  change r ≤ ‖countingForm N M X P v g‖ at hgLarge
  change 0 < r at hr₀
  linarith only [hgLarge,hBnd,hMain,hCost,hr₀]

/-- A count of the manuscript's size forces a local polynomial phase test
unless the spatial scale is polynomial in the reciprocal count. -/
theorem largeCountLocalTest_of_kmtt (hKMTT : KMTTLocalInverse) : LargeCountLocalTest := by
  classical
  intro C d k hC hk
  have hk' : 0 < k := by omega
  by_cases hd : d = 0
  · refine ⟨1,1,1,0,by norm_num,by norm_num,by norm_num,?_⟩
    intro N q hN hq hqLog M hM P hP htop hcoeff
    have hLast : Fin.last k ≠ (0 : Fin (k+1)) := by
      intro h
      have hh := congrArg Fin.val h
      simp at hh
      omega
    have hDegree := (hcoeff (Fin.last k) hLast).2.2.1
    omega
  have hd' : 0 < d := Nat.pos_of_ne_zero hd
  obtain ⟨Ks,Ds,c₁,D₁,A,Vexp,B,hKs,hDs,hc₁,hD₁,hA,hVexp,hSub⟩ :=
    local_phase_substitution_of_kmtt hKMTT C d k hC hd' hk'
  obtain ⟨K,D,c,hK,hD,hc,hTest⟩ :=
    largeCountLocalTest_using_substitution (fun _ _ => True) C d k hC hd' hk'
      Ks Ds c₁ D₁ A Vexp B hKs hDs hc₁ hD₁ hA hVexp (by
        intro N q hN hq hqLog M hM P hP htop hcoeff v f hv hf hfs δ hδ hδ' hT _
        exact hSub N q hN hq hqLog hM P hP htop hcoeff v f hv hf hfs δ hδ hδ' hT)
  refine ⟨K,D,c,B,hK,hD,hc,?_⟩
  intro N q hN hq hqLog M hM P hP htop hcoeff v f hv hf hfs δ hδ hδ' hT
  exact hTest N q hN hq hqLog hM P hP htop hcoeff v f hv hf hfs δ hδ hδ' hT trivial

/-- Fixed spatial factors force a local test at every large count for
which the modulus contains the specified lcm cutoff. -/
theorem largeCountLocalTest_on_lcm_moduli (hKMTT : KMTTLocalInverse)
    (C : ℝ) (d k : ℕ) (hC : 1 ≤ C) (hd : 0 < d) (hk : 0 < k) :
    ∃ (U E K D c : ℝ) (B : ℕ), 0 < U ∧ 0 < E ∧ 0 < K ∧ 0 < D ∧ 0 < c ∧
      LargeCountLocalTestOn (LcmCutoff U E) C d k K D c B := by
  obtain ⟨U,E,Ks,Ds,c₁,D₁,A,Vexp,B,hU,hE,hKs,hDs,hc₁,hD₁,hA,hVexp,hSub⟩ :=
    local_phase_substitution_on_lcm_moduli hKMTT C d k hC hd hk
  obtain ⟨K,D,c,hK,hD,hc,hTest⟩ :=
    largeCountLocalTest_using_substitution (LcmCutoff U E) C d k hC hd hk
      Ks Ds c₁ D₁ A Vexp B hKs hDs hc₁ hD₁ hA hVexp hSub
  exact ⟨U,E,K,D,c,B,hU,hE,hK,hD,hc,hTest⟩

/-- The manuscript's full local generalized von Neumann theorem, as a
deduction from the explicit quoted KMTT unweighted inverse estimate. -/
theorem localGeneralizedVonNeumann_of_kmtt (hKMTT : KMTTLocalInverse) :
    LocalGeneralizedVonNeumann :=
  localGeneralizedVonNeumann_of_largeCountLocalTest (largeCountLocalTest_of_kmtt hKMTT)

/-- The local test estimate obtained from fixed factors with an lcm
guard at the testing threshold. -/
theorem localGeneralizedVonNeumann_on_lcm_moduli (hKMTT : KMTTLocalInverse)
    (C : ℝ) (d ℓ : ℕ) (hC : 1 ≤ C) (hd : 0 < d) (hℓ : 0 < ℓ) :
    ∃ (U E η A₁ A₂ J : ℝ) (B : ℕ),
      0 < U ∧ 0 < E ∧ 0 < η ∧ 0 < A₁ ∧ 0 < A₂ ∧ 0 < J ∧
      LocalGeneralizedVonNeumannOn (LcmCutoff U E) C d ℓ η A₁ A₂ J B := by
  by_cases hL : ℓ = 1
  · subst ℓ
    refine ⟨1,1,1,1,1,3*C,0,by norm_num,by norm_num,by norm_num,by norm_num,by norm_num,by linarith,?_⟩
    intro N q hN hq hqr M hM P hP hdeg hcoeff v f hv hf hfs ρ hρ hρ' _
    have hp : (P (1 : Fin 2)).natDegree ≤ d := by simpa using hdeg.le
    have hb := localGeneralizedVonNeumann_twoInput C N M d P v f hC (by omega) hM hP.2.1 hp hv hf hfs
    simp only [if_pos rfl, if_true, Real.rpow_one]
    refine hb.trans (mul_le_mul_of_nonneg_left ?_ (by linarith))
    have hN' : (0 : ℝ) ≤ (N : ℝ)^(-(1:ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    linarith
  obtain ⟨U,E,K,D,c,B,hU,hE,hK,hD,hc,hTest⟩ :=
    largeCountLocalTest_on_lcm_moduli hKMTT C d ℓ hC hd hℓ
  obtain ⟨η,A₁,A₂,J,hη,hA₁,hA₂,hJ,hVN⟩ :=
    localGeneralizedVonNeumann_using_largeCountLocalTest (LcmCutoff U E)
      (lcmCutoff_mono hU.le hE.le) C d ℓ hC hL K D c B hK hD hc hTest
  exact ⟨U,E,η,A₁,A₂,J,B,hU,hE,hη,hA₁,hA₂,hJ,hVN⟩

end NilBohr
