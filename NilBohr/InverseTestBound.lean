import NilBohr.DifferenceWitnesses
import NilBohr.TwoInput

/-! Passing from the large-count assertion to the local von Neumann bound. -/

open scoped BigOperators
open Polynomial

namespace NilBohr

theorem phaseNorm_nonneg {s : ℕ} (hs : 0 < s) (I : Finset ℤ) (v : ℤ → ℂ) :
    0 ≤ phaseNorm s I v :=
  (norm_nonneg (phaseAverage I v 0)).trans
    (norm_phaseAverage_le_phaseNorm v 0 (by simpa using hs))

theorem phaseNorm_le_one {s : ℕ} (hs : 0 < s) (I : Finset ℤ) (v : ℤ → ℂ)
    (hv : OneBoundedOn I v) : phaseNorm s I v ≤ 1 := by
  unfold phaseNorm
  apply csSup_le
  · exact ⟨‖phaseAverage I v 0‖, 0, by simpa using hs, rfl⟩
  · rintro _ ⟨P, _, rfl⟩
    have hsum : (∑ y ∈ I, ‖v y‖) ≤ (I.card : ℝ) := by
      simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using
        Finset.sum_le_sum (s := I) (g := fun _ => (1 : ℝ)) (fun y hy => hv y hy)
    have h := norm_phaseAverage_le (I := I) v P
    by_cases hI : I.card = 0
    · simpa [hI] using (h.trans (by simp [hI]))
    · exact h.trans ((div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hI)).mpr hsum)

theorem phaseNorm_le_localPhaseNorm {d M q B : ℕ} {A₁ A₂ ρ : ℝ} {v : ℤ → ℂ}
    (hv : OneBoundedOn (positiveInterval M) v) {l r u : ℤ} {b : ℕ}
    (hb : b ≤ B) (hI : Finset.Icc l r ⊆ positiveInterval M)
    (hlen : (M : ℝ) * (q : ℝ)^(-A₁) * ρ^A₂ ≤ ((Finset.Icc l r).card : ℝ))
    (hn : (localProgression l r u (q^b)).Nonempty) :
    phaseNorm (d+1) (localProgression l r u (q^b)) v ≤ localPhaseNorm d M q B A₁ A₂ ρ v := by
  apply le_csSup
  · refine ⟨1,?_⟩
    rintro _ ⟨l',r',u',b',_,hI',_,_,rfl⟩
    exact phaseNorm_le_one (by omega) _ v
      (fun y hy => hv y (hI' (Finset.mem_filter.mp hy).1))
  · exact ⟨l,r,u,b,hb,hI,hlen,hn,rfl⟩

theorem localPhaseNorm_nonneg {d M q B : ℕ} (hM : 0 < M) (hq : 0 < q)
    {A₁ A₂ ρ : ℝ} (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    (hρ : 0 < ρ) (hρ' : ρ ≤ 1) (v : ℤ → ℂ) (hv : OneBoundedOn (positiveInterval M) v) :
    0 ≤ localPhaseNorm d M q B A₁ A₂ ρ v := by
  have hQ : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqA := Real.rpow_le_one_of_one_le_of_nonpos hQ (neg_nonpos.mpr hA₁)
  have hρA := Real.rpow_le_one hρ.le hρ' hA₂
  have hlen : (M : ℝ) * (q : ℝ)^(-A₁) * ρ^A₂ ≤ ((Finset.Icc 1 (M : ℤ)).card : ℝ) := by
    have hcard : (Finset.Icc 1 (M : ℤ)).card = M := by simp [Int.card_Icc]
    rw [hcard,mul_assoc]
    simpa using (mul_le_mul_of_nonneg_left
      (mul_le_one₀ hqA (Real.rpow_nonneg hρ.le _) hρA) (Nat.cast_nonneg M))
  have hn : (localProgression 1 (M : ℤ) 0 (q^0)).Nonempty := by
    refine ⟨1,?_⟩
    simp [localProgression, Int.ModEq, show (1 : ℤ) ≤ M by exact_mod_cast hM]
  exact (phaseNorm_nonneg (s:=d+1) (by omega) _ v).trans
    (phaseNorm_le_localPhaseNorm hv (b:=0) (Nat.zero_le B) (fun _ h => h) hlen hn)

private theorem exists_half_pow_le {c : ℝ} (hc : 0 < c) :
    ∃ E : ℝ, 0 < E ∧ (1/2 : ℝ)^E ≤ c := by
  let E := max 1 (-Real.log c / Real.log 2)
  have hlog2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  refine ⟨E, (show (0 : ℝ) < 1 by norm_num).trans_le (le_max_left _ _), ?_⟩
  apply (Real.rpow_le_iff_le_log (by norm_num) hc).2
  rw [Real.log_div (by norm_num) (by norm_num),Real.log_one,zero_sub]
  have h := (div_le_iff₀ hlog2).mp (le_max_right (1:ℝ) (-Real.log c / Real.log 2))
  linarith only [h]

/-- The direct estimate follows from the inverse large-count assertion.
The latter is an internal proof target for the longer-family part of Theorem 4.2. -/
def LargeCountLocalTest : Prop :=
  ∀ (C : ℝ) (d ℓ : ℕ), 1 ≤ C → 2 ≤ ℓ →
  ∃ (K D c : ℝ) (B : ℕ), 0 < K ∧ 0 < D ∧ 0 < c ∧
  ∀ (N q : ℕ), 3 ≤ N → 0 < q → (q : ℝ) ≤ Real.exp ((Real.log N) ^ (1 / 10 : ℝ)) →
    let M := parameterLength N q d
    0 < M →
    ∀ (P : Fin (ℓ + 1) → Polynomial ℤ), FixedPolynomialFamily P →
    (P (Fin.last ℓ)).natDegree = d → (∀ i, i ≠ 0 → HasCoefficients C q (P i)) →
    ∀ (v : ℤ → ℂ) (f : Fin (ℓ + 1) → ℤ → ℂ),
    OneBoundedOn (positiveInterval M) v →
    (∀ i, OneBoundedOn (spatialInterval C N) (f i)) →
    (∀ i, SupportedOn (spatialInterval C N) (f i)) →
    ∀ δ : ℝ, 0 < δ → δ < 1/2 → δ ≤ ‖countingForm N M (spatialInterval C N) P v f‖ →
    (N : ℝ) ≤ K * δ^(-D) ∨
      ∃ (l r u : ℤ) (b : ℕ), b ≤ B ∧ Finset.Icc l r ⊆ positiveInterval M ∧
        c * (M : ℝ) * (q : ℝ)^(-D) * δ^D ≤ ((Finset.Icc l r).card : ℝ) ∧
        (localProgression l r u (q^b)).Nonempty ∧
        c * δ^D ≤ phaseNorm (d+1) (localProgression l r u (q^b)) v

def LargeCountLocalTestOn (Hguard : ℕ → ℝ → Prop) (C : ℝ) (d ℓ : ℕ)
    (K D c : ℝ) (B : ℕ) : Prop :=
  ∀ (N q : ℕ), 3 ≤ N → 0 < q → (q : ℝ) ≤ Real.exp ((Real.log N) ^ (1 / 10 : ℝ)) →
    let M := parameterLength N q d
    0 < M →
    ∀ (P : Fin (ℓ + 1) → Polynomial ℤ), FixedPolynomialFamily P →
    (P (Fin.last ℓ)).natDegree = d → (∀ i, i ≠ 0 → HasCoefficients C q (P i)) →
    ∀ (v : ℤ → ℂ) (f : Fin (ℓ + 1) → ℤ → ℂ),
    OneBoundedOn (positiveInterval M) v →
    (∀ i, OneBoundedOn (spatialInterval C N) (f i)) →
    (∀ i, SupportedOn (spatialInterval C N) (f i)) →
    ∀ δ : ℝ, 0 < δ → δ < 1/2 → δ ≤ ‖countingForm N M (spatialInterval C N) P v f‖ → Hguard q δ →
    (N : ℝ) ≤ K * δ^(-D) ∨
      ∃ (l r u : ℤ) (b : ℕ), b ≤ B ∧ Finset.Icc l r ⊆ positiveInterval M ∧
        c * (M : ℝ) * (q : ℝ)^(-D) * δ^D ≤ ((Finset.Icc l r).card : ℝ) ∧
        (localProgression l r u (q^b)).Nonempty ∧
        c * δ^D ≤ phaseNorm (d+1) (localProgression l r u (q^b)) v

def LocalGeneralizedVonNeumannOn (Hguard : ℕ → ℝ → Prop) (C : ℝ) (d ℓ : ℕ)
    (η A₁ A₂ K : ℝ) (B : ℕ) : Prop :=
  ∀ (N q : ℕ), 3 ≤ N → 0 < q → (q : ℝ) ≤ Real.exp ((Real.log N) ^ (1 / 10 : ℝ)) →
    let M := parameterLength N q d
    0 < M →
    ∀ (P : Fin (ℓ + 1) → Polynomial ℤ), FixedPolynomialFamily P →
    (P (Fin.last ℓ)).natDegree = d → (∀ i, i ≠ 0 → HasCoefficients C q (P i)) →
    ∀ (v : ℤ → ℂ) (f : Fin (ℓ + 1) → ℤ → ℂ),
    OneBoundedOn (positiveInterval M) v →
    (∀ i, OneBoundedOn (spatialInterval C N) (f i)) →
    (∀ i, SupportedOn (spatialInterval C N) (f i)) →
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 / 2 → Hguard q ρ →
      ‖countingForm N M (spatialInterval C N) P v f‖ ≤
        K * ((N : ℝ) ^ (-η) + ρ +
          (if ℓ = 1 then phaseNorm (d + 1) (positiveInterval M) v
            else localPhaseNorm d M q B A₁ A₂ ρ v) ^ η)

theorem localGeneralizedVonNeumann_using_largeCountLocalTest
    (Hguard : ℕ → ℝ → Prop) (hGuardMono : ∀ q, Monotone (Hguard q))
    (C : ℝ) (d ℓ : ℕ) (hC : 1 ≤ C) (hL : ℓ ≠ 1)
    (K D c : ℝ) (B : ℕ) (hK : 0 < K) (hD : 0 < D) (hc : 0 < c)
    (hInv : LargeCountLocalTestOn Hguard C d ℓ K D c B) :
    ∃ η A₁ A₂ J : ℝ, 0 < η ∧ 0 < A₁ ∧ 0 < A₂ ∧ 0 < J ∧
      LocalGeneralizedVonNeumannOn Hguard C d ℓ η A₁ A₂ J B := by
  obtain ⟨E,hE,hHalf⟩ := exists_half_pow_le hc
  let A₂ := D+E
  let J := (12*C) * max 1 (max (K^D⁻¹) ((c⁻¹)^D⁻¹))
  have hJ : 0 < J := by dsimp [J]; positivity
  refine ⟨D⁻¹,D,A₂,J,inv_pos.mpr hD,hD,by dsimp [A₂]; positivity,hJ,?_⟩
  intro N q hN hq hqr M hM P hP hdeg hcoeff v f hv hf hfs ρ hρ hρ' hGuard
  let T := ‖countingForm N M (spatialInterval C N) P v f‖
  let W := localPhaseNorm d M q B D A₂ ρ v
  have hW : 0 ≤ W := localPhaseNorm_nonneg hM hq hD.le (by dsimp [A₂]; positivity)
    hρ (by linarith) v hv
  have hQ : 0 ≤ (N : ℝ)^(-D⁻¹) + ρ + W^D⁻¹ := by positivity
  rw [if_neg hL]
  change T ≤ J*((N : ℝ)^(-D⁻¹)+ρ+W^D⁻¹)
  by_cases ht : T = 0
  · rw [ht]; exact mul_nonneg hJ.le hQ
  have ht' : 0 < T := lt_of_le_of_ne (norm_nonneg _) (Ne.symm ht)
  have hN' : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN'
  have hT : T ≤ 3*C := by
    refine (norm_countingForm_le_window hN' hM _ _ _ _ hv
      (fun i => oneBounded_of_supported (hf i) (hfs i))).trans ?_
    exact (div_le_iff₀ hNR).mpr (card_spatialInterval_bounds hC hN').2
  let δ := T/(12*C)
  have hC' : 0 < 12*C := by positivity
  have hδ : 0 < δ := div_pos ht' hC'
  have hδ' : δ < 1/2 := (div_lt_iff₀ hC').mpr (by linarith)
  have htδ : T = 12*C*δ := by dsimp [δ]; field_simp
  have hδT : δ ≤ T := by
    apply div_le_self (norm_nonneg _)
    linarith
  have hJb : 12*C ≤ J := by
    dsimp [J]
    simpa using (mul_le_mul_of_nonneg_left (le_max_left (1:ℝ) _) hC'.le)
  by_cases hsmall : δ ≤ ρ
  · rw [htδ]
    refine (mul_le_mul hJb hsmall hδ.le hJ.le).trans (mul_le_mul_of_nonneg_left ?_ hJ.le)
    linarith [Real.rpow_nonneg (Nat.cast_nonneg N) (-D⁻¹), Real.rpow_nonneg hW D⁻¹]
  have hint := hInv N q hN hq hqr hM P hP hdeg hcoeff v f hv hf hfs δ hδ hδ' hδT
    (hGuardMono q (le_of_not_ge hsmall) hGuard)
  rcases hint with hsmall' | ⟨l,r,u,b,hb,hI,hlen,hn,htest⟩
  · have hPwr : δ^D ≤ K/(N : ℝ) := by
      rw [Real.rpow_neg hδ.le] at hsmall'
      apply (le_div_iff₀ hNR).2
      have h := (le_div_iff₀ (Real.rpow_pos_of_pos hδ D)).mp (by simpa [div_eq_mul_inv] using hsmall')
      linarith only [h]
    have hbound := (Real.le_rpow_inv_iff_of_pos hδ.le (by positivity) hD).2 hPwr
    rw [Real.div_rpow hK.le (Nat.cast_nonneg _), div_eq_mul_inv,
      ← Real.rpow_neg (Nat.cast_nonneg N)] at hbound
    have hCoeff : 12*C * K^D⁻¹ ≤ J := by
      dsimp [J]
      exact mul_le_mul_of_nonneg_left ((le_max_left _ _).trans (le_max_right _ _)) hC'.le
    rw [htδ]
    refine (mul_le_mul_of_nonneg_left hbound hC'.le).trans ?_
    rw [← mul_assoc]
    refine (mul_le_mul_of_nonneg_right hCoeff (Real.rpow_nonneg (Nat.cast_nonneg _) _)).trans ?_
    apply mul_le_mul_of_nonneg_left _ hJ.le
    linarith [Real.rpow_nonneg hW D⁻¹]
  · have hρδ : ρ ≤ δ := le_of_not_ge hsmall
    have hρE := (Real.rpow_le_rpow hρ.le hρ' hE.le).trans hHalf
    have hρD := Real.rpow_le_rpow hρ.le hρδ hD.le
    have hlen' : (M : ℝ) * (q : ℝ)^(-D) * ρ^A₂ ≤ ((Finset.Icc l r).card : ℝ) := by
      dsimp [A₂]
      rw [Real.rpow_add hρ]
      refine le_trans ?_ hlen
      calc
        _ ≤ ((M : ℝ) * (q : ℝ)^(-D)) * (δ^D * c) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hρD hρE (by positivity) (by positivity))
            (by positivity)
        _ = _ := by ring
    have hcnt : c * δ^D ≤ W := htest.trans (phaseNorm_le_localPhaseNorm hv hb hI hlen' hn)
    have hPwr : δ^D ≤ W/c := by
      apply (le_div_iff₀ hc).2
      simpa [mul_comm] using hcnt
    have hbound := (Real.le_rpow_inv_iff_of_pos hδ.le (by positivity) hD).2 hPwr
    rw [div_eq_mul_inv, Real.mul_rpow hW (by positivity), mul_comm] at hbound
    have hCoeff : 12*C * ((c⁻¹)^D⁻¹) ≤ J := by
      dsimp [J]
      exact mul_le_mul_of_nonneg_left ((le_max_right _ _).trans (le_max_right _ _)) hC'.le
    rw [htδ]
    refine (mul_le_mul_of_nonneg_left hbound hC'.le).trans ?_
    rw [← mul_assoc]
    refine (mul_le_mul_of_nonneg_right hCoeff (Real.rpow_nonneg hW _)).trans ?_
    apply mul_le_mul_of_nonneg_left _ hJ.le
    linarith [Real.rpow_nonneg (Nat.cast_nonneg N) (-D⁻¹)]

theorem localGeneralizedVonNeumann_of_largeCountLocalTest
    (hInv : LargeCountLocalTest) : LocalGeneralizedVonNeumann := by
  intro C d ℓ hC hℓ
  by_cases hL : ℓ = 1
  · subst ℓ
    refine ⟨1,1,1,3*C,0,by norm_num,by norm_num,by norm_num,by linarith,?_⟩
    intro N q hN hq hqr M hM P hP hdeg hcoeff v f hv hf hfs ρ hρ hρ'
    have hp : (P (1 : Fin 2)).natDegree ≤ d := by simpa using hdeg.le
    have hb := localGeneralizedVonNeumann_twoInput C N M d P v f hC (by omega) hM hP.2.1 hp hv hf hfs
    simp only [if_pos rfl, if_true, Real.rpow_one]
    refine hb.trans (mul_le_mul_of_nonneg_left ?_ (by linarith))
    have hN' : (0 : ℝ) ≤ (N : ℝ)^(-(1:ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    linarith
  obtain ⟨K,D,c,B,hK,hD,hc,hInv⟩ := hInv C d ℓ hC (by omega)
  obtain ⟨η,A₁,A₂,J,hη,hA₁,hA₂,hJ,hEst⟩ :=
    localGeneralizedVonNeumann_using_largeCountLocalTest (fun _ _ => True)
      (fun _ _ _ _ _ => trivial) C d ℓ hC hL K D c B hK hD hc (by
        intro N q hN hq hqr M hM P hP hdeg hcoeff v f hv hf hfs δ hδ hδ' ht _
        exact hInv N q hN hq hqr hM P hP hdeg hcoeff v f hv hf hfs δ hδ hδ' ht)
  refine ⟨η,A₁,A₂,J,B,hη,hA₁,hA₂,hJ,?_⟩
  intro N q hN hq hqr M hM P hP hdeg hcoeff v f hv hf hfs ρ hρ hρ'
  exact hEst N q hN hq hqr hM P hP hdeg hcoeff v f hv hf hfs ρ hρ hρ' trivial

end NilBohr
