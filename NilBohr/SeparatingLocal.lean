import NilBohr.CenteredHeisenbergEstimate
import NilBohr.SeparatingScales
import NilBohr.SeparatingScaleConstruction

/-! The local phase and count bounds on the separating scales of Appendix A. -/

open Filter Polynomial
open scoped BigOperators Topology NNReal

namespace NilBohr

/-- The local half of Proposition A.1 at any sequences of parameter lengths
and moduli. The test progression is measured by its actual cardinality. -/
def SeparatingLocalPhaseDecay (α β : ℝ) (F : Circle → ℂ) (q M : ℕ → ℕ) : Prop :=
  ∀ (A : ℝ), 0 < A → ∀ B : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ᶠ j : ℕ in atTop, ∀ (l r u : ℤ) (b : ℕ), b ≤ B →
      Finset.Icc l r ⊆ positiveInterval (M j) →
      ((q j : ℝ) * M j)^(1/2 : ℝ) ≤ ((localProgression l r u (q j ^ b)).card : ℝ) →
      phaseNorm 3 (localProgression l r u (q j ^ b)) (separatingWeight α β F (q j)) ≤
        C * Real.log (M j : ℝ)^(-A)

/-- Apply the centered Heisenberg estimate after parametrizing the congruence
class. Its integer step is the original step multiplied by the modulus. -/
theorem separatingLocalPhase_log_bound {α β : ℝ} {F : Circle → ℂ}
    {r q M : ℕ → ℕ} (hCenter : CenteredHeisenbergPhaseEstimate 2 (heisenbergPhase α β) F r)
    (hPrime : ∀ j, (r j).Prime) (hM : Tendsto M atTop atTop)
    (hWindow : ∀ᶠ j : ℕ in atTop, 0 < q j ∧ (q j).Coprime (r j) ∧
      (r j : ℝ) ≤ ((q j : ℝ)*M j)^(1/100 : ℝ) ∧
      ((q j : ℝ)*M j)^(1/100 : ℝ) < (r (j+1) : ℝ))
    (hStep : ∀ B : ℕ, ∀ᶠ j : ℕ in atTop,
      ((q j^(B+1) : ℕ) : ℝ) ≤ ((q j : ℝ)*M j)^(1/10000 : ℝ)) :
    SeparatingLocalPhaseDecay α β F q M := by
  intro A hA B
  obtain ⟨C,hC,hPhase⟩ := hCenter A hA
  refine ⟨C,hC,?_⟩
  have hMX : Tendsto (fun j : ℕ => ((q j : ℝ)*M j)) atTop atTop := by
    apply tendsto_atTop_mono' _ _ (tendsto_natCast_atTop_atTop.comp hM)
    filter_upwards [hWindow] with j hj
    have hq : (1 : ℝ) ≤ q j := by exact_mod_cast hj.1
    exact le_mul_of_one_le_left (Nat.cast_nonneg _) hq
  have hMlog : Tendsto (fun j : ℕ => Real.log (M j : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hM)
  filter_upwards [hMX.eventually hPhase,hWindow,hStep B,hMlog.eventually_ge_atTop 1,
    hM.eventually_ge_atTop 1] with j hPhase hjwin hStep hlog hMpos
  intro l r' u b hb _ hLen
  obtain ⟨hq,hcop,hLeft,hRight⟩ := hjwin
  let P := localProgression l r' u (q j ^ b)
  let Y := (q j : ℝ)*M j
  have hq₁ : (1 : ℝ) ≤ q j := by exact_mod_cast hq
  have hY : 0 < Y := by
    have hM' : (0 : ℝ) < M j := by exact_mod_cast (show 0 < M j by omega)
    dsimp [Y]
    positivity
  have hPpos : 0 < (P.card : ℝ) := (Real.rpow_pos_of_pos hY _).trans_le hLen
  have hP : P.Nonempty := Finset.card_pos.mp (by exact_mod_cast hPpos)
  obtain ⟨a,_,hrep⟩ := localProgression_as_affine (pow_pos hq b) hP
  have hlen : Y^(1/2 : ℝ) ≤ (P.card : ℝ) := hLen
  have hv : ((q j^(b+1) : ℕ) : ℝ) ≤ Y^(1/10000 : ℝ) := by
    apply le_trans _ hStep
    exact_mod_cast pow_le_pow_right₀ hq (Nat.succ_le_succ hb)
  have hNot : ¬ r j ∣ q j^(b+1) := by
    intro h
    exact (hPrime j).coprime_iff_not_dvd.mp hcop.symm ((hPrime j).dvd_of_dvd_pow h)
  have hAvg := hPhase j hLeft hRight ((q j : ℤ)*a) (q j^(b+1)) P.card
    (pow_pos hq _) hv hNot hlen
  have hBound : phaseNorm 3 P (separatingWeight α β F (q j)) ≤ C*Real.log Y^(-A) := by
    refine le_trans ?_ hAvg
    have hPull := phaseNorm_le_affine_pullback (s := 3) (K := P.card)
      (by omega) (pow_pos hq b) a (separatingWeight α β F (q j))
    rw [← hrep] at hPull
    have hEval (t : ℤ) :
        separatingWeight α β F (q j) (a + ((q j^b : ℕ) : ℤ)*t) =
        F (heisenbergPhase α β ((q j : ℤ)*a + ((q j^(b+1) : ℕ) : ℤ)*t) : Circle) -
          circleMean F := by
      have heq :
          (q j : ℤ)*(a + ((q j^b : ℕ) : ℤ)*t) =
          (q j : ℤ)*a + ((q j^(b+1) : ℕ) : ℤ)*t := by
        simp only [pow_succ, Nat.cast_mul, Nat.cast_pow]
        ring
      simp only [separatingWeight, selectorWeight, heq]
    simpa only [hEval] using hPull
  have hM' : (0 : ℝ) < M j := by exact_mod_cast (show 0 < M j by omega)
  have hLogY : Real.log (M j : ℝ) ≤ Real.log Y :=
    Real.log_le_log hM' (le_mul_of_one_le_left hM'.le hq₁)
  exact hBound.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans_le hlog) hLogY (neg_nonpos.mpr hA.le))
    hC.le)

/-- The Appendix family has exactly the prescribed degrees and coefficient
bounds, with coefficient constant one for every positive modulus. -/
theorem separatingFamily_coefficients {q : ℕ} (hq : 0 < q) :
    FixedPolynomialFamily (separatingFamily q) ∧
    ((separatingFamily q) (Fin.last 2)).natDegree = 2 ∧
    ∀ i, i ≠ 0 → HasCoefficients 1 q (separatingFamily q i) := by
  have hqZ : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
  have hdeg (i : Fin 3) : (separatingFamily q i).natDegree = i.val := by
    fin_cases i
    · simp [separatingFamily]
    · simp [separatingFamily]
    · change (Polynomial.C (q : ℤ) * Polynomial.X^2).natDegree = 2
      exact Polynomial.natDegree_C_mul_X_pow 2 _ hqZ
  have hz (i : Fin 3) : (separatingFamily q i).coeff 0 = 0 := by
    fin_cases i <;> simp [separatingFamily, coeff_C_mul]
  refine ⟨⟨by omega,by simp [separatingFamily],hz,?_⟩,hdeg _,?_⟩
  · intro i j hij
    change (separatingFamily q i).natDegree < (separatingFamily q j).natDegree
    rwa [hdeg,hdeg]
  · intro i hi
    refine ⟨le_rfl,hq,?_,hz i,?_,?_⟩
    · rw [hdeg]
      exact Fin.pos_iff_ne_zero.mpr hi
    · intro t ht ht'
      rw [hdeg] at ht'
      revert ht'
      fin_cases i
      · contradiction
      · simp
        omega
      · intro ht'
        have h : t = 1 := by
          have h2 : t < 2 := ht'
          omega
        simp [h,separatingFamily,coeff_C_mul]
    · refine ⟨1, by norm_num, by norm_num, ?_⟩
      rw [hdeg]
      fin_cases i
      · contradiction
      · simp [separatingFamily]
      · change (Polynomial.C (q : ℤ) * Polynomial.X^2).leadingCoeff = 1*(q : ℤ)^(2-1 : ℕ)
        rw [Polynomial.leadingCoeff_C_mul_X_pow]
        norm_num

private theorem eventually_log_pow_le_nat_pow {M : ℕ → ℕ} (hM : Tendsto M atTop atTop)
    (A : ℝ) {s : ℝ} (hs : 0 < s) :
    ∀ᶠ j : ℕ in atTop, Real.log (M j : ℝ)^A ≤ (M j : ℝ)^s := by
  have hMt : Tendsto (fun j => (M j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hM
  have hLog := Real.tendsto_log_atTop.comp hMt
  have hsmall := hMt.eventually ((isLittleO_log_rpow_rpow_atTop A hs).bound one_pos)
  filter_upwards [hsmall,hLog.eventually_ge_atTop 1,hM.eventually_ge_atTop 1] with j hs hl hm
  have hm' : (0 : ℝ) < M j := by exact_mod_cast (show 0 < M j by omega)
  have hl' : 0 < Real.log (M j : ℝ) := zero_lt_one.trans_le hl
  simpa only [Real.norm_of_nonneg (Real.rpow_nonneg hl'.le A),
    Real.norm_of_nonneg (Real.rpow_nonneg hm'.le s), one_mul] using hs

/-- With `rho = 1 / log M`, every nonempty local test in Theorem 4.2 on
the separating scales has at least `sqrt(q*M)` actual points. -/
theorem eventually_separating_test_length {q M : ℕ → ℕ}
    (hM : Tendsto M atTop atTop) (hq : ∀ᶠ j : ℕ in atTop, 0 < q j)
    (hqGrowth : ∀ e : ℝ, 0 < e → ∀ᶠ j : ℕ in atTop, (q j : ℝ) ≤ (M j : ℝ)^e)
    {A₁ A₂ : ℝ} (hA₁ : 0 < A₁) (B : ℕ) :
    ∀ᶠ j : ℕ in atTop, ∀ (l r u : ℤ) (b : ℕ), b ≤ B →
      (M j : ℝ)*(q j : ℝ)^(-A₁)*(Real.log (M j : ℝ))⁻¹^A₂ ≤
        ((Finset.Icc l r).card : ℝ) →
      (localProgression l r u (q j^b)).Nonempty →
      ((q j : ℝ)*M j)^(1/2 : ℝ) ≤ ((localProgression l r u (q j^b)).card : ℝ) := by
  let E := A₁+(B : ℝ)+1
  have hE : 0 < E := by dsimp [E]; positivity
  let e := (1/8 : ℝ)/E
  have he : 0 < e := div_pos (by norm_num) hE
  have hMt : Tendsto (fun j => (M j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hM
  have hLog := Real.tendsto_log_atTop.comp hMt
  have hscale := (tendsto_rpow_atTop (show (0 : ℝ) < 1/4 by norm_num)).comp hMt
  filter_upwards [hq,hqGrowth e he,eventually_log_pow_le_nat_pow hM A₂
    (show (0 : ℝ) < 1/8 by norm_num),hM.eventually_ge_atTop 1,
    hLog.eventually_ge_atTop 1,hscale.eventually_ge_atTop 2]
    with j hq hqGrowth hlogpow hM₁ hL₁ hscale
  intro l r u b hb hsize hP
  let Q := (q j : ℝ)
  let T := (M j : ℝ)
  let L := Real.log T
  let Y := Q*T
  have hQ₁ : 1 ≤ Q := by
    change (1 : ℝ) ≤ (q j : ℝ)
    exact_mod_cast (show 1 ≤ q j from hq)
  have hQ : 0 < Q := zero_lt_one.trans_le hQ₁
  have hT₁ : 1 ≤ T := by
    change (1 : ℝ) ≤ (M j : ℝ)
    exact_mod_cast hM₁
  have hT : 0 < T := zero_lt_one.trans_le hT₁
  have hL : 0 < L := zero_lt_one.trans_le hL₁
  have hX₁ : 1 ≤ Y := by
    dsimp [Y]
    exact hT₁.trans (le_mul_of_one_le_left hT.le hQ₁)
  have hXsqrt₁ : (1 : ℝ) ≤ Y^(1/2 : ℝ) := Real.one_le_rpow hX₁ (by norm_num)
  have hqe : Q^E ≤ T^(1/8 : ℝ) := by
    calc
      _ ≤ (T^e)^E := Real.rpow_le_rpow hQ.le hqGrowth hE.le
      _ = _ := by
        rw [← Real.rpow_mul hT.le]
        have heq : e*E = (1/8 : ℝ) := div_mul_cancel₀ _ hE.ne'
        rw [heq]
  have hbR : (b : ℝ) ≤ B := by exact_mod_cast hb
  have hqexp : Q^(A₁+(b : ℝ)+1/2) ≤ T^(1/8 : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hQ₁ (by dsimp [E]; linarith)).trans hqe
  have hmass : 2*Y^(1/2:ℝ)*Q^(b:ℝ)*(Q^A₁*L^A₂) ≤ T := by
    calc
      _ = 2*T^(1/2:ℝ)*Q^(A₁+(b:ℝ)+1/2)*L^A₂ := by
        dsimp [Y]
        rw [Real.mul_rpow hQ.le hT.le, Real.rpow_add hQ,
          Real.rpow_add hQ]
        ring
      _ ≤ 2*T^(1/2:ℝ)*T^(1/8:ℝ)*T^(1/8:ℝ) := by
        gcongr
      _ = 2*T^(3/4:ℝ) := by
        rw [mul_assoc 2, ← Real.rpow_add hT,mul_assoc 2, ← Real.rpow_add hT]
        norm_num
      _ ≤ T^(1/4:ℝ)*T^(3/4:ℝ) :=
        mul_le_mul_of_nonneg_right hscale (Real.rpow_nonneg hT.le _)
      _ = _ := by rw [← Real.rpow_add hT]; norm_num
  have hsize' : T / (Q^A₁*L^A₂) ≤ ((Finset.Icc l r).card : ℝ) := by
    change T*Q^(-A₁)*L⁻¹^A₂ ≤ _ at hsize
    rw [Real.rpow_neg hQ.le, Real.inv_rpow hL.le, mul_assoc, ← mul_inv, ← div_eq_mul_inv]
      at hsize
    exact hsize
  have hcount : 2*Y^(1/2:ℝ) ≤ ((Finset.Icc l r).card : ℝ)/(q j^b : ℕ) := by
    have hbpos : (0 : ℝ) < (q j^b : ℕ) := by exact_mod_cast (pow_pos hq b)
    apply (le_div_iff₀ hbpos).mpr
    refine le_trans ?_ hsize'
    apply (le_div_iff₀ (by positivity)).mpr
    rw [Nat.cast_pow, ← Real.rpow_natCast]
    exact hmass
  obtain ⟨_,hLength,_⟩ := localProgression_as_affine (pow_pos hq b) hP
  change _ ≤ ((localProgression l r u (q j^b)).card : ℝ)
  change Y^(1/2:ℝ) ≤ _
  have hhalf : Y^(1/2:ℝ) ≤
      ((Finset.Icc l r).card : ℝ)/(q j^b : ℕ) - 1 := by
    linarith only [hXsqrt₁,hcount]
  exact hhalf.trans hLength.le

/-- The comparison at the end of Appendix A. The scale of the spatial
interval is exactly `q*M²`, and the bound is uniform in the three inputs. -/
theorem separatingCount_log_bound {α β : ℝ} {F : Circle → ℂ}
    {q M : ℕ → ℕ} (hF : Continuous F) (hVN : LocalGeneralizedVonNeumann)
    (hLocal : SeparatingLocalPhaseDecay α β F q M)
    (hM : Tendsto M atTop atTop) (hq : ∀ᶠ j : ℕ in atTop, 0 < q j)
    (hqGrowth : ∀ e : ℝ, 0 < e → ∀ᶠ j : ℕ in atTop, (q j : ℝ) ≤ (M j : ℝ)^e)
    (hqVN : ∀ᶠ j : ℕ in atTop, (q j : ℝ) ≤
      Real.exp ((Real.log (q j*(M j)^2 : ℕ))^(1/10 : ℝ))) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ j : ℕ in atTop,
      let N := q j*(M j)^2
      ∀ f : Fin 3 → ℤ → ℂ,
        (∀ i, OneBoundedOn (spatialInterval 1 N) (f i)) →
        (∀ i, SupportedOn (spatialInterval 1 N) (f i)) →
        ‖countingForm N (M j) (spatialInterval 1 N) (separatingFamily (q j))
          (separatingWeight α β F (q j)) f‖ ≤ C * (Real.log (M j : ℝ))⁻¹ := by
  obtain ⟨η,A₁,A₂,K,B,hη,hA₁,hA₂,hK,hVN⟩ := hVN 1 2 2 le_rfl (by omega)
  let D := η⁻¹
  have hD : 0 < D := inv_pos.mpr hη
  obtain ⟨L,hL,hLocal⟩ := hLocal D hD B
  obtain ⟨W₀,hW₀⟩ := (isCompact_univ (X := Circle)).exists_bound_of_continuousOn
    ((hF.sub continuous_const : Continuous (fun x => F x-circleMean F)).continuousOn)
  let W := max 1 W₀
  have hW₁ : 1 ≤ W := le_max_left _ _
  have hW : 0 < W := zero_lt_one.trans_le hW₁
  let C := W*K*(2+L^η)
  have hMt : Tendsto (fun j => (M j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hM
  have hLog := Real.tendsto_log_atTop.comp hMt
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  filter_upwards [hLocal,hq,hqVN,eventually_separating_test_length hM hq hqGrowth hA₁ (A₂ := A₂) B,
    hM.eventually_ge_atTop 3,hLog.eventually_ge_atTop 2,
    eventually_log_pow_le_nat_pow hM 1 hη] with j hLocal hq hqVN hLen hM₃ hLog₂ hNPow
  let N := q j*(M j)^2
  let t := Real.log (M j : ℝ)
  let ρ := t⁻¹
  let weight := separatingWeight α β F (q j)
  let v := fun y => ((W:ℂ)⁻¹)*weight y
  change ∀ f : Fin 3 → ℤ → ℂ, _ → _ → ‖countingForm N (M j) (spatialInterval 1 N)
    (separatingFamily (q j)) weight f‖ ≤ C*ρ
  intro f hf hfSupport
  have hMpos : 0 < M j := by omega
  have hq₁ : (1 : ℝ) ≤ q j := by exact_mod_cast hq
  have hM₁ : (1 : ℝ) ≤ M j := by exact_mod_cast (show 1 ≤ M j by omega)
  have hM_le_N : M j ≤ N := by
    dsimp [N]
    rw [pow_two]
    calc
      _ ≤ M j*M j := by exact le_mul_of_one_le_right (Nat.zero_le _) (by omega)
      _ ≤ _ := le_mul_of_one_le_left (Nat.zero_le _) hq
  have hN : 3 ≤ N := hM₃.trans hM_le_N
  have ht : 0 < t := zero_lt_two.trans_le hLog₂
  have hρ : 0 < ρ := inv_pos.mpr ht
  have hρ₂ : ρ ≤ 1/2 := by
    change t⁻¹ ≤ 1/2
    rw [one_div]
    exact inv_anti₀ (by norm_num) hLog₂
  have hρ₁ : ρ ≤ 1 := hρ₂.trans (by norm_num)
  have hNormW : ‖((W:ℂ)⁻¹)‖ ≤ 1 := by
    rw [norm_inv,Complex.norm_of_nonneg hW.le]
    exact inv_le_one_of_one_le₀ hW₁
  have hv : OneBoundedOn (positiveInterval (M j)) v := by
    intro y _
    change ‖((W:ℂ)⁻¹)*(F (heisenbergPhase α β ((q j:ℤ)*y) : Circle)-circleMean F)‖ ≤ 1
    rw [norm_mul,norm_inv,Complex.norm_of_nonneg hW.le,← div_eq_inv_mul]
    exact (div_le_one hW).mpr ((hW₀ _ (Set.mem_univ _)).trans (le_max_right _ _))
  have hLocalBound : localPhaseNorm 2 (M j) (q j) B A₁ A₂ ρ v ≤ L*t^(-D) := by
    unfold localPhaseNorm
    apply Real.sSup_le _ (by positivity)
    rintro _ ⟨l,r,u,b,hb,hI,hSize,hn,rfl⟩
    have hLtest := hLocal l r u b hb hI (hLen l r u b hb hSize hn)
    exact (phaseNorm_const_mul_le (s := 3) (by omega)
      (localProgression l r u (q j^b)) weight ((W:ℂ)⁻¹)).trans
      ((mul_le_of_le_one_left (phaseNorm_nonneg_of_pos (s := 3) (by omega) _ _) hNormW).trans
        hLtest)
  have hLocal₀ := localPhaseNorm_nonneg (d := 2) (B := B) hMpos hq
    hA₁.le hA₂.le hρ hρ₁ v hv
  have hLocalPow : (localPhaseNorm 2 (M j) (q j) B A₁ A₂ ρ v)^η ≤ L^η*ρ := by
    refine (Real.rpow_le_rpow hLocal₀ hLocalBound hη.le).trans_eq ?_
    rw [Real.mul_rpow hL.le (Real.rpow_nonneg ht.le _),← Real.rpow_mul ht.le]
    rw [show -D*η = -(1:ℝ) by rw [neg_mul,inv_mul_cancel₀ hη.ne']]
    rw [Real.rpow_neg_one]
  have hNPow : (N : ℝ)^(-η) ≤ ρ := by
    have hMposit : (0 : ℝ) < M j := by exact_mod_cast hMpos
    refine (Real.rpow_le_rpow_of_nonpos hMposit (by exact_mod_cast hM_le_N) (neg_nonpos.mpr hη.le)).trans ?_
    rw [Real.rpow_neg hMposit.le]
    exact inv_anti₀ ht (by simpa only [Real.rpow_one] using hNPow)
  obtain ⟨hP,hTop,hCoeffs⟩ := separatingFamily_coefficients hq
  have hWindow : parameterLength N (q j) 2 = M j := parameterLength_separatingFamily _ hq
  specialize hVN N (q j) hN hq hqVN
  rw [hWindow] at hVN
  have hcount := hVN hMpos (separatingFamily (q j)) hP hTop hCoeffs v f hv
    hf hfSupport ρ hρ hρ₂
  simp only [show ¬ (2 : ℕ) = 1 by omega, if_false] at hcount
  have hCountBound := hcount.trans (mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add hNPow le_rfl) hLocalPow) hK.le)
  have hWeight : weight = (fun x => (W:ℂ)*v x) := by
    funext x
    have hWne : (W:ℂ) ≠ 0 := by exact_mod_cast hW.ne'
    simp only [v,← mul_assoc,mul_inv_cancel₀ hWne,one_mul]
  rw [hWeight,countingForm_mul_weight,norm_mul,Complex.norm_of_nonneg hW.le]
  refine (mul_le_mul_of_nonneg_left hCountBound hW.le).trans_eq ?_
  dsimp [C]
  ring

/-- The entire interval is a tested progression once the modulus is at
most the parameter length. -/
theorem separatingGlobalPhase_log_bound {α β : ℝ} {F : Circle → ℂ}
    {q M : ℕ → ℕ} (hLocal : SeparatingLocalPhaseDecay α β F q M)
    (hqM : ∀ᶠ j : ℕ in atTop, q j ≤ M j) {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ j : ℕ in atTop,
      phaseNorm 3 (positiveInterval (M j)) (separatingWeight α β F (q j)) ≤
        C * Real.log (M j : ℝ)^(-A) := by
  obtain ⟨C,hC,hLocal⟩ := hLocal A hA 0
  refine ⟨C,hC,?_⟩
  filter_upwards [hLocal,hqM] with j hLocal hqM
  have hP : localProgression 1 (M j : ℤ) 0 (q j^0) = positiveInterval (M j) := by
    simp [localProgression, positiveInterval, Int.modEq_one]
  have hLen : ((q j : ℝ)*M j)^(1/2 : ℝ) ≤ (M j : ℝ) := by
    calc
      _ ≤ ((M j : ℝ)^2)^(1/2 : ℝ) := by
        apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
        rw [pow_two]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hqM) (Nat.cast_nonneg _)
      _ = _ := by
        rw [← Real.rpow_natCast,← Real.rpow_mul (Nat.cast_nonneg _)]
        norm_num
  have hBound := hLocal 1 (M j : ℤ) 0 0 le_rfl (by rfl)
    (by rw [hP,card_positiveInterval]; exact hLen)
  rwa [hP] at hBound

/-- In the repeated-residue dilation at (K=1), the phase-norm contribution
tends to zero by the whole-interval test. -/
theorem separatingGlobalPhase_tendsto_zero {α β : ℝ} {F : Circle → ℂ}
    {q M : ℕ → ℕ} (hLocal : SeparatingLocalPhaseDecay α β F q M)
    (hqM : ∀ᶠ j : ℕ in atTop, q j ≤ M j) (hM : Tendsto M atTop atTop) :
    Tendsto (fun j => phaseNorm 3 (positiveInterval (M j))
      (separatingWeight α β F (q j))) atTop (𝓝 0) := by
  obtain ⟨C,_,hUpper⟩ := separatingGlobalPhase_log_bound hLocal hqM
    (show 0 < (1 : ℝ) by norm_num)
  have hLog : Tendsto (fun j => Real.log (M j : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hM)
  have hInv := (tendsto_inv_atTop_zero.comp hLog).const_mul C
  refine squeeze_zero' (g := fun j => C*(Real.log (M j : ℝ))⁻¹) (Eventually.of_forall (fun j =>
    phaseNorm_nonneg_of_pos (by omega) _ _)) ?_ ?_
  · simpa only [Real.rpow_neg_one] using hUpper
  · simpa only [mul_zero] using hInv

/-- The stated local phase estimate on the explicit separating scales
follows from the same two quantitative obstruction interfaces as (24). -/
theorem separatingLocalPhase_of_obstructions
    (hGT : ProductHeisenbergObstruction) (hScalar : ScalarHeisenbergObstruction)
    {α β : ℝ} (hα : BadlyApproximable α) {r : ℕ → ℕ}
    (hr : AdmissibleBetaDenominators β r) (F : Circle → ℂ)
    {κ : ℝ≥0} (hF : LipschitzWith κ F) :
    SeparatingLocalPhaseDecay α β F (fun j => separatingModulus (r j))
      (fun j => separatingLength (r j) (r (j+1))) := by
  have hPrimes (j : ℕ) : (r j).Prime := by
    obtain ⟨_,_,_,hPrimes,_⟩ := hr
    exact (hPrimes j).1
  refine separatingLocalPhase_log_bound
    (centeredHeisenbergPhaseEstimate_of_obstructions hGT hScalar hα hr 2 F hF)
    hPrimes (tendsto_separatingLength hr) ?_ (eventually_separatingStep hr)
  filter_upwards [eventually_separatingScale hr] with j hj
  refine ⟨hj.q_pos,hj.coprime,?_,?_⟩
  · simpa only [separatingScaleX,Nat.cast_mul] using hj.bracket_left
  · simpa only [separatingScaleX,Nat.cast_mul] using hj.bracket_right

/-- The original weighted count on the explicit separating sequence is
uniformly bounded by the inverse logarithm of the parameter length. -/
theorem separatingCount_of_kmtt (hKMTT : KMTTLocalInverse)
    (hGT : ProductHeisenbergObstruction) (hScalar : ScalarHeisenbergObstruction)
    {α β : ℝ} (hα : BadlyApproximable α) {r : ℕ → ℕ}
    (hr : AdmissibleBetaDenominators β r) (F : Circle → ℂ)
    {κ : ℝ≥0} (hF : LipschitzWith κ F) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ j : ℕ in atTop,
      let q := separatingModulus (r j)
      let M := separatingLength (r j) (r (j+1))
      let N := separatingSpatialScale (r j) (r (j+1))
      ∀ f : Fin 3 → ℤ → ℂ,
        (∀ i, OneBoundedOn (spatialInterval 1 N) (f i)) →
        (∀ i, SupportedOn (spatialInterval 1 N) (f i)) →
        ‖countingForm N M (spatialInterval 1 N) (separatingFamily q)
          (separatingWeight α β F q) f‖ ≤ C * (Real.log (M : ℝ))⁻¹ := by
  refine separatingCount_log_bound hF.continuous (localGeneralizedVonNeumann_of_kmtt hKMTT)
    (separatingLocalPhase_of_obstructions hGT hScalar hα hr F hF)
    (tendsto_separatingLength hr) ((eventually_separatingScale hr).mono fun _ hj => hj.q_pos)
    ?_ (eventually_separatingModulus_subexponential hr)
  intro e he
  simpa only [pow_one] using eventually_separatingModulus_subpower hr 1 he

end NilBohr
