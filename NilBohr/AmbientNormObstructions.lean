import NilBohr.SeparatingGowers
import NilBohr.SeparatingQuadraticLimit

/-! The two Gowers obstructions in the introductory proof overview. -/

open Filter Polynomial
open scoped BigOperators Topology NNReal ComplexConjugate

namespace NilBohr

/-- The positive lower bound for the centered selector at the ambient modulus
holds along all sufficiently large intervals, at every order at least three. -/
theorem ambient_centered_gowers_lower_bound
    (hGT : ScalarHeisenbergObstruction) (hBernstein : BernsteinCircleLipschitzFourier)
    (α β : ℝ) (hα : BadlyApproximable α) (hβ : AdmissibleBeta β)
    (F : C(Circle, ℂ)) {κF : ℝ≥0} (hF : LipschitzWith κF F)
    (hFnonconstant : ∃ x y : Circle, F x ≠ F y)
    (S : ℕ) (hS : 3 ≤ S) (hG : NormalizedGowersLaws S) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ M : ℕ in atTop,
      c ≤ normalizedGowers S 1 (M : ℤ)
        (fun n => F (heisenbergPhase α β n : Circle) - circleMean F) := by
  obtain ⟨_, _, r, hr⟩ := (admissibleBeta_iff_exists_denominators β).mp hβ
  obtain ⟨c, hc, hBound⟩ :=
    separating_gowers_lower_bound hGT hBernstein α β hα hr F hF hFnonconstant S hS hG
  have hbracket := (heisenberg_horizontal_for_denominators α β hα hr).1
  refine ⟨c, hc, ?_⟩
  filter_upwards [tendsto_natCast_atTop_atTop.eventually (hBound.and hbracket),
    eventually_ge_atTop 1] with M ⟨hM, hj⟩ hMpos
  obtain ⟨j, hjlo, hjhi⟩ := hj
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hMpos
  have hprime : (r j).Prime := by
    obtain ⟨_, _, _, h, _⟩ := hr
    exact (h j).1
  have hnot : ¬ r j ∣ 1 := fun h => hprime.ne_one (Nat.dvd_one.mp h)
  have h := hM j 1 M hjlo hjhi Nat.one_pos
    (by simpa only [Nat.cast_one] using
      (Real.one_le_rpow hM' (show (0 : ℝ) ≤ 1/10000 by norm_num))) hnot
    (by simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hM' (show (1/2 : ℝ) ≤ 1 by norm_num))
  have heq : separatingWeight α β F 1 =
      fun n => F (heisenbergPhase α β n : Circle) - circleMean F := by
    funext n
    simp [separatingWeight, selectorWeight]
  rwa [heq] at h

/-- The quadratic phase whose second differences will be tested. -/
noncomputable def quadraticObstructionWeight (θ : ℝ) (n : ℤ) : ℂ :=
  phase (-θ * (n : ℝ)^2)

private noncomputable def quadraticCountInputs (θ : ℝ) (M : ℕ) (i : Fin 3) (x : ℤ) : ℂ :=
  if i = 0 then zeroOutside 1 ((M : ℤ)^2) (fun t => phase (-θ * (t : ℝ))) x
  else zeroOutside 1 (2*(M : ℤ)^2) (fun t => if i = 2 then phase (θ * (t : ℝ)) else 1) x

/-- The two spatial linear phases cancel the parameter phase exactly on
the supporting interval. The spatial supports are all contained in
\([2M^2]\), and the count uses the scale \(M^2\). -/
theorem quadratic_obstruction_count (θ : ℝ) {M : ℕ} (hM : 0 < M) :
    ∃ f : Fin 3 → ℤ → ℂ,
      (∀ i, SupportedOn (positiveInterval (2*M^2)) (f i)) ∧
      (∀ i x, ‖f i x‖ ≤ 1) ∧
      SupportedOn (positiveInterval (M^2)) (f 0) ∧
      countingForm (M^2) M (positiveInterval (M^2)) (separatingFamily 1)
        (quadraticObstructionWeight θ) f = 1 := by
  refine ⟨quadraticCountInputs θ M, ?_, ?_, ?_, ?_⟩
  · intro i x hx
    have h₂ : x ∉ Finset.Icc (1 : ℤ) (2*(M : ℤ)^2) := by
      simpa [positiveInterval, Nat.cast_mul, Nat.cast_pow] using hx
    have h₁ : x ∉ Finset.Icc (1 : ℤ) ((M : ℤ)^2) := by
      intro hm
      have hh := (Finset.mem_Icc.mp hm)
      exact h₂ (Finset.mem_Icc.mpr ⟨hh.1, hh.2.trans (by nlinarith)⟩)
    simp [quadraticCountInputs, zeroOutside, h₁, h₂]
  · intro i x
    unfold quadraticCountInputs zeroOutside
    split_ifs <;> simp [norm_phase]
  · intro x hx
    have h₁ : x ∉ Finset.Icc (1 : ℤ) ((M : ℤ)^2) := by
      simpa only [positiveInterval, Nat.cast_pow] using hx
    simp [quadraticCountInputs, zeroOutside, h₁]
  · have hprod (x n : ℤ) (hx : x ∈ positiveInterval (M^2)) (hn : n ∈ positiveInterval M) :
        quadraticObstructionWeight θ n *
          ∏ i : Fin 3, quadraticCountInputs θ M i (x+(separatingFamily 1 i).eval n) = 1 := by
      have hx' : (1 : ℤ) ≤ x ∧ x ≤ (M : ℤ)^2 := by simpa [positiveInterval] using hx
      have hn' : (1 : ℤ) ≤ n ∧ n ≤ (M : ℤ) := by simpa [positiveInterval] using hn
      have hMain : n^2 ≤ (M : ℤ)^2 := pow_le_pow_left₀ (by omega) hn'.2 2
      have hx₁ : (1 : ℤ) ≤ x+n ∧ x+n ≤ 2*(M : ℤ)^2 := by
        constructor
        · omega
        · nlinarith only [hx'.2, hn'.1, hMain, mul_nonneg (show 0 ≤ n by omega)
            (show 0 ≤ n-1 by omega)]
      have hx₂ : (1 : ℤ) ≤ x+n^2 ∧ x+n^2 ≤ 2*(M : ℤ)^2 :=
        ⟨by nlinarith only [hx'.1, sq_nonneg n], by omega⟩
      simp (disch := omega) [Fin.prod_univ_succ, separatingFamily, quadraticCountInputs,
        zeroOutside, hx'.1, hx'.2, hx₁.1, hx₁.2, hx₂.1, hx₂.2, quadraticObstructionWeight]
      rw [← phase_add, ← phase_add]
      convert phase_zero using 1
      ring_nf
    have hx (x : ℤ) (hx : x ∈ positiveInterval (M^2)) :
        (∑ n ∈ positiveInterval M, quadraticObstructionWeight θ n *
          ∏ i : Fin 3, quadraticCountInputs θ M i (x+(separatingFamily 1 i).eval n)) = (M : ℂ) := by
      rw [Finset.sum_congr rfl (fun n hn => hprod x n hx hn)]
      simp
    unfold countingForm
    rw [Finset.sum_congr rfl hx]
    have hMC : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
    simp [hMC]

/-- With a single supporting interval and spatial normalization for all
three inputs, the same example has count one half. -/
theorem quadratic_obstruction_common_window (θ : ℝ) {M : ℕ} (hM : 0 < M) :
    ∃ f : Fin 3 → ℤ → ℂ,
      (∀ i, SupportedOn (positiveInterval (2*M^2)) (f i)) ∧
      (∀ i x, ‖f i x‖ ≤ 1) ∧
      countingForm (2*M^2) M (positiveInterval (2*M^2)) (separatingFamily 1)
        (quadraticObstructionWeight θ) f = 1/2 := by
  obtain ⟨f, hf, hb, hBase, h⟩ := quadratic_obstruction_count θ hM
  let X := positiveInterval (2*M^2)
  have hsub : positiveInterval (M^2) ⊆ X := by
    apply Finset.Icc_subset_Icc le_rfl
    have h : M^2 ≤ 2*M^2 := by omega
    exact_mod_cast h
  have hzero : separatingFamily 1 (0 : Fin 3) = 0 := by simp [separatingFamily]
  rw [countingForm_mono_window (k := 2) (M^2) M hsub (separatingFamily 1) hzero
    (quadraticObstructionWeight θ) f hBase] at h
  have hs : countingForm (M^2) M X (separatingFamily 1) (quadraticObstructionWeight θ) f =
      2 * countingForm (2*M^2) M X (separatingFamily 1) (quadraticObstructionWeight θ) f := by
    have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
    simp only [countingForm, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
    field_simp [hM', show (2 : ℂ) ≠ 0 by norm_num]
    ring
  refine ⟨f, hf, hb, ?_⟩
  rw [hs] at h
  apply mul_left_cancel₀ (show (2 : ℂ) ≠ 0 by norm_num)
  simpa using h

private abbrev ShiftIndex (M : ℕ) :=
  Fin (2 * ((M : ℤ) - 1).toNat + 1)

private def intervalShift (M : ℕ) (i : ShiftIndex M) : ℤ :=
  (i.val : ℤ) - (((M : ℤ) - 1).toNat : ℤ)

private def intervalOverlap (M : ℕ) (h : ℤ) : Finset ℤ :=
  Finset.Icc (max 1 (1-h)) (min (M : ℤ) ((M : ℤ)-h))

private theorem mem_intervalOverlap (M : ℕ) (h x : ℤ) :
    x ∈ intervalOverlap M h ↔ x ∈ positiveInterval M ∧ x+h ∈ positiveInterval M := by
  simp only [intervalOverlap, positiveInterval, Finset.mem_Icc, max_le_iff, le_min_iff]
  omega

private theorem intervalOverlap_card_le (M : ℕ) (h : ℤ) :
    (intervalOverlap M h).card ≤ M := by
  have hsub : intervalOverlap M h ⊆ positiveInterval M :=
    fun x hx => ((mem_intervalOverlap M h x).mp hx).1
  simpa [positiveInterval, Int.card_Icc] using Finset.card_le_card hsub

private theorem gowers_two_sum_sq (M : ℕ) (hM : 0 < M) (f : ℤ → ℂ) :
    (gowersCubePower 2 1 (M : ℤ) f).re =
      ∑ i : ShiftIndex M,
        ‖∑ x ∈ intervalOverlap M (intervalShift M i),
          f x * conj (f (x + intervalShift M i))‖^2 := by
  have hI : (1 : ℤ) ≤ M := by exact_mod_cast hM
  change (gowersCubePower (1+1) 1 (M : ℤ) f).re = _
  rw [gowersCubePower_succ_eq_sum_sq _ _ hI 1]
  have hdir (u : Fin 1 → ShiftIndex M) :
      gowersDirectionsHere 1 (M : ℤ) 1 u = [intervalShift M (u 0)] := by
    simp [gowersDirectionsHere, intervalShift, List.ofFn_succ]
  simp only [hdir, cubeProduct, ← Complex.ofReal_sum, Complex.ofReal_re]
  apply Fintype.sum_equiv (Equiv.funUnique (Fin 1) (ShiftIndex M))
  intro u
  change ‖∑ x ∈ positiveInterval M,
    zeroOutside 1 (M : ℤ) f x *
      conj (zeroOutside 1 (M : ℤ) f (x+intervalShift M (u 0)))‖^2 =
    ‖∑ x ∈ intervalOverlap M (intervalShift M (u 0)),
      f x * conj (f (x+intervalShift M (u 0)))‖^2
  congr 2
  let h := intervalShift M (u 0)
  have hsub : intervalOverlap M h ⊆ positiveInterval M :=
    fun x hx => ((mem_intervalOverlap M h x).mp hx).1
  rw [← Finset.sum_subset hsub]
  · apply Finset.sum_congr rfl
    intro x hx
    obtain ⟨hx₁, hx₂⟩ := (mem_intervalOverlap M h x).mp hx
    change x ∈ Finset.Icc 1 (M : ℤ) at hx₁
    change x+intervalShift M (u 0) ∈ Finset.Icc 1 (M : ℤ) at hx₂
    simp only [zeroOutside, if_pos hx₁, if_pos hx₂]
  · intro x hx hx'
    have hn : x+h ∉ positiveInterval M :=
      fun hy => hx' ((mem_intervalOverlap M h x).mpr ⟨hx, hy⟩)
    change x+intervalShift M (u 0) ∉ Finset.Icc 1 (M : ℤ) at hn
    simp only [zeroOutside, if_neg hn, map_zero, mul_zero]

private theorem norm_sum_phase_Icc_mul_torusNorm_le (a b : ℤ) (u c : ℝ) :
    ‖∑ x ∈ Finset.Icc a b, phase (u*(x : ℝ)+c)‖ * torusNorm u ≤ 1 := by
  let H := (b+1-a).toNat
  rw [Int.Icc_eq_finset_map, Finset.sum_map]
  change ‖∑ n ∈ Finset.range H, phase (u*((a+(n : ℤ) : ℤ) : ℝ)+c)‖ * torusNorm u ≤ 1
  simp only [Int.cast_add, Int.cast_natCast, mul_add]
  have hrewrite (n : ℕ) :
      u*(a : ℝ)+u*(n : ℝ)+c = u*(n : ℝ)+(u*(a : ℝ)+c) := by ring
  simp only [hrewrite]
  have h := norm_prefixAverage_linear_mul_torusNorm_le H u (u*(a : ℝ)+c)
  by_cases hH : H = 0
  · simp [hH]
  · have hH' : (H : ℝ) ≠ 0 := by exact_mod_cast hH
    have heq : prefixAverage (fun n => phase (u*(n : ℝ)+(u*(a : ℝ)+c))) H =
        (∑ n ∈ Finset.range H, phase (u*(n : ℝ)+(u*(a : ℝ)+c))) / (H : ℂ) := by
      simp [prefixAverage, Complex.real_smul, div_eq_mul_inv, mul_comm]
    rw [heq, norm_div, Complex.norm_natCast, ← mul_assoc, div_mul_cancel₀ _ hH'] at h
    exact h

private noncomputable def quadraticCorrelation (θ : ℝ) (M : ℕ) (h : ℤ) : ℂ :=
  ∑ x ∈ intervalOverlap M h,
    quadraticObstructionWeight θ x * conj (quadraticObstructionWeight θ (x+h))

private theorem norm_quadraticCorrelation_le (θ : ℝ) (M : ℕ) (h : ℤ) :
    ‖quadraticCorrelation θ M h‖ ≤ M := by
  calc
    _ ≤ ∑ x ∈ intervalOverlap M h,
        ‖quadraticObstructionWeight θ x * conj (quadraticObstructionWeight θ (x+h))‖ :=
      norm_sum_le _ _
    _ = ((intervalOverlap M h).card : ℝ) := by
      simp [quadraticObstructionWeight, norm_mul, norm_phase]
    _ ≤ _ := by exact_mod_cast intervalOverlap_card_le M h

private theorem norm_quadraticCorrelation_mul_torusNorm_le (θ : ℝ) (M : ℕ) (h : ℤ) :
    ‖quadraticCorrelation θ M h‖ * torusNorm ((2*θ)*(h : ℝ)) ≤ 1 := by
  have hphase (x : ℤ) :
      quadraticObstructionWeight θ x * conj (quadraticObstructionWeight θ (x+h)) =
      phase ((2*θ)*(h : ℝ)*x + θ*(h : ℝ)^2) := by
    change phaseExponential (-θ*(x : ℝ)^2) *
      conj (phaseExponential (-θ*((x+h : ℤ) : ℝ)^2)) = phaseExponential _
    rw [← phaseExponential_sub, Int.cast_add]
    congr 1
    ring
  simpa only [quadraticCorrelation, hphase, intervalOverlap] using
    norm_sum_phase_Icc_mul_torusNorm_le (max 1 (1-h)) (min (M : ℤ) ((M : ℤ)-h))
      ((2*θ)*(h : ℝ)) (θ*(h : ℝ)^2)

/-- In each block of K consecutive directions at most one rotation is
closer than a sufficiently small positive threshold to an integer. -/
private theorem small_rotations_card_bound (θ : ℝ) (hθ : Irrational θ)
    (K : ℕ) (hK : 2 ≤ K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ M : ℕ,
      (Finset.univ.filter (fun i : ShiftIndex M =>
        torusNorm ((2*θ)*(intervalShift M i : ℝ)) < δ)).card ≤ (2*M)/K+1 := by
  classical
  let D := (Finset.Icc (1-(K : ℤ)) ((K : ℤ)-1)).erase 0
  have hD : D.Nonempty := by
    refine ⟨1, ?_⟩
    simp [D]
    omega
  obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image D
    (fun t : ℤ => torusNorm ((2*θ)*(t : ℝ))) hD
  have hmne : m ≠ 0 := Finset.ne_of_mem_erase hm
  have hirr : Irrational ((2*θ)*(m : ℝ)) := by
    have h := (irrational_intCast_mul_iff (m := 2*m)).2
      ⟨by omega, hθ⟩
    convert h using 1
    push_cast
    ring
  let d := torusNorm ((2*θ)*(m : ℝ))
  have hd : 0 < d := by
    dsimp [d]
    rw [torusNorm_eq, abs_pos, sub_ne_zero]
    exact hirr.ne_int _
  refine ⟨d/3, by positivity, ?_⟩
  intro M
  let B := Finset.univ.filter (fun i : ShiftIndex M =>
    torusNorm ((2*θ)*(intervalShift M i : ℝ)) < d/3)
  have hW : ((M : ℤ)-1).toNat ≤ M := by omega
  have hKpos : 0 < K := by omega
  calc
    B.card ≤ (Finset.range ((2*M)/K+1)).card := by
      apply Finset.card_le_card_of_injOn (fun i : ShiftIndex M => i.val/K)
      · intro i _
        apply Finset.mem_range.mpr
        have hi : i.val ≤ 2*M := by have := i.isLt; omega
        exact Nat.lt_succ_of_le (Nat.div_le_div_right hi)
      · intro a ha b hb hab
        by_contra hn
        have ha' : a.val % K < K := Nat.mod_lt _ hKpos
        have hb' : b.val % K < K := Nat.mod_lt _ hKpos
        have hqa := Nat.div_add_mod a.val K
        have hqb := Nat.div_add_mod b.val K
        change a.val/K = b.val/K at hab
        rw [hab] at hqa
        have hdiff : intervalShift M a-intervalShift M b =
            ((a.val % K : ℕ) : ℤ)-((b.val % K : ℕ) : ℤ) := by
          dsimp [intervalShift]
          omega
        have hne : intervalShift M a-intervalShift M b ≠ 0 := by
          intro he
          apply hn
          apply Fin.ext
          dsimp [intervalShift] at he
          omega
        have hmem : intervalShift M a-intervalShift M b ∈ D := by
          simp only [D, Finset.mem_erase, Finset.mem_Icc, hne, true_and]
          omega
        have h := hmin _ hmem
        change d ≤ _ at h
        rw [Int.cast_sub, mul_sub] at h
        have ht := torusNorm_sub_le ((2*θ)*(intervalShift M a : ℝ))
          ((2*θ)*(intervalShift M b : ℝ))
        have h₁ := (Finset.mem_filter.mp ha).2
        have h₂ := (Finset.mem_filter.mp hb).2
        linarith only [ht, h, h₁, h₂, hd]
    _ = _ := Finset.card_range _

private theorem gowers_two_one_lower {M : ℕ} (hM : 0 < M) :
    (M : ℝ)^3/8 ≤ (gowersCubePower 2 1 (M : ℤ) (fun _ => 1)).re := by
  let W := ((M : ℤ)-1).toNat
  have hW : W = M-1 := by dsimp [W]; omega
  let K := M/2
  have hK : K ≤ W := by dsimp [K]; omega
  let J := Finset.univ.filter (fun i : ShiftIndex M => W ≤ i.val ∧ i.val ≤ W+K)
  have hCard : K+1 ≤ J.card := by
    let f (i : Fin (K+1)) : ShiftIndex M := ⟨W+i.val, by have := i.isLt; omega⟩
    have h := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (Fin (K+1))))
      (t := J) f (by
        intro i _
        have hi := i.isLt
        simp [J, f]
        omega)
      (by intro a _ b _ hab; apply Fin.ext; have h := congrArg Fin.val hab; simpa [f] using h)
    simpa using h
  have hCard' : (M : ℝ)/2 ≤ (J.card : ℝ) := by
    have h : M ≤ 2*J.card := by dsimp [K] at hCard; omega
    have h' : (M : ℝ) ≤ 2*(J.card : ℝ) := by exact_mod_cast h
    linarith
  rw [gowers_two_sum_sq M hM]
  simp only [map_one, one_mul, Finset.sum_const, nsmul_eq_mul, mul_one,
    Complex.norm_natCast]
  calc
    (M : ℝ)^3/8 = ((M : ℝ)/2)*((M : ℝ)/2)^2 := by ring
    _ ≤ (J.card : ℝ)*((M : ℝ)/2)^2 :=
      mul_le_mul_of_nonneg_right hCard' (sq_nonneg _)
    _ = ∑ i ∈ J, ((M : ℝ)/2)^2 := by simp
    _ ≤ ∑ i ∈ J, ((intervalOverlap M (intervalShift M i)).card : ℝ)^2 := by
      apply Finset.sum_le_sum
      intro i hi
      have hab := (Finset.mem_filter.mp hi).2
      let h := intervalShift M i
      have hh : 0 ≤ h ∧ h ≤ (K : ℤ) := by dsimp [h, intervalShift]; omega
      have hcard : ((intervalOverlap M h).card : ℤ) = (M : ℤ)-h := by
        have h₁ : 1-h ≤ (1 : ℤ) := by omega
        have h₂ : (M : ℤ)-h ≤ M := by omega
        rw [intervalOverlap, max_eq_left h₁, min_eq_right h₂, Int.card_Icc]
        rw [show (M : ℤ)-h+1-1 = (M : ℤ)-h by ring]
        exact Int.toNat_of_nonneg (by dsimp [K] at hh; omega)
      have hlo : (M : ℤ) ≤ 2*((intervalOverlap M h).card : ℤ) := by
        rw [hcard]
        dsimp [K] at hh
        omega
      have hlo' : (M : ℝ) ≤ 2*((intervalOverlap M h).card : ℝ) := by exact_mod_cast hlo
      exact pow_le_pow_left₀ (by positivity) (by linarith) 2
    _ ≤ ∑ i : ShiftIndex M, ((intervalOverlap M (intervalShift M i)).card : ℝ)^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; positivity)

private theorem gowers_two_quadratic_upper (θ : ℝ) {M K : ℕ} (hM : 0 < M)
    {δ : ℝ} (hδ : 0 < δ)
    (hCard : (Finset.univ.filter (fun i : ShiftIndex M =>
      torusNorm ((2*θ)*(intervalShift M i : ℝ)) < δ)).card ≤ (2*M)/K+1) :
    (gowersCubePower 2 1 (M : ℤ) (quadraticObstructionWeight θ)).re ≤
      (2*(M : ℝ)/K+1)*(M : ℝ)^2 + 3*M*(δ⁻¹)^2 := by
  classical
  let p (i : ShiftIndex M) := torusNorm ((2*θ)*(intervalShift M i : ℝ)) < δ
  let R (i : ShiftIndex M) := ‖quadraticCorrelation θ M (intervalShift M i)‖^2
  let Bad := Finset.univ.filter p
  let Good := Finset.univ.filter (fun i => ¬ p i)
  have hBad : (Bad.card : ℝ) ≤ 2*(M : ℝ)/K+1 := by
    have hc : (Bad.card : ℝ) ≤ (((2*M)/K+1 : ℕ) : ℝ) := by exact_mod_cast hCard
    push_cast at hc
    exact hc.trans (add_le_add_right (by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using
        (Nat.cast_div_le (α := ℝ) (m := 2*M) (n := K))) _)
  have hGood : (Good.card : ℝ) ≤ 3*M := by
    have hc : Good.card ≤ Fintype.card (ShiftIndex M) := Finset.card_le_univ _
    have hW : ((M : ℤ)-1).toNat ≤ M := by omega
    simp only [ShiftIndex, Fintype.card_fin] at hc
    exact_mod_cast (show Good.card ≤ 3*M by omega)
  have hGoodTerm (i : ShiftIndex M) (hi : i ∈ Good) :
      R i ≤ (δ⁻¹)^2 := by
    have hd : δ ≤ torusNorm ((2*θ)*(intervalShift M i : ℝ)) :=
      le_of_not_gt (Finset.mem_filter.mp hi).2
    have h : ‖quadraticCorrelation θ M (intervalShift M i)‖ ≤ δ⁻¹ := by
      rw [← one_div, le_div_iff₀ hδ]
      exact (mul_le_mul_of_nonneg_left hd (norm_nonneg _)).trans
        (norm_quadraticCorrelation_mul_torusNorm_le θ M _)
    exact pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [gowers_two_sum_sq M hM]
  change (∑ i : ShiftIndex M, R i) ≤ _
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ p R]
  change (∑ i ∈ Bad, R i) + (∑ i ∈ Good, R i) ≤ _
  apply add_le_add
  · calc
      _ ≤ ∑ i ∈ Bad, (M : ℝ)^2 := Finset.sum_le_sum fun i _ =>
        pow_le_pow_left₀ (norm_nonneg _) (norm_quadraticCorrelation_le θ M _) 2
      _ = (Bad.card : ℝ)*(M : ℝ)^2 := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hBad (sq_nonneg _)
  · calc
      _ ≤ ∑ i ∈ Good, (δ⁻¹)^2 := Finset.sum_le_sum hGoodTerm
      _ = (Good.card : ℝ)*(δ⁻¹)^2 := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hGood (sq_nonneg _)

/-- The normalized interval U² norm of an irrational quadratic tends to
zero on the complete range of positive integer scales. -/
theorem irrational_quadratic_gowers_two_tendsto_zero (θ : ℝ) (hθ : Irrational θ) :
    Tendsto (fun M : ℕ => normalizedGowers 2 1 (M : ℤ) (quadraticObstructionWeight θ))
      atTop (𝓝 0) := by
  let A (M : ℕ) := (gowersCubePower 2 1 (M : ℤ) (quadraticObstructionWeight θ)).re
  let D (M : ℕ) := (gowersCubePower 2 1 (M : ℤ) (fun _ => 1)).re
  have hA (M : ℕ) : 0 ≤ A M := gowersCubePower_re_nonnegative _ _ _ (by decide) _
  have hD (M : ℕ) : 0 ≤ D M := gowersCubePower_re_nonnegative _ _ _ (by decide) _
  have hRatio : Tendsto (fun M : ℕ => A M / D M) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show 0 < ε/32 by positivity)
    let K := k+2
    have hK : 2 ≤ K := by dsimp [K]; omega
    have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
    have hKsmall : (16 : ℝ)/K < ε := by
      have h : 1/(K : ℝ) ≤ 1/(k+1 : ℝ) :=
        one_div_le_one_div_of_le (by positivity) (by dsimp [K]; push_cast; linarith)
      have h' := h.trans_lt hk
      have : (16 : ℝ)/K = 16*(1/(K : ℝ)) := by ring
      linarith
    obtain ⟨δ, hδ, hCard⟩ := small_rotations_card_bound θ hθ K hK
    let E (M : ℕ) := (16 : ℝ)/K + 8*(M : ℝ)⁻¹ +
      24*(δ⁻¹)^2*((M : ℝ)⁻¹)^2
    have hInv : Tendsto (fun M : ℕ => (M : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have hE : Tendsto E atTop (𝓝 ((16 : ℝ)/K)) := by
      simpa only [E, mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero] using
        ((tendsto_const_nhds (x := (16 : ℝ)/K)).add (hInv.const_mul 8)).add
          ((hInv.pow 2).const_mul (24*(δ⁻¹)^2))
    filter_upwards [hE.eventually_lt_const hKsmall, eventually_gt_atTop 0] with M hEM hM
    have hMpos : 0 < (M : ℝ) := Nat.cast_pos.mpr hM
    have hDlo : (M : ℝ)^3/8 ≤ D M := gowers_two_one_lower hM
    have hDpos : 0 < D M := (by positivity : 0 < (M : ℝ)^3/8).trans_le hDlo
    have hAhi : A M ≤ (2*(M : ℝ)/K+1)*(M : ℝ)^2 + 3*M*(δ⁻¹)^2 :=
      gowers_two_quadratic_upper θ hM hδ (hCard M)
    rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hA M) (hD M))]
    calc
      A M / D M ≤ A M / ((M : ℝ)^3/8) :=
        div_le_div_of_nonneg_left (hA M) (by positivity) hDlo
      _ ≤ ((2*(M : ℝ)/K+1)*(M : ℝ)^2 + 3*M*(δ⁻¹)^2) / ((M : ℝ)^3/8) :=
        div_le_div_of_nonneg_right hAhi (by positivity)
      _ = E M := by dsimp [E]; field_simp [hMpos.ne', hKpos.ne', hδ.ne']; ring
      _ < ε := hEM
  have hExp : (0 : ℝ) < ((2 : ℝ)^2)⁻¹ := by positivity
  have hlim := ((Real.continuous_rpow_const hExp.le).tendsto 0).comp hRatio
  simpa only [Function.comp_def, Real.zero_rpow hExp.ne', Real.div_rpow (hA _) (hD _),
    normalizedGowers, A, D] using hlim

/-- At the quadratic family no scale-independent weighted count bound
in terms of the normalized U² norm alone can hold. -/
theorem no_uniform_weighted_gowers_two (θ : ℝ) (hθ : Irrational θ) :
    ¬ ∃ C : ℝ, ∀ M : ℕ, 0 < M → ∀ f : Fin 3 → ℤ → ℂ,
      (∀ i, SupportedOn (positiveInterval (2*M^2)) (f i)) →
      (∀ i x, ‖f i x‖ ≤ 1) →
      ‖countingForm (2*M^2) M (positiveInterval (2*M^2)) (separatingFamily 1)
          (quadraticObstructionWeight θ) f‖ ≤
        C * normalizedGowers 2 1 (M : ℤ) (quadraticObstructionWeight θ) := by
  rintro ⟨C, h⟩
  have hlim := (irrational_quadratic_gowers_two_tendsto_zero θ hθ).const_mul C
  have hsmall : ∀ᶠ M : ℕ in atTop,
      C * normalizedGowers 2 1 (M : ℤ) (quadraticObstructionWeight θ) < 1/2 := by
    rw [mul_zero] at hlim
    exact hlim.eventually_lt_const (by norm_num)
  obtain ⟨M, hM, hMsmall⟩ := ((eventually_gt_atTop 0).and hsmall).exists
  obtain ⟨f, hf, hb, he⟩ := quadratic_obstruction_common_window θ hM
  have hlarge := h M hM f hf hb
  have hTwo : ‖(2 : ℂ)‖ = 2 := by simp
  rw [he, norm_div, norm_one, hTwo] at hlarge
  exact (not_lt_of_ge hlarge) hMsmall

end NilBohr
