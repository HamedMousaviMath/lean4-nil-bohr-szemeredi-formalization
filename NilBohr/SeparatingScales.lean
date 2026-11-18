import NilBohr.LocalPhases
import NilBohr.LocalizedPrimeModel

/-! Finite identities for the separating family in Appendix A. -/

open Polynomial
open scoped BigOperators

namespace NilBohr

/-- The zero extension of a function from a dilated copy of the integers. -/
def dilatedWeight (q : ℕ) (v : ℤ → ℂ) (m : ℤ) : ℂ :=
  if (q : ℤ) ∣ m then v (m / (q : ℤ)) else 0

@[simp] theorem dilatedWeight_at_multiple {q : ℕ} (hq : 0 < q) (v : ℤ → ℂ) (y : ℤ) :
    dilatedWeight q v ((q : ℤ) * y) = v y := by
  have hqZ : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
  simp [dilatedWeight, Int.mul_ediv_cancel_left _ hqZ]

private theorem positiveInterval_multiples {q M : ℕ} (hq : 0 < q) :
    (positiveInterval (q * M)).filter (fun n => (q : ℤ) ∣ n) =
      (positiveInterval M).image (fun y : ℤ => (q : ℤ) * y) := by
  have hqZ : (0 : ℤ) < q := by exact_mod_cast hq
  ext n
  simp only [Finset.mem_filter, Finset.mem_image, positiveInterval, Finset.mem_Icc, Nat.cast_mul]
  constructor
  · rintro ⟨⟨hn, hnM⟩, ⟨y, rfl⟩⟩
    have hy : 0 < y := (mul_pos_iff_of_pos_left hqZ).mp (by omega)
    exact ⟨y, ⟨by omega, (mul_le_mul_left hqZ).mp hnM⟩, rfl⟩
  · rintro ⟨y, ⟨hy, hyM⟩, rfl⟩
    have hpos : 0 < (q : ℤ) * y := mul_pos hqZ (by omega)
    exact ⟨⟨by omega, mul_le_mul_of_nonneg_left hyM hqZ.le⟩, dvd_mul_right _ _⟩

/-- The exact (1/q) loss for a single ordinary polynomial phase under
zero extension to `qℤ`, with the rescaled phase (Q(qy)). -/
theorem phaseAverage_dilatedWeight {q M : ℕ} (hq : 0 < q) (v : ℤ → ℂ)
    (Q : Polynomial ℝ) :
    phaseAverage (positiveInterval (q*M)) (dilatedWeight q v) Q =
      phaseAverage (positiveInterval M) v (Q.comp (C (q : ℝ) * X)) / (q : ℂ) := by
  classical
  have hqZ : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
  have hsum :
      (∑ n ∈ positiveInterval (q*M), dilatedWeight q v n * phase (-(Q.eval (n : ℝ)))) =
      ∑ y ∈ positiveInterval M, v y * phase (-((Q.comp (C (q : ℝ) * X)).eval (y : ℝ))) := by
    calc
      _ = ∑ n ∈ (positiveInterval (q*M)).filter (fun n => (q : ℤ) ∣ n),
          dilatedWeight q v n * phase (-(Q.eval (n : ℝ))) := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro n _
        by_cases hn : (q : ℤ) ∣ n <;> simp [hn, dilatedWeight]
      _ = _ := by
        rw [positiveInterval_multiples hq,
          Finset.sum_image (fun x _ y _ h => mul_left_cancel₀ hqZ h)]
        apply Finset.sum_congr rfl
        intro y _
        simp [dilatedWeight_at_multiple hq, Polynomial.eval_comp]
  simp only [phaseAverage, card_positiveInterval, hsum, Nat.cast_mul]
  rw [div_div, mul_comm (M : ℂ)]

/-- Equation `e:lift-form` for the phase norm, including the converse
rescaling by (y=n/q). -/
theorem phaseNorm_dilatedWeight {s q M : ℕ} (hs : 0 < s) (hq : 0 < q) (v : ℤ → ℂ) :
    phaseNorm s (positiveInterval (q*M)) (dilatedWeight q v) =
      phaseNorm s (positiveInterval M) v / (q : ℝ) := by
  let P := positiveInterval M
  let I := positiveInterval (q*M)
  let w := dilatedWeight q v
  let L : Polynomial ℝ := C (q : ℝ) * X
  let Linv : Polynomial ℝ := C ((q : ℝ)⁻¹) * X
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hL : L.natDegree ≤ 1 := by
    exact (natDegree_C_mul_le _ _).trans (by simp)
  have hLinv : Linv.natDegree ≤ 1 := by
    exact (natDegree_C_mul_le _ _).trans (by simp)
  have hcompose (Q R : Polynomial ℝ) (hQ : Q.natDegree < s) (hR : R.natDegree ≤ 1) :
      (Q.comp R).natDegree < s :=
    (natDegree_comp_le.trans (by simpa using Nat.mul_le_mul_left Q.natDegree hR)).trans_lt hQ
  have hdil (Q : Polynomial ℝ) :
      ‖phaseAverage I w Q‖ = ‖phaseAverage P v (Q.comp L)‖ / (q : ℝ) := by
    rw [phaseAverage_dilatedWeight hq, norm_div, Complex.norm_natCast]
  have hInverses (Q : Polynomial ℝ) : (Q.comp Linv).comp L = Q := by
    rw [comp_assoc]
    have heq : Linv.comp L = X := by
      simp only [Linv, L, mul_comp, C_comp, X_comp, ← mul_assoc, ← C_mul,
        inv_mul_cancel₀ hqR.ne', C_1, one_mul]
    simp [heq]
  apply le_antisymm
  · unfold phaseNorm at ⊢
    refine csSup_le ⟨‖phaseAverage I w 0‖, 0, by simpa using hs, rfl⟩ ?_
    rintro c ⟨Q, hQ, rfl⟩
    change ‖phaseAverage I w Q‖ ≤ phaseNorm s P v / (q : ℝ)
    rw [hdil]
    exact div_le_div_of_nonneg_right (norm_phaseAverage_le_phaseNorm _ _ (hcompose Q L hQ hL)) hqR.le
  · apply (div_le_iff₀ hqR).2
    change phaseNorm s P v ≤ phaseNorm s I w * (q : ℝ)
    unfold phaseNorm
    refine csSup_le ⟨‖phaseAverage P v 0‖, 0, by simpa using hs, rfl⟩ ?_
    rintro c ⟨Q, hQ, rfl⟩
    change ‖phaseAverage P v Q‖ ≤ phaseNorm s I w * (q : ℝ)
    apply (div_le_iff₀ hqR).1
    rw [← hInverses Q, ← hdil]
    exact norm_phaseAverage_le_phaseNorm _ _ (hcompose Q Linv hQ hLinv)

/-- Restricting a polynomial test to the multiples of `r` costs no factor
in the ambient normalized bound. The indicator has a Fourier expansion of
absolute coefficient sum one, and each additional phase is linear. -/
theorem norm_phaseAverage_multiples_le_phaseNorm {s r : ℕ} (hs : 2 ≤ s) (hr : 0 < r)
    (I : Finset ℤ) (v : ℤ → ℂ) (Q : Polynomial ℝ) (hQ : Q.natDegree < s) :
    ‖phaseAverage I (fun y => if (r : ℤ) ∣ y then v y else 0) Q‖ ≤ phaseNorm s I v := by
  classical
  letI : NeZero r := ⟨hr.ne'⟩
  let χ (a : ZMod r) : Polynomial ℝ := Q - C ((a.val : ℝ) / (r : ℝ)) * X
  have hχ (a : ZMod r) : (χ a).natDegree < s := by
    dsimp [χ]
    refine (natDegree_sub_le _ _).trans_lt (max_lt hQ ?_)
    exact (natDegree_C_mul_le _ _).trans_lt (by simpa using (show 1 < s by omega))
  have hFour (y : ℤ) :
      (if (r : ℤ) ∣ y then (1 : ℂ) else 0) =
        ∑ a : ZMod r, (r : ℂ)⁻¹ * phase (((a.val : ℝ)/(r : ℝ)) * y) := by
    simpa [Int.modEq_zero_iff_dvd, phaseExponential, phase] using
      (residue_indicator_fourier r y 0)
  have hχEval (a : ZMod r) (y : ℤ) :
      phase (((a.val : ℝ)/(r : ℝ)) * y) * phase (-(Q.eval (y : ℝ))) =
        phase (-((χ a).eval (y : ℝ))) := by
    rw [← phase_add]
    congr 1
    simp only [χ, eval_sub, eval_mul, eval_C, eval_X]
    ring
  have hsum :
      (∑ y ∈ I, (if (r : ℤ) ∣ y then v y else 0) * phase (-(Q.eval (y : ℝ)))) =
        ∑ a : ZMod r, (r : ℂ)⁻¹ * (∑ y ∈ I, v y * phase (-((χ a).eval (y : ℝ)))) := by
    calc
      _ = ∑ y ∈ I, (∑ a : ZMod r, (r : ℂ)⁻¹ *
          (v y * phase (-((χ a).eval (y : ℝ))))) := by
        apply Finset.sum_congr rfl
        intro y _
        have hif : (if (r : ℤ) ∣ y then v y else 0) =
            (if (r : ℤ) ∣ y then (1 : ℂ) else 0) * v y := by
          split_ifs <;> simp
        rw [hif, hFour, Finset.sum_mul, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _
        rw [← hχEval]
        ring
      _ = _ := by rw [Finset.sum_comm]; simp_rw [Finset.mul_sum]
  have hAvg :
      phaseAverage I (fun y => if (r : ℤ) ∣ y then v y else 0) Q =
        ∑ a : ZMod r, (r : ℂ)⁻¹ * phaseAverage I v (χ a) := by
    unfold phaseAverage
    rw [hsum, Finset.sum_div]
    simp only [mul_div_assoc]
  rw [hAvg]
  refine (norm_sum_le _ _).trans ?_
  calc
    (∑ a : ZMod r, ‖(r : ℂ)⁻¹ * phaseAverage I v (χ a)‖) ≤
        ∑ _ : ZMod r, (r : ℝ)⁻¹ * phaseNorm s I v := by
      refine Finset.sum_le_sum (fun a _ => ?_)
      rw [norm_mul, norm_inv, Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_left (norm_phaseAverage_le_phaseNorm _ _ (hχ a)) (by positivity)
    _ = _ := by
      have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
      simp [ZMod.card, nsmul_eq_mul, ← mul_assoc, hrR]

/-- A correlation on the multiples of `r` inside `[rH]` supplies the
global ordinary phase-norm lower bound used in Proposition A.1. -/
theorem residueCorrelation_le_phaseNorm {s r H : ℕ} (hs : 2 ≤ s) (hr : 0 < r)
    (v : ℤ → ℂ) (Q : Polynomial ℝ) (hQ : Q.natDegree < s) :
    ‖phaseAverage (positiveInterval H) (fun t => v ((r : ℤ) * t))
        (Q.comp (C (r : ℝ) * X))‖ / (r : ℝ) ≤
      phaseNorm s (positiveInterval (r*H)) v := by
  have heq (y : ℤ) : (if (r : ℤ) ∣ y then v y else 0) =
      dilatedWeight r (fun t => v ((r : ℤ) * t)) y := by
    rcases Classical.em ((r : ℤ) ∣ y) with ⟨t, rfl⟩ | h
    · simp [dilatedWeight_at_multiple hr]
    · simp [h, dilatedWeight]
  have h := norm_phaseAverage_multiples_le_phaseNorm hs hr (positiveInterval (r*H)) v Q hQ
  simp_rw [heq, phaseAverage_dilatedWeight hr, norm_div, Complex.norm_natCast] at h
  exact h

/-- The quadratic matching the Heisenberg phase on an approximating
denominator's residue class. -/
noncomputable def separatingQuadratic (α : ℝ) (a r : ℤ) (q : ℕ) : Polynomial ℝ :=
  C (-α * ((a : ℝ) / r) / 2) *
    ((C (q : ℝ) * X)^2 + C (q : ℝ) * X)

theorem separatingQuadratic_natDegree_le (α : ℝ) (a r : ℤ) (q : ℕ) :
    (separatingQuadratic α a r q).natDegree ≤ 2 := by
  unfold separatingQuadratic
  have hL : (C (q : ℝ) * (X : Polynomial ℝ)).natDegree ≤ 1 :=
    (natDegree_C_mul_le _ _).trans (by simp)
  apply (natDegree_C_mul_le _ _).trans
  apply natDegree_add_le_of_degree_le
  · exact natDegree_pow_le.trans (by simpa using Nat.mul_le_mul_left 2 hL)
  · exact hL.trans (by decide)

/-- The approximation in `e:uniappzq` on all multiples of `r` in
`[M]`, with an explicit remainder constant. -/
theorem abs_heisenbergPhase_sub_separatingQuadratic_le (α β : ℝ) (a r : ℤ)
    (hr : r ≠ 0) {q M : ℕ} (hq : 0 < q) {y : ℤ} (hy : y ∈ positiveInterval M)
    (hdiv : r ∣ y) {E : ℝ} (hE : 0 ≤ β - (a : ℝ)/r)
    (hE' : β - (a : ℝ)/r ≤ E) (hsmall : E * ((q : ℝ) * M) < 1) :
    |heisenbergPhase α β ((q : ℤ) * y) - (separatingQuadratic α a r q).eval (y : ℝ)| ≤
      |α| * E * ((q : ℝ) * M)^2 / 2 := by
  let n := (q : ℤ) * y
  obtain ⟨hy₀, hy₁⟩ := Finset.mem_Icc.mp hy
  have hnZ : 1 ≤ n := by
    have hqZ : (0 : ℤ) < q := by exact_mod_cast hq
    have hp : 0 < (q : ℤ) * y := mul_pos hqZ (by omega)
    omega
  have hn₀ : (1 : ℝ) ≤ n := by exact_mod_cast hnZ
  have hn₁ : (n : ℝ) ≤ (q : ℝ) * M := by
    dsimp [n]
    exact_mod_cast mul_le_mul_of_nonneg_left hy₁ (show (0 : ℤ) ≤ q by positivity)
  have he₀ : 0 ≤ E := hE.trans hE'
  have he : (β - (a : ℝ)/r) * n < 1 :=
    (mul_le_mul hE' hn₁ (by linarith) he₀).trans_lt hsmall
  have hdiv' : r ∣ n := dvd_mul_of_dvd_right hdiv (q : ℤ)
  have hphase := heisenbergPhase_rational_residue α β a r n hr hdiv'
    (mul_nonneg hE (by linarith)) he
  have hpol : (separatingQuadratic α a r q).eval (y : ℝ) =
      -α * ((a : ℝ)/r) / 2 * ((n : ℝ)^2+(n : ℝ)) := by
    simp [separatingQuadratic, n]
  change |heisenbergPhase α β n - (separatingQuadratic α a r q).eval (y : ℝ)| ≤ _
  rw [hphase, hpol, add_sub_cancel_left, abs_mul, abs_div, abs_mul, abs_of_nonneg hE,
    abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  have hnpos : 0 ≤ (n : ℝ) := zero_le_one.trans hn₀
  have hquad : 0 ≤ (n : ℝ)^2 - n := by
    nlinarith only [mul_nonneg hnpos (sub_nonneg.mpr hn₀)]
  have hscale : (n : ℝ)^2 - n ≤ ((q : ℝ) * M)^2 := by
    have hsq : (n : ℝ)^2 ≤ ((q : ℝ) * M)^2 :=
      pow_le_pow_left₀ hnpos hn₁ _
    linarith only [hsq, hnpos]
  rw [abs_of_nonneg hquad]
  have hfirst : |α| * (β - (a : ℝ)/r) ≤ |α| * E :=
    mul_le_mul_of_nonneg_left hE' (abs_nonneg _)
  have hmain := mul_le_mul hfirst hscale hquad (mul_nonneg (abs_nonneg _) he₀)
  convert div_le_div_of_nonneg_right hmain (by norm_num : (0 : ℝ) ≤ 2) using 1
  ring


/-- The spatial scale in Appendix A gives the exact parameter length of
Theorem 4.2. -/
theorem parameterLength_separatingFamily (M : ℕ) {q : ℕ} (hq : 0 < q) :
    parameterLength (q*M^2) q 2 = M := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  unfold parameterLength
  simp only [show 2 - 1 = (1 : ℕ) by decide, pow_one, Nat.cast_mul, Nat.cast_pow]
  rw [mul_comm (q : ℝ), mul_div_cancel_right₀ _ hqR,
    ← Real.rpow_natCast_mul (Nat.cast_nonneg M)]
  norm_num

/-- The ordered family (0,y,qy^2) in Appendix A. -/
noncomputable def separatingFamily (q : ℕ) : Fin 3 → Polynomial ℤ :=
  ![0, X, C (q : ℤ) * X^2]

/-- The centered vertical weight on the parameter variable in Appendix A. -/
noncomputable def separatingWeight (α β : ℝ) (F : Circle → ℂ) (q : ℕ) (y : ℤ) : ℂ :=
  selectorWeight (heisenbergPhase α β) F q y - circleMean F

private theorem eval_separatingFamily_dilate (q : ℕ) (i : Fin 3) (y : ℤ) :
    (separatingFamily 1 i).eval ((q : ℤ) * y) =
      (q : ℤ) * (separatingFamily q i).eval y := by
  fin_cases i
  · simp [separatingFamily]
  · simp [separatingFamily]
  · simp [separatingFamily]
    ring

/-- The exact count identity of Appendix A for zero-extension to `qℤ`.
The image window contains precisely the surviving base coordinates.
Specializing `N = q*M^2` gives the fixed-family spatial scale `(q*M)^2`. -/
theorem countingForm_separatingFamily_dilate {N M q : ℕ}
    (hN : 0 < N) (hM : 0 < M) (hq : 0 < q) (I : Finset ℤ)
    (v : ℤ → ℂ) (f : Fin 3 → ℤ → ℂ) :
    countingForm N M I (separatingFamily q) v f =
      (q : ℂ)^2 * countingForm (q*N) (q*M)
        (I.image (fun x : ℤ => (q : ℤ)*x)) (separatingFamily 1)
        (dilatedWeight q v) (fun i => dilatedWeight q (f i)) := by
  classical
  have hqZ : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
  have hinj : Function.Injective (fun x : ℤ => (q : ℤ)*x) :=
    fun _ _ h => mul_left_cancel₀ hqZ h
  have hnum :
      (∑ m ∈ I.image (fun x : ℤ => (q : ℤ)*x), ∑ n ∈ positiveInterval (q*M),
        dilatedWeight q v n *
          ∏ i : Fin 3, dilatedWeight q (f i) (m + (separatingFamily 1 i).eval n)) =
      ∑ x ∈ I, ∑ y ∈ positiveInterval M,
        v y * ∏ i : Fin 3, f i (x + (separatingFamily q i).eval y) := by
    rw [Finset.sum_image (fun _ _ _ _ h => hinj h)]
    apply Finset.sum_congr rfl
    intro x _
    calc
      _ = ∑ n ∈ (positiveInterval (q*M)).filter (fun n => (q : ℤ) ∣ n),
          dilatedWeight q v n *
            ∏ i : Fin 3, dilatedWeight q (f i)
              ((q : ℤ)*x + (separatingFamily 1 i).eval n) := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro n _
        by_cases hn : (q : ℤ) ∣ n <;> simp [hn, dilatedWeight]
      _ = _ := by
        rw [positiveInterval_multiples hq, Finset.sum_image (fun _ _ _ _ h => hinj h)]
        apply Finset.sum_congr rfl
        intro y _
        simp only [eval_separatingFamily_dilate, ← mul_add, dilatedWeight_at_multiple hq]
  simp only [countingForm, hnum, Nat.cast_mul]
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hMC : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  field_simp [hqC, hNC, hMC]
  ring


/-- The base variable after repeating each spatial input on all residue
classes. Quotient and remainder distinguish all positions in this window. -/
def repeatedSpatialWindow (q : ℕ) (I : Finset ℤ) : Finset ℤ :=
  (I ×ˢ Finset.range q).image (fun p : ℤ × ℕ => (q : ℤ)*p.1+(p.2 : ℤ))

private theorem repeat_position_ediv {q a : ℕ} (ha : a < q) (x : ℤ) :
    ((q : ℤ)*x+(a : ℤ)) / (q : ℤ) = x := by
  have hq : (q : ℤ) ≠ 0 := by exact_mod_cast (Nat.zero_lt_of_lt ha).ne'
  rw [Int.mul_add_ediv_left _ _ hq,
    Int.ediv_eq_zero_of_lt (by positivity) (by exact_mod_cast ha), add_zero]

private theorem repeat_position_emod {q a : ℕ} (ha : a < q) (x : ℤ) :
    ((q : ℤ)*x+(a : ℤ)) % (q : ℤ) = (a : ℤ) := by
  rw [add_comm, Int.add_mul_emod_self_left,
    Int.emod_eq_of_lt (by positivity) (by exact_mod_cast ha)]

/-- Repeating the spatial inputs on all `q` residue classes increases the
lifted numerator by exactly `q`, giving the second normalization identity
in Appendix A. The parameter weight is still extended by zero. -/
theorem countingForm_separatingFamily_repeat {N M q : ℕ}
    (hN : 0 < N) (hM : 0 < M) (hq : 0 < q) (I : Finset ℤ)
    (v : ℤ → ℂ) (f : Fin 3 → ℤ → ℂ) :
    countingForm N M I (separatingFamily q) v f =
      (q : ℂ) * countingForm (q*N) (q*M) (repeatedSpatialWindow q I)
        (separatingFamily 1) (dilatedWeight q v) (fun i x => f i (x / (q : ℤ))) := by
  classical
  let pos (p : ℤ × ℕ) := (q : ℤ)*p.1+(p.2 : ℤ)
  have hqZ : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
  have hinjQ : Function.Injective (fun x : ℤ => (q : ℤ)*x) :=
    fun _ _ h => mul_left_cancel₀ hqZ h
  have hinj : Set.InjOn pos ↑(I ×ˢ Finset.range q) := by
    intro a ha b hb hab
    have ha' := Finset.mem_range.mp (Finset.mem_product.mp ha).2
    have hb' := Finset.mem_range.mp (Finset.mem_product.mp hb).2
    apply Prod.ext
    · simpa only [pos, repeat_position_ediv ha', repeat_position_ediv hb'] using
        congrArg (fun m : ℤ => m / (q : ℤ)) hab
    · exact_mod_cast (show (a.2 : ℤ) = (b.2 : ℤ) by
        simpa only [pos, repeat_position_emod ha', repeat_position_emod hb'] using
          congrArg (fun m : ℤ => m % (q : ℤ)) hab)
  let num (x : ℤ) := ∑ y ∈ positiveInterval M,
    v y * ∏ i : Fin 3, f i (x + (separatingFamily q i).eval y)
  have hnum :
      (∑ m ∈ repeatedSpatialWindow q I, ∑ n ∈ positiveInterval (q*M),
        dilatedWeight q v n *
          ∏ i : Fin 3, f i ((m + (separatingFamily 1 i).eval n) / (q : ℤ))) =
      (q : ℂ) * ∑ x ∈ I, num x := by
    change (∑ m ∈ (I ×ˢ Finset.range q).image pos, _) = _
    rw [Finset.sum_image hinj]
    calc
      _ = ∑ p ∈ I ×ˢ Finset.range q, num p.1 := by
        apply Finset.sum_congr rfl
        intro p hp
        have hpq := Finset.mem_range.mp (Finset.mem_product.mp hp).2
        calc
          _ = ∑ n ∈ (positiveInterval (q*M)).filter (fun n => (q : ℤ) ∣ n),
              dilatedWeight q v n *
                ∏ i : Fin 3, f i ((pos p + (separatingFamily 1 i).eval n) / (q : ℤ)) := by
            rw [Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro n _
            by_cases hn : (q : ℤ) ∣ n <;> simp [hn, dilatedWeight]
          _ = _ := by
            rw [positiveInterval_multiples hq, Finset.sum_image (fun _ _ _ _ h => hinjQ h)]
            apply Finset.sum_congr rfl
            intro y _
            have hpos (i : Fin 3) : pos p + (separatingFamily 1 i).eval ((q : ℤ)*y) =
                (q : ℤ)*(p.1 + (separatingFamily q i).eval y)+(p.2 : ℤ) := by
              rw [eval_separatingFamily_dilate]
              dsimp [pos]
              ring
            simp only [dilatedWeight_at_multiple hq, hpos, repeat_position_ediv hpq]
      _ = _ := by
        rw [Finset.sum_product, Finset.mul_sum]
        simp [nsmul_eq_mul]
  simp only [countingForm, hnum, Nat.cast_mul]
  change (∑ x ∈ I, num x) / ((N : ℂ)*(M : ℂ)) = _
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hMC : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  field_simp [hqC, hNC, hMC]
  ring

end NilBohr
