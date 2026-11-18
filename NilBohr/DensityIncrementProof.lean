import NilBohr.DensityRegularity
import NilBohr.DensityParameters
import NilBohr.ArcApproximation

/-! Uniform model positivity and the quantitative density increment. -/

open Filter
open scoped BigOperators Topology

namespace NilBohr

/-- The floored parameter length never exceeds the defining power scale. -/
theorem parameterLength_power_le {N q d : ℕ} (hq : 0 < q) (hd : 0 < d) :
    (q : ℝ)^(d - 1) * (parameterLength N q d : ℝ)^d ≤ N := by
  let Q := (q : ℝ)^(d - 1)
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hs : 0 ≤ (N : ℝ) / Q := div_nonneg (Nat.cast_nonneg _) hQ.le
  have hfloor : (parameterLength N q d : ℝ) ≤ ((N : ℝ) / Q)^((d : ℝ)⁻¹) :=
    Nat.floor_le (Real.rpow_nonneg hs _)
  calc
    _ ≤ Q * ((((N : ℝ) / Q)^((d : ℝ)⁻¹))^d) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hfloor _) hQ.le
    _ = N := by rw [Real.rpow_inv_natCast_pow hs hd.ne', mul_div_cancel₀ _ hQ.ne']

private theorem eval_abs_le_of_hasCoefficients {C : ℝ} {q : ℕ} {P : Polynomial ℤ}
    (hP : HasCoefficients C q P) (y : ℤ) (hy : 1 ≤ y) :
    |((P.eval y : ℤ) : ℝ)| ≤ C^2 * ((P.natDegree + 1 : ℕ) : ℝ) *
      (q : ℝ)^(P.natDegree - 1) * (y : ℝ)^P.natDegree := by
  obtain ⟨hC, hq, hd, hconst, hcoeff, a, _, haC, hlead⟩ := hP
  let e := P.natDegree
  let Q := (q : ℝ)^(e-1)
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hC₀ : 0 ≤ C := by linarith
  have hleadR : |(P.leadingCoeff : ℝ)| ≤ C * Q := by
    have heq : (P.leadingCoeff : ℝ) = (a : ℝ) * Q := by
      dsimp [Q, e]
      exact_mod_cast hlead
    rw [heq, abs_mul, abs_of_nonneg hQ]
    exact mul_le_mul_of_nonneg_right haC hQ
  have hcoef (j : ℕ) (hj : j ≤ e) : |(P.coeff j : ℝ)| ≤ C^2 * Q := by
    by_cases hzero : j = 0
    · simp only [hzero, hconst, Int.cast_zero, abs_zero]
      exact mul_nonneg (sq_nonneg _) hQ
    rcases eq_or_lt_of_le hj with rfl | hj'
    · rw [Polynomial.coeff_natDegree]
      exact hleadR.trans (mul_le_mul_of_nonneg_right (by nlinarith) hQ)
    · exact (hcoeff j (by omega) hj').trans
        (by simpa only [pow_two, mul_assoc] using
          mul_le_mul_of_nonneg_left hleadR hC₀)
  have hyR : 1 ≤ (y : ℝ) := by exact_mod_cast hy
  have hev : ((P.eval y : ℤ) : ℝ) =
      ∑ j ∈ Finset.range (e+1), (P.coeff j : ℝ) * (y : ℝ)^j := by
    rw [Polynomial.eval_eq_sum_range]
    push_cast
    rfl
  calc
    _ = |∑ j ∈ Finset.range (e+1), (P.coeff j : ℝ) * (y : ℝ)^j| := by rw [hev]
    _ ≤ ∑ j ∈ Finset.range (e+1), |(P.coeff j : ℝ) * (y : ℝ)^j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range (e+1), (C^2 * Q) * (y : ℝ)^e := by
      refine Finset.sum_le_sum (fun j hj => ?_)
      have hj' : j ≤ e := by have := Finset.mem_range.mp hj; omega
      rw [abs_mul, abs_of_nonneg (pow_nonneg (zero_le_one.trans hyR) _)]
      exact mul_le_mul (hcoef j hj') (pow_le_pow_right₀ hyR hj')
        (by positivity) (by positivity)
    _ = _ := by simp [Q, e]; ring

/-- A uniform short-parameter cutoff for the constant-density model count. -/
noncomputable def densityModelCutoff (C : ℝ) (d : ℕ) : ℝ :=
  (4 * C^2 * ((d : ℝ) + 1))⁻¹

/-- The lower bound from (3.1) of the proof, including a floor-safe
parameter cutoff and a coefficient-uniform positive constant. -/
theorem density_model_lower_from_coefficients {N q d ℓ : ℕ} {C : ℝ}
    (hC : 1 ≤ C) (hN : 0 < N) (hq : 0 < q) (hd : 0 < d)
    (P : Fin (ℓ + 1) → Polynomial ℤ) (hP₀ : P 0 = 0)
    (hdeg : ∀ i, (P i).natDegree ≤ d)
    (hcoeff : ∀ i, i ≠ 0 → HasCoefficients C q (P i))
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hlarge : 2 ≤ densityModelCutoff C d * (parameterLength N q d : ℝ)) :
    densityModelCutoff C d / 4 * δ^(ℓ + 1) ≤
      ‖countingForm N (parameterLength N q d) (positiveInterval N) P
        (fun _ => 1) (fun _ => densityModel N δ)‖ := by
  let τ := densityModelCutoff C d
  let M := parameterLength N q d
  have hτ : 0 < τ := by dsimp [τ, densityModelCutoff]; positivity
  have hτ₁ : τ ≤ 1 := by
    dsimp [τ, densityModelCutoff]
    apply inv_le_one_of_one_le₀
    have hdR : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    nlinarith [mul_nonneg (show 0 ≤ C^2 - 1 by nlinarith) hdR]
  have hM : 0 < M := by
    by_contra! hM
    have hM' : M = 0 := by omega
    change 2 ≤ τ * (M : ℝ) at hlarge
    simp [hM'] at hlarge
    linarith
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  let m := ⌊τ * (M : ℝ)⌋₊
  let Y := positiveInterval m
  have hY : Y ⊆ positiveInterval M := by
    intro y hy
    apply Finset.mem_Icc.mpr
    have h := Finset.mem_Icc.mp hy
    have hm : m ≤ M := Nat.floor_le_of_le (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hτ₁ hMR.le)
    exact ⟨h.1, h.2.trans (by exact_mod_cast hm)⟩
  have hshift (y : ℤ) (hy : y ∈ Y) (i : Fin (ℓ + 1)) :
      |(P i).eval y| ≤ ((N / 4 : ℕ) : ℤ) := by
    by_cases hi : i = 0
    · simp only [hi, hP₀, Polynomial.eval_zero, abs_zero]; positivity
    let e := (P i).natDegree
    have he : 0 < e := (hcoeff i hi).2.2.1
    have hed : e ≤ d := hdeg i
    have hy1 := (Finset.mem_Icc.mp hy).1
    have hyR : (1 : ℝ) ≤ y := by exact_mod_cast hy1
    have hym := (Finset.mem_Icc.mp hy).2
    have hymR : (y : ℝ) ≤ (m : ℝ) := by exact_mod_cast hym
    have hyτ : (y : ℝ) ≤ τ * (M : ℝ) :=
      hymR.trans (Nat.floor_le (mul_nonneg hτ.le hMR.le))
    have hyM : (y : ℝ) ≤ M :=
      hyτ.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hτ₁ hMR.le)
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hpy : (y : ℝ)^e ≤ (τ * (M : ℝ)) * (M : ℝ)^(e - 1) := by
      calc
        _ = (y : ℝ) * (y : ℝ)^(e - 1) := by
          rw [← pow_succ', Nat.sub_add_cancel (Nat.succ_le_of_lt he)]
        _ ≤ _ := mul_le_mul hyτ (pow_le_pow_left₀ (zero_le_one.trans hyR) hyM _)
          (by positivity) (by positivity)
    have hbase : C^2 * ((e + 1 : ℕ) : ℝ) * (q : ℝ)^(e - 1) ≤
        C^2 * ((d : ℝ) + 1) * (q : ℝ)^(d - 1) := by
      have hdegR : ((e + 1 : ℕ) : ℝ) ≤ (d : ℝ) + 1 := by
        exact_mod_cast Nat.add_le_add_right hed 1
      exact mul_le_mul (mul_le_mul_of_nonneg_left hdegR (sq_nonneg C))
        (pow_le_pow_right₀ hq1 (Nat.sub_le_sub_right hed 1)) (by positivity) (by positivity)
    have hMy : (M : ℝ) * (M : ℝ)^(e - 1) ≤ (M : ℝ)^d := by
      rw [← pow_succ', Nat.sub_add_cancel (Nat.succ_le_of_lt he)]
      exact pow_le_pow_right₀ hM1 hed
    have hquarter : |(((P i).eval y : ℤ) : ℝ)| ≤ (N : ℝ) / 4 := calc
      _ ≤ C^2 * ((e + 1 : ℕ) : ℝ) * (q : ℝ)^(e - 1) * (y : ℝ)^e :=
        eval_abs_le_of_hasCoefficients (hcoeff i hi) y hy1
      _ ≤ C^2 * ((d : ℝ) + 1) * (q : ℝ)^(d - 1) *
          ((τ * (M : ℝ)) * (M : ℝ)^(e - 1)) := by
        exact mul_le_mul hbase hpy (by positivity) (by positivity)
      _ ≤ C^2 * ((d : ℝ) + 1) * (q : ℝ)^(d - 1) *
          (τ * (M : ℝ)^d) := by
        rw [mul_assoc τ]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hMy hτ.le) (by positivity)
      _ = ((q : ℝ)^(d - 1) * (M : ℝ)^d) / 4 := by
        dsimp [τ, densityModelCutoff]
        have hC' : C ≠ 0 := by linarith
        have hd' : (d : ℝ) + 1 ≠ 0 := by positivity
        field_simp
        ring
      _ ≤ _ := div_le_div_of_nonneg_right (parameterLength_power_le hq hd) (by norm_num)
    have hfour : (4 : ℤ) * |(P i).eval y| ≤ (N : ℤ) := by
      exact_mod_cast (show (4 : ℝ) * |(((P i).eval y : ℤ) : ℝ)| ≤ (N : ℝ) by linarith)
    omega
  have hm : τ * (M : ℝ) / 2 ≤ (m : ℝ) := by
    have hf := Nat.lt_floor_add_one (τ * (M : ℝ))
    change 2 ≤ τ * (M : ℝ) at hlarge
    change τ * (M : ℝ) < (m : ℝ) + 1 at hf
    linarith
  have hratio : τ / 4 ≤ (Y.card : ℝ) / (2 * (M : ℝ)) := by
    change τ / 4 ≤ ((positiveInterval m).card : ℝ) / (2 * (M : ℝ))
    rw [card_positiveInterval]
    apply (le_div_iff₀ (by positivity)).mpr
    linarith
  exact (mul_le_mul_of_nonneg_right hratio (pow_nonneg hδ _)).trans
    (density_model_count_lower hN hM P Y hY hshift hδ)

/-- The coefficients of the original finite polynomial family have a single
bound, before rescaling. -/
theorem exists_family_coefficientBound {ℓ : ℕ} (P : Fin (ℓ + 1) → Polynomial ℤ)
    (hP : FixedPolynomialFamily P) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ i, i ≠ 0 → HasCoefficients C 1 (P i) := by
  let bound (i : Fin (ℓ + 1)) := (Finset.range ((P i).natDegree + 1)).sup
    (fun j => ((P i).coeff j).natAbs)
  let C := max 1 ((Finset.univ : Finset (Fin (ℓ + 1))).sup bound)
  have hC : (1 : ℝ) ≤ C := by
    exact_mod_cast (le_max_left 1 ((Finset.univ : Finset (Fin (ℓ+1))).sup bound))
  have hc (i : Fin (ℓ + 1)) (j : ℕ) (hj : j ≤ (P i).natDegree) :
      |(((P i).coeff j : ℤ) : ℝ)| ≤ (C : ℝ) := by
    have h₁ : ((P i).coeff j).natAbs ≤ bound i := Finset.le_sup (f :=
      fun j => ((P i).coeff j).natAbs) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
    have h₂ : bound i ≤ (Finset.univ : Finset (Fin (ℓ + 1))).sup bound :=
      Finset.le_sup (Finset.mem_univ i)
    have h₃ : ((P i).coeff j).natAbs ≤ C := h₁.trans (h₂.trans (le_max_right _ _))
    rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
    exact_mod_cast h₃
  refine ⟨C, hC, ?_⟩
  intro i hi
  have hid : 0 < (P i).natDegree := by
    have hi' : (0 : Fin (ℓ + 1)) < i := Fin.pos_iff_ne_zero.mpr hi
    have hdeg := hP.2.2.2 hi'
    simpa only [hP.2.1, Polynomial.natDegree_zero] using hdeg
  have hlead_ne : (P i).leadingCoeff ≠ 0 := by
    apply Polynomial.leadingCoeff_ne_zero.mpr
    intro he
    rw [he, Polynomial.natDegree_zero] at hid
    omega
  have hlead₁ : (1 : ℝ) ≤ |((P i).leadingCoeff : ℝ)| := by
    exact_mod_cast (show (1 : ℤ) ≤ |(P i).leadingCoeff| by
      have hp := abs_pos.mpr hlead_ne
      omega)
  refine ⟨hC, by decide, hid, hP.2.2.1 i, ?_, (P i).leadingCoeff, by linarith, ?_, by simp⟩
  · intro j _ hj
    exact (hc i j hj.le).trans (le_mul_of_one_le_right (by linarith : 0 ≤ (C : ℝ)) hlead₁)
  · simpa only [Polynomial.coeff_natDegree] using hc i (P i).natDegree le_rfl

/-- Coefficient scaling leaves the index order, degrees and zero shifts
unchanged. -/
theorem fixedPolynomialFamily_rescale {ℓ q : ℕ} (hq : 0 < q)
    (P : Fin (ℓ + 1) → Polynomial ℤ) (hP : FixedPolynomialFamily P) :
    FixedPolynomialFamily (fun i => rescalePolynomial q (P i)) := by
  have hq' : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
  refine ⟨hP.1, ?_, fun i => coeff_zero_rescalePolynomial _ _, ?_⟩
  · simp [hP.2.1, rescalePolynomial]
  · simpa only [natDegree_rescalePolynomial _ _ hq'] using hP.2.2.2

/-- Including $16$ in the least common multiple absorbs the extra factor
of eight on top of the product of all the distinct primes up to the cutoff. -/
theorem eight_mul_primeProduct_dvd_initialModulus {w : ℕ} (hw : 16 ≤ w) :
    8 * (∏ p ∈ primesThrough w, p) ∣ initialModulus w := by
  classical
  let e (p : ℕ) := if p = 2 then 4 else 1
  have hp (p : ℕ) (hp : p ∈ primesThrough w) : p.Prime ∧ p ≤ w := by
    have h := Finset.mem_filter.mp hp
    exact ⟨h.2, Nat.lt_succ_iff.mp (Finset.mem_range.mp h.1)⟩
  have htwo : 2 ∈ primesThrough w :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Nat.prime_two⟩
  have hdiv : (∏ p ∈ primesThrough w, p^e p) ∣ initialModulus w := by
    refine Finset.prod_dvd_of_isRelPrime (fun p hp' r hr' hne => ?_) (fun p hp' => ?_)
    · apply Nat.coprime_iff_isRelPrime.mp
      have hc := (Nat.coprime_primes (hp p hp').1 (hp r hr').1).mpr hne
      exact (hc.pow_left _).pow_right _
    · unfold initialModulus
      apply Finset.dvd_lcm
      apply Finset.mem_Icc.mpr
      by_cases h : p = 2
      · subst p
        norm_num [e]
        exact hw
      · simpa [e, h] using ⟨(hp p hp').1.one_le, (hp p hp').2⟩
  have hEq : (∏ p ∈ primesThrough w, p^e p) = 8 * (∏ p ∈ primesThrough w, p) := by
    rw [← Finset.mul_prod_erase _ _ htwo, ← Finset.mul_prod_erase _ _ htwo]
    simp only [e, if_true]
    have hprod :
        (∏ x ∈ (primesThrough w).erase 2, x^(if x = 2 then 4 else 1)) =
        ∏ x ∈ (primesThrough w).erase 2, x := by
      refine Finset.prod_congr rfl (fun x hx => ?_)
      simp [(Finset.mem_erase.mp hx).1]
    rw [hprod]
    ring
  rw [← hEq]
  exact hdiv

end NilBohr
