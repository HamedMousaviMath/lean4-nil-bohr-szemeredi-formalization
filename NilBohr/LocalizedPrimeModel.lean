import NilBohr.GowersMultiplier
import NilBohr.PolynomialGowers
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.NumberTheory.Harmonic.Bounds

/-! Finite restriction of the localized prime model to an integer
progression. The normalization of each mean is explicit. -/

open AddCircle Polynomial
open scoped BigOperators ComplexConjugate

namespace NilBohr

private theorem phaseExponential_add (x y : ℝ) :
    phaseExponential (x+y) = phaseExponential x * phaseExponential y := by
  unfold phaseExponential
  rw [Complex.ofReal_add, mul_add, Complex.exp_add]

private theorem norm_sum_restrict_by_fourier {ι : Type*} (X : ℕ) {J : Finset ℤ}
    (hJ : J ⊆ positiveInterval X) (hJ₀ : J.Nonempty)
    (I : Finset ι) (c : ι → ℂ) (θ : ι → ℝ)
    (hFourier : ∀ m ∈ positiveInterval X,
      (if m ∈ J then (1 : ℂ) else 0) =
        ∑ i ∈ I, c i * phaseExponential (θ i * (m : ℝ)))
    (v : ℤ → ℂ) (D : ℝ)
    (hBound : ∀ t : ℝ,
      ‖(∑ m ∈ positiveInterval X, v m * phaseExponential (t*(m : ℝ))) / (X : ℂ)‖ ≤ D) :
    ‖(∑ m ∈ J, v m) / (J.card : ℂ)‖ ≤
      ((X : ℝ) / (J.card : ℝ)) * (∑ i ∈ I, ‖c i‖) * D := by
  classical
  have hX₀ : 0 < X := by
    have ⟨m, hm⟩ := hJ₀
    by_contra! h
    have hX : X = 0 := by omega
    have : m ∈ positiveInterval 0 := hX ▸ hJ hm
    rw [show positiveInterval 0 = ∅ by ext x; simp [positiveInterval]] at this
    simp at this
  have hXc : (X : ℂ) ≠ 0 := by exact_mod_cast hX₀.ne'
  have hJc : (J.card : ℂ) ≠ 0 := by exact_mod_cast hJ₀.card_pos.ne'
  have hs : (∑ m ∈ J, v m) =
      ∑ i ∈ I, c i*(∑ m ∈ positiveInterval X, v m * phaseExponential (θ i * (m : ℝ))) := by
    have hFilter : (positiveInterval X).filter (· ∈ J) = J :=
      Finset.filter_mem_eq_inter.trans (Finset.inter_eq_right.mpr hJ)
    calc
      (∑ m ∈ J, v m) = ∑ m ∈ positiveInterval X, (if m ∈ J then (1 : ℂ) else 0) * v m := by
        simpa only [Finset.sum_filter, ite_mul, one_mul, zero_mul] using
          congrArg (fun A : Finset ℤ => ∑ m ∈ A, v m) hFilter.symm
      _ = ∑ m ∈ positiveInterval X, ∑ i ∈ I,
          c i * (v m*phaseExponential (θ i * (m : ℝ))) := by
        refine Finset.sum_congr rfl fun m hm => ?_
        rw [hFourier m hm, Finset.sum_mul]
        exact Finset.sum_congr rfl fun _ _ => by ring
      _ = _ := by rw [Finset.sum_comm]; simp_rw [← Finset.mul_sum]
  have heq :
      (∑ m ∈ J, v m) / (J.card : ℂ) =
        ((X : ℂ)/(J.card : ℂ)) * ∑ i ∈ I, c i *
          ((∑ m ∈ positiveInterval X, v m * phaseExponential (θ i * (m : ℝ))) / (X : ℂ)) := by
    rw [hs, Finset.mul_sum, Finset.sum_div]
    exact Finset.sum_congr rfl fun _ _ => by field_simp; ring
  rw [heq, norm_mul, norm_div, Complex.norm_natCast, Complex.norm_natCast]
  calc
    ((X : ℝ)/(J.card : ℝ)) *
        ‖∑ i ∈ I, c i * ((∑ m ∈ positiveInterval X,
          v m * phaseExponential (θ i * (m : ℝ))) / (X : ℂ))‖ ≤
        ((X : ℝ)/(J.card : ℝ)) * ∑ i ∈ I, ‖c i‖*D := by
      apply mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans ?_) (by positivity)
      refine Finset.sum_le_sum fun i _ => ?_
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hBound (θ i)) (norm_nonneg _)
    _ = _ := by rw [← Finset.sum_mul, mul_assoc]

/-- The finite restriction estimate in (diffgowersnorm). The coefficient
sum of the progression indicator is explicit in this lemma, allowing the
independent cyclic Fourier bounds to be applied to the same normalization. -/
theorem localized_prime_model_replacement_of_expansion {ι : Type*}
    (X S : ℕ) (hX : 0 < X) (hS : 3 ≤ S) (hG : NormalizedGowersLaws S)
    (D : ℝ) (hD : 0 < D) (hMean : ∀ f : ℤ → ℂ,
      ‖(∑ m ∈ positiveInterval X, f m) / (X : ℂ)‖ ≤
        D * normalizedGowers S 1 (X : ℤ) f)
    (u : ℤ → ℂ) (χ : C(Circle,ℂ)) (hAbs : Summable fun n : ℤ => ‖fourierCoeff χ n‖)
    (lo hi : ℝ) (hshort : 2*(hi-lo) < 1)
    (hχ : ∀ t : ℝ, t ∈ Set.Ico (0 : ℝ) 1 → χ (t : Circle) ≠ 0 → t ∈ Set.Icc lo hi)
    (α β : ℝ) (h : ℤ) (Q : ℝ[X]) (hQ : Q.natDegree < S)
    (J : Finset ℤ) (hJ : J ⊆ positiveInterval X) (hJ₀ : J.Nonempty)
    (I : Finset ι) (c : ι → ℂ) (θ : ι → ℝ)
    (hFourier : ∀ m ∈ positiveInterval X,
      (if m ∈ J then (1 : ℂ) else 0) =
        ∑ i ∈ I, c i * phaseExponential (θ i * (m : ℝ))) :
    ‖(∑ m ∈ J, u m * χ ((β*((m-1 : ℤ) : ℝ) : ℝ) : Circle) *
      phaseExponential ((h : ℝ)*heisenbergPhase α β (m-1)-Q.eval (m : ℝ))) / (J.card : ℂ)‖ ≤
        ((X : ℝ)/(J.card : ℝ)) * (∑ i ∈ I, ‖c i‖) *
          (D * (∑' n : ℤ, ‖fourierCoeff χ n‖) * normalizedGowers S 1 (X : ℤ) u) := by
  let w (m : ℤ) := u m * χ ((β*((m-1 : ℤ) : ℝ) : ℝ) : Circle) *
    phaseExponential ((h : ℝ)*heisenbergPhase α β (m-1))
  let v (m : ℤ) := u m * χ ((β*((m-1 : ℤ) : ℝ) : ℝ) : Circle) *
    phaseExponential ((h : ℝ)*heisenbergPhase α β (m-1)-Q.eval (m : ℝ))
  apply norm_sum_restrict_by_fourier X hJ hJ₀ I c θ hFourier v
  intro t
  let P : ℝ[X] := C t * Polynomial.X - Q
  have hP : P.natDegree < S := by
    apply (natDegree_sub_le _ _).trans_lt
    apply max_lt
    · have h : (C t * (Polynomial.X : ℝ[X])).natDegree ≤ 1 := by
        simpa using (natDegree_mul_le (p := C t) (q := Polynomial.X))
      exact h.trans_lt (by omega)
    · exact hQ
  have hEval (m : ℤ) : P.eval (m : ℝ) = t*(m : ℝ)-Q.eval (m : ℝ) := by simp [P]
  have heq (m : ℤ) : v m * phaseExponential (t*(m : ℝ)) =
      w m * phaseExponential (P.eval (m : ℝ)) := by
    rw [hEval]
    dsimp only [v, w]
    simp only [mul_assoc, ← phaseExponential_add]
    congr 3
    ring
  have hXI : (1 : ℤ) ≤ X := by exact_mod_cast hX
  have hGower : normalizedGowers S 1 (X : ℤ) w ≤
      (∑' n : ℤ, ‖fourierCoeff χ n‖) * normalizedGowers S 1 (X : ℤ) u := by
    simpa [w, sub_eq_add_neg, add_comm] using
      localized_vertical_fourier_multiplier 1 (X : ℤ) hXI S hS hG χ hAbs
        lo hi hshort hχ α β (-1) 1 h u
  simp_rw [heq]
  refine (hMean _).trans ?_
  rw [normalizedGowers_mul_polynomial_phase 1 (X : ℤ) S P hP]
  simpa [mul_assoc] using mul_le_mul_of_nonneg_left hGower hD.le

private theorem standardCharacter_as_phase {D : ℕ} [NeZero D] (r : ZMod D) (m : ℤ) :
    ZMod.stdAddChar ((m : ZMod D)*r) =
      phaseExponential (((r.val : ℝ)/(D : ℝ))*(m : ℝ)) := by
  have hr : ((m*(r.val : ℤ) : ℤ) : ZMod D) = (m : ZMod D)*r := by
    simp only [Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
  rw [← hr, ZMod.stdAddChar_coe]
  unfold phaseExponential
  congr 1
  push_cast
  ring

private theorem sum_standardCharacter_mul {D : ℕ} [NeZero D] (m : ZMod D) :
    (∑ r : ZMod D, ZMod.stdAddChar (m*r)) = if m = 0 then (D : ℂ) else 0 := by
  split_ifs with h
  · simp [h, ZMod.card]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar D h)

/-- A residue indicator as a finite sum of real linear characters. -/
theorem residue_indicator_fourier (D : ℕ) [NeZero D] (m u : ℤ) :
    (if Int.ModEq (D : ℤ) m u then (1 : ℂ) else 0) =
      ∑ r : ZMod D, ((D : ℂ)⁻¹ * phaseExponential (-((r.val : ℝ)/(D : ℝ))*(u : ℝ))) *
        phaseExponential (((r.val : ℝ)/(D : ℝ))*(m : ℝ)) := by
  have hD : (D : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne D
  have hchar (r : ZMod D) :
      phaseExponential (-((r.val : ℝ)/(D : ℝ))*(u : ℝ)) *
        phaseExponential (((r.val : ℝ)/(D : ℝ))*(m : ℝ)) =
      ZMod.stdAddChar (((m-u : ℤ) : ZMod D)*r) := by
    rw [standardCharacter_as_phase, ← phaseExponential_add]
    congr 1
    push_cast
    ring
  simp_rw [mul_assoc, hchar]
  rw [← Finset.mul_sum]
  rw [sum_standardCharacter_mul]
  have hZero : (((m-u : ℤ) : ZMod D) = 0) ↔ Int.ModEq (D : ℤ) m u := by
    rw [Int.cast_sub, sub_eq_zero, ZMod.intCast_eq_intCast_iff]
  by_cases hm : Int.ModEq (D : ℤ) m u
  · simp [hm, hZero.mpr hm, hD]
  · simp only [if_neg hm, if_neg (hZero.not.mpr hm), mul_zero]

/-- The coefficients in the residue class expansion have absolute sum one. -/
theorem residue_indicator_fourier_l1 (D : ℕ) [NeZero D] (u : ℤ) :
    (∑ r : ZMod D, ‖(D : ℂ)⁻¹ * phaseExponential (-((r.val : ℝ)/(D : ℝ))*(u : ℝ))‖) = 1 := by
  have hD : (D : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne D
  simp [norm_mul, phaseExponential, Complex.norm_exp, ZMod.card, hD]

/-- Normalized finite Fourier coefficients of the interval indicator on
the cyclic group of order `2*X+1`. The ambient interval does not wrap. -/
noncomputable def intervalCyclicFourierCoefficient (X : ℕ) (a b : ℤ) (r : ZMod (2*X+1)) : ℂ :=
  ((2*X+1 : ℕ) : ℂ)⁻¹ * ∑ n ∈ Finset.Icc a b, ZMod.stdAddChar (-((n : ZMod (2*X+1))*r))

private theorem eq_of_zmod_eq_on_positiveInterval (X : ℕ) {m n : ℤ}
    (hm : m ∈ positiveInterval X) (hn : n ∈ positiveInterval X)
    (heq : (m : ZMod (2*X+1)) = (n : ZMod (2*X+1))) : m = n := by
  have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub m n (2*X+1)).mp heq
  have hm' : 1 ≤ m ∧ m ≤ (X : ℤ) := by simpa [positiveInterval] using hm
  have hn' : 1 ≤ n ∧ n ≤ (X : ℤ) := by simpa [positiveInterval] using hn
  have hz := Int.eq_zero_of_abs_lt_dvd hd (show |n-m| < ((2*X+1 : ℕ) : ℤ) by
    push_cast
    exact abs_lt.mpr ⟨by omega, by omega⟩)
  omega

/-- The exact normalized cyclic Fourier expansion of a consecutive
interval on the paper's ambient range `[X]`. -/
theorem interval_indicator_fourier (X : ℕ) (a b m : ℤ)
    (hI : Finset.Icc a b ⊆ positiveInterval X) (hm : m ∈ positiveInterval X) :
    (if m ∈ Finset.Icc a b then (1 : ℂ) else 0) =
      ∑ r : ZMod (2*X+1), intervalCyclicFourierCoefficient X a b r *
        phaseExponential (((r.val : ℝ)/((2*X+1 : ℕ) : ℝ))*(m : ℝ)) := by
  let D := 2*X+1
  have hD : (D : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by dsimp [D]; omega)
  change _ = ∑ r : ZMod D, intervalCyclicFourierCoefficient X a b r *
    phaseExponential (((r.val : ℝ)/(D : ℝ))*(m : ℝ))
  have hExpansion : (∑ r : ZMod D, intervalCyclicFourierCoefficient X a b r *
      phaseExponential (((r.val : ℝ)/(D : ℝ))*(m : ℝ))) =
        ((D : ℂ)⁻¹ * ∑ n ∈ Finset.Icc a b, ∑ r : ZMod D,
          ZMod.stdAddChar ((-(n : ZMod D) + (m : ZMod D))*r)) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    change ((D : ℂ)⁻¹ * ∑ n ∈ Finset.Icc a b, ZMod.stdAddChar (-((n : ZMod D)*r))) *
      phaseExponential (((r.val : ℝ)/(D : ℝ))*(m : ℝ)) = _
    rw [mul_assoc, Finset.sum_mul, ← standardCharacter_as_phase]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← AddChar.map_add_eq_mul, ← neg_mul, ← add_mul]
  rw [hExpansion]
  have hlookup (n : ℤ) (hn : n ∈ Finset.Icc a b) :
      (-(n : ZMod D) + (m : ZMod D) = 0) ↔ n = m := by
    rw [neg_add_eq_sub, sub_eq_zero]
    exact ⟨fun h => (eq_of_zmod_eq_on_positiveInterval X hm (hI hn) h).symm,
      fun h => congrArg (fun k : ℤ => (k : ZMod D)) h.symm⟩
  simp_rw [sum_standardCharacter_mul]
  have hsum : (∑ n ∈ Finset.Icc a b,
     if -(n : ZMod D) + (m : ZMod D) = 0 then (D : ℂ) else 0) =
     ∑ n ∈ Finset.Icc a b, if n = m then (D : ℂ) else 0 :=
    Finset.sum_congr rfl fun n hn => if_congr (hlookup n hn) rfl rfl
  rw [hsum, Finset.sum_ite_eq']
  split_ifs <;> simp [hD]

/-- Progression specialization of the localized prime-model replacement.
The residue coefficients have been summed exactly. Only the cyclic
interval Fourier coefficient mass remains as a numerical factor. -/
theorem localized_prime_model_replacement_progression (S : ℕ) (hS : 3 ≤ S)
    (hG : NormalizedGowersLaws S) :
    ∃ E : ℝ, 0 < E ∧ ∀ (X D : ℕ) [NeZero D], 0 < X →
    ∀ (a b u₀ : ℤ), Finset.Icc a b ⊆ positiveInterval X →
      (localProgression a b u₀ D).Nonempty →
    ∀ (u : ℤ → ℂ) (χ : C(Circle,ℂ)),
      Summable (fun n : ℤ => ‖fourierCoeff χ n‖) →
    ∀ (lo hi : ℝ), 2*(hi-lo) < 1 →
      (∀ t : ℝ, t ∈ Set.Ico (0 : ℝ) 1 → χ (t : Circle) ≠ 0 → t ∈ Set.Icc lo hi) →
    ∀ (α β : ℝ) (h : ℤ) (Q : ℝ[X]), Q.natDegree < S →
    let J := localProgression a b u₀ D
    ‖(∑ m ∈ J, u m * χ ((β*((m-1 : ℤ) : ℝ) : ℝ) : Circle) *
      phaseExponential ((h : ℝ)*heisenbergPhase α β (m-1)-Q.eval (m : ℝ))) / (J.card : ℂ)‖ ≤
        ((X : ℝ)/(J.card : ℝ)) * (∑ r : ZMod (2*X+1), ‖intervalCyclicFourierCoefficient X a b r‖) *
          (E * (∑' n : ℤ, ‖fourierCoeff χ n‖) * normalizedGowers S 1 (X : ℤ) u) := by
  obtain ⟨E, hE, hMean⟩ := hG.meanBound
  refine ⟨E, hE, ?_⟩
  intro X D _ hX a b u₀ hI hJ₀ u χ hAbs lo hi hshort hχ α β h Q hQ J
  let W := 2*X+1
  let iCoef (r : ZMod W) := intervalCyclicFourierCoefficient X a b r
  let rCoef (s : ZMod D) := (D : ℂ)⁻¹ * phaseExponential (-((s.val : ℝ)/(D : ℝ))*(u₀ : ℝ))
  let c (k : ZMod W × ZMod D) := iCoef k.1 * rCoef k.2
  let θ (k : ZMod W × ZMod D) := (k.1.val : ℝ)/(W : ℝ) + (k.2.val : ℝ)/(D : ℝ)
  have hSub : J ⊆ positiveInterval X := fun m hm => hI (Finset.mem_filter.mp hm).1
  have hExpansion (m : ℤ) (hm : m ∈ positiveInterval X) :
      (if m ∈ J then (1 : ℂ) else 0) =
        ∑ k : ZMod W × ZMod D, c k * phaseExponential (θ k * (m : ℝ)) := by
    have hProd : (if m ∈ J then (1 : ℂ) else 0) =
        (if m ∈ Finset.Icc a b then (1 : ℂ) else 0) *
          (if Int.ModEq (D : ℤ) m u₀ then (1 : ℂ) else 0) := by
      by_cases hi : m ∈ Finset.Icc a b <;> by_cases hr : Int.ModEq (D : ℤ) m u₀ <;>
        simp [J, localProgression, Finset.mem_filter, hi, hr]
    rw [hProd, interval_indicator_fourier X a b m hI hm, residue_indicator_fourier D m u₀,
      Fintype.sum_prod_type, Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [c, θ, add_mul, phaseExponential_add, iCoef, rCoef, W]
    ring
  have hL1 : (∑ k : ZMod W × ZMod D, ‖c k‖) = ∑ r : ZMod W, ‖iCoef r‖ := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [c, norm_mul, ← Finset.mul_sum]
    rw [show (∑ s : ZMod D, ‖rCoef s‖) = 1 from residue_indicator_fourier_l1 D u₀, mul_one]
  have hMain := localized_prime_model_replacement_of_expansion X S hX hS hG E hE (hMean X hX)
    u χ hAbs lo hi hshort hχ α β h Q hQ J hSub hJ₀ Finset.univ c θ hExpansion
  rw [hL1] at hMain
  exact hMain

private theorem norm_phaseExponential (t : ℝ) : ‖phaseExponential t‖ = 1 := by
  simp [phaseExponential, Complex.norm_exp]

theorem phaseExponential_sub_one_lower (t : ℝ) (ht : |t| ≤ 1/2) :
    4*|t| ≤ ‖phaseExponential t - 1‖ := by
  have h1 : phaseExponential (t/2) * phaseExponential (t/2) = phaseExponential t := by
    rw [← phaseExponential_add, show t/2+t/2=t by ring]
  have h2 : phaseExponential (t/2) * conj (phaseExponential (t/2)) = 1 := by
    simpa only [sub_self, phaseExponential_zero] using (phaseExponential_sub (t/2) (t/2)).symm
  have heq : phaseExponential t - 1 =
      phaseExponential (t/2)*(phaseExponential (t/2)-conj (phaseExponential (t/2))) := by
    rw [mul_sub, h1, h2]
  have him : (phaseExponential (t/2)).im = Real.sin (Real.pi*t) := by
    unfold phaseExponential
    rw [show 2*(Real.pi : ℂ)*Complex.I*((t/2 : ℝ) : ℂ) =
      ((Real.pi*t : ℝ) : ℂ)*Complex.I by push_cast; ring]
    exact Complex.exp_ofReal_mul_I_im _
  have hTwo : |(2 : ℝ)| = 2 := abs_of_nonneg (by norm_num)
  rw [heq, norm_mul, norm_phaseExponential, one_mul, Complex.sub_conj, norm_mul, Complex.norm_I,
    mul_one, Complex.norm_real, Real.norm_eq_abs, him]
  simp only [abs_mul, hTwo]
  have hSine := Real.le_sin_mul (show 0 ≤ 2*|t| by positivity) (show 2*|t| ≤ 1 by linarith)
  have he : Real.pi/2*(2*|t|) = Real.pi*|t| := by ring
  rw [he] at hSine
  have hAbs : Real.sin (Real.pi*|t|) ≤ |Real.sin (Real.pi*t)| := by
    rcases le_or_gt 0 t with hp | hp
    · rw [abs_of_nonneg hp]
      exact le_abs_self _
    · rw [abs_of_neg hp, mul_neg, Real.sin_neg]
      exact neg_le_abs _
  linarith

private theorem norm_standardCharacter {D : ℕ} [NeZero D] (x : ZMod D) :
    ‖ZMod.stdAddChar x‖ = 1 := by
  rw [ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

private theorem interval_character_geometric {D : ℕ} [NeZero D] (a b : ℤ) (r : ZMod D) :
    ‖(∑ n ∈ Finset.Icc a b, ZMod.stdAddChar (-((n : ZMod D)*r))) *
        (ZMod.stdAddChar (-r)-1)‖ ≤ 2 := by
  let H := (b+1-a).toNat
  let f (n : ℕ) := ZMod.stdAddChar (-(((a+(n : ℤ) : ℤ) : ZMod D)*r))
  have hstep (n : ℕ) : f n * ZMod.stdAddChar (-r) = f (n+1) := by
    unfold f
    rw [← AddChar.map_add_eq_mul]
    congr 1
    push_cast
    ring
  have heq : (∑ n ∈ Finset.Icc a b, ZMod.stdAddChar (-((n : ZMod D)*r))) *
      (ZMod.stdAddChar (-r)-1) = f H-f 0 := by
    rw [Int.Icc_eq_finset_map, Finset.sum_map]
    change (∑ n ∈ Finset.range H, f n) * (ZMod.stdAddChar (-r)-1) = _
    simp only [Finset.sum_mul, mul_sub, mul_one, hstep]
    simpa only [Finset.sum_sub_distrib] using Finset.sum_range_sub f H
  rw [heq]
  exact (norm_sub_le _ _).trans_eq (by norm_num [f, norm_standardCharacter])

/-- The geometric-series estimate at each nonzero centered frequency.
For an odd cyclic group the centered frequency has magnitude at most
half the period. -/
theorem norm_intervalCyclicFourierCoefficient_nonzero (X : ℕ) (a b : ℤ)
    (r : ZMod (2*X+1)) (hr : r ≠ 0) :
    ‖intervalCyclicFourierCoefficient X a b r‖ ≤ 1/(2*(r.valMinAbs.natAbs : ℝ)) := by
  let D := 2*X+1
  change r ≠ (0 : ZMod D) at hr
  let j := r.valMinAbs
  have hj : j ≠ 0 := fun h => hr ((ZMod.valMinAbs_eq_zero r).mp h)
  have hD : 0 < (D : ℝ) := by exact_mod_cast (show 0 < D by dsimp [D]; omega)
  have hJ : 0 < (j.natAbs : ℝ) := by exact_mod_cast (Int.natAbs_pos.mpr hj)
  have hSmall : (j.natAbs : ℝ) ≤ (D : ℝ)/2 := by
    have hh := r.natAbs_valMinAbs_le
    change j.natAbs ≤ D/2 at hh
    have hp : 2*j.natAbs ≤ D := by omega
    have hh' : (2:ℝ)*(j.natAbs : ℝ) ≤ (D : ℝ) := by exact_mod_cast hp
    linarith
  have hChar : ZMod.stdAddChar (-r) = phaseExponential (-(j : ℝ)/(D : ℝ)) := by
    change ZMod.stdAddChar (-r : ZMod D) = _
    have heq : (-r : ZMod D) = ((-j : ℤ) : ZMod D) := by
      rw [Int.cast_neg, show ((j : ℤ) : ZMod D) = r from ZMod.coe_valMinAbs r]
    rw [heq, ZMod.stdAddChar_coe (N := D)]
    unfold phaseExponential
    congr 1
    push_cast
    ring
  have hAbs : |-(j : ℝ)/(D : ℝ)| = (j.natAbs : ℝ)/(D : ℝ) := by
    rw [abs_div, abs_neg, abs_of_pos hD, ← Int.cast_abs, Int.abs_eq_natAbs]
    rfl
  have hLower : 4*((j.natAbs : ℝ)/(D : ℝ)) ≤ ‖ZMod.stdAddChar (-r)-1‖ := by
    rw [hChar, ← hAbs]
    apply phaseExponential_sub_one_lower
    rw [hAbs]
    exact (div_le_iff₀ hD).mpr (by linarith)
  let A := ∑ n ∈ Finset.Icc a b, ZMod.stdAddChar (-((n : ZMod D)*r))
  have hGeom : ‖A‖ * ‖ZMod.stdAddChar (-r)-1‖ ≤ 2 := by
    rw [← norm_mul]
    exact interval_character_geometric a b r
  have hProd : ‖A‖ * (4*((j.natAbs : ℝ)/(D : ℝ))) ≤ 2 :=
    (mul_le_mul_of_nonneg_left hLower (norm_nonneg _)).trans hGeom
  change ‖((D : ℂ)⁻¹)*A‖ ≤ 1/(2*(j.natAbs : ℝ))
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  apply (le_div_iff₀ (by positivity : 0 < 2*(j.natAbs : ℝ))).mpr
  change (D : ℝ)⁻¹ * ‖A‖ * (2*(j.natAbs : ℝ)) ≤ 1
  have hEq : (D : ℝ)⁻¹ * ‖A‖ * (2*(j.natAbs : ℝ)) =
      (‖A‖ * (4*((j.natAbs : ℝ)/(D : ℝ)))) / 2 := by ring
  rw [hEq]
  exact (div_le_iff₀ (show (0 : ℝ) < 2 by norm_num)).mpr (by simpa using hProd)

private theorem norm_intervalCyclicFourierCoefficient_zero (X : ℕ) (a b : ℤ)
    (hI : Finset.Icc a b ⊆ positiveInterval X) :
    ‖intervalCyclicFourierCoefficient X a b 0‖ ≤ 1 := by
  have hc : (Finset.Icc a b).card ≤ X := by
    simpa only [card_positiveInterval] using Finset.card_le_card hI
  have hX : (0 : ℝ) < ((2*X+1 : ℕ) : ℝ) := by positivity
  unfold intervalCyclicFourierCoefficient
  simp only [mul_zero, neg_zero, AddChar.map_zero_eq_one, Finset.sum_const, nsmul_eq_mul,
    mul_one, norm_mul, norm_inv, Complex.norm_natCast]
  rw [← div_eq_inv_mul]
  apply (div_le_one hX).mpr
  exact_mod_cast (show (Finset.Icc a b).card ≤ 2*X+1 by omega)

private theorem sum_centered_frequency_weights (X : ℕ) :
    (∑ r : ZMod (2*X+1), if r.valMinAbs = 0 then (1 : ℝ)
      else 1/(2*(r.valMinAbs.natAbs : ℝ))) = 1 + (harmonic X : ℝ) := by
  let D := 2*X+1
  let w (j : ℤ) : ℝ := if j = 0 then 1 else 1/(2*(j.natAbs : ℝ))
  let z : ZMod D → ℤ := ZMod.valMinAbs
  change (∑ r : ZMod D, w (z r)) = _
  have hz : Function.Injective z := ZMod.injective_valMinAbs
  have hImage : Finset.univ.image z = Finset.Icc (-(X : ℤ)) (X : ℤ) := by
    ext j
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_Icc]
    constructor
    · rintro ⟨r, rfl⟩
      have hr := r.valMinAbs_mem_Ioc
      change -(D : ℤ) < z r * 2 ∧ z r * 2 ≤ (D : ℤ) at hr
      dsimp [D] at hr
      push_cast at hr
      omega
    · intro hj
      refine ⟨(j : ZMod D), (ZMod.valMinAbs_spec _ _).mpr ⟨rfl, ?_⟩⟩
      change -(D : ℤ) < j*2 ∧ j*2 ≤ (D : ℤ)
      dsimp [D]
      push_cast
      omega
  have hPush : (∑ j ∈ Finset.univ.image z, w j) = ∑ r : ZMod D, w (z r) :=
    Finset.sum_image (fun _ _ _ _ heq => hz heq)
  rw [← hPush, hImage]
  let I := Finset.Icc (1 : ℕ) X
  let P := I.image (fun j : ℕ => (j : ℤ))
  let N := I.image (fun j : ℕ => -(j : ℤ))
  have hP (j : ℤ) : j ∈ P ↔ 0 < j ∧ j ≤ (X : ℤ) := by
    simp only [P, I, Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨k, hk, rfl⟩
      omega
    · intro hj
      exact ⟨j.toNat, by omega, by omega⟩
  have hN (j : ℤ) : j ∈ N ↔ -(X : ℤ) ≤ j ∧ j < 0 := by
    simp only [N, I, Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨k, hk, rfl⟩
      omega
    · intro hj
      exact ⟨(-j).toNat, by omega, by omega⟩
  have hPartition : P ∪ N ∪ {0} = Finset.Icc (-(X : ℤ)) (X : ℤ) := by
    ext j
    simp only [Finset.mem_union, hP, hN, Finset.mem_singleton, Finset.mem_Icc]
    omega
  have hPN : Disjoint P N := Finset.disjoint_left.mpr fun j a b => by
    have := (hP j).mp a
    have := (hN j).mp b
    omega
  have hPN₀ : Disjoint (P ∪ N) {0} := Finset.disjoint_left.mpr fun j a b => by
    simp only [Finset.mem_union, hP, hN] at a
    simp only [Finset.mem_singleton] at b
    omega
  rw [← hPartition, Finset.sum_union hPN₀, Finset.sum_union hPN, Finset.sum_singleton]
  have hp : (∑ j ∈ P, w j) = ∑ j ∈ I, 1/(2*(j : ℝ)) := by
    rw [Finset.sum_image (fun x _ y _ h => by exact_mod_cast h)]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj₀ : (j : ℤ) ≠ 0 := by
      have := (Finset.mem_Icc.mp hj).1
      omega
    simp only [w, if_neg hj₀, Int.natAbs_natCast]
  have hn : (∑ j ∈ N, w j) = ∑ j ∈ I, 1/(2*(j : ℝ)) := by
    rw [Finset.sum_image (fun x _ y _ h => by exact_mod_cast (neg_inj.mp h))]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj₀ : (j : ℤ) ≠ 0 := by
      have := (Finset.mem_Icc.mp hj).1
      omega
    simp only [w, if_neg (neg_ne_zero.mpr hj₀), Int.natAbs_neg, Int.natAbs_natCast]
  rw [hp, hn, ← Finset.sum_add_distrib]
  have hSum : (∑ j ∈ I, (1/(2*(j : ℝ)) + 1/(2*(j : ℝ)))) = (harmonic X : ℝ) := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [one_div, mul_inv_rev]
    ring
  rw [hSum, show w 0 = 1 by simp [w], add_comm]

/-- The normalized interval Fourier coefficient mass is bounded by the
harmonic series over the positive centered frequencies, plus the zero mode. -/
theorem intervalCyclicFourierCoefficient_l1_le (X : ℕ) (a b : ℤ)
    (hI : Finset.Icc a b ⊆ positiveInterval X) :
    (∑ r : ZMod (2*X+1), ‖intervalCyclicFourierCoefficient X a b r‖) ≤ 2 + Real.log X := by
  calc
    _ ≤ ∑ r : ZMod (2*X+1), if r.valMinAbs = 0 then (1 : ℝ)
        else 1/(2*(r.valMinAbs.natAbs : ℝ)) := by
      refine Finset.sum_le_sum fun r _ => ?_
      by_cases hr : r = 0
      · subst r
        simpa [ZMod.valMinAbs_zero] using norm_intervalCyclicFourierCoefficient_zero X a b hI
      · rw [if_neg ((ZMod.valMinAbs_eq_zero r).not.mpr hr)]
        exact norm_intervalCyclicFourierCoefficient_nonzero X a b r hr
    _ = 1 + (harmonic X : ℝ) := sum_centered_frequency_weights X
    _ ≤ _ := by linarith [harmonic_le_one_add_log X]

end NilBohr
