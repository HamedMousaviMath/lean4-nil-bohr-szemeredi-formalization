import NilBohr.Definitions

/-! Fourier inversion for the two-input case of Theorem 4.2. -/

open MeasureTheory Polynomial ComplexConjugate
open scoped BigOperators

namespace NilBohr

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- Haar probability measure on the unit circle used by the Fourier formula. -/
noncomputable abbrev normalizedCircleMeasure : Measure Circle := AddCircle.haarAddCircle

/-- Finite Fourier transform of an integer-supported function, with the sign
recorded as an integer multiplier of the frequency. -/
noncomputable def spatialFourier (X : Finset ℤ) (f : ℤ → ℂ) (sign : ℤ) (θ : Circle) : ℂ :=
  ∑ x ∈ X, f x * fourier (sign * x) θ

private theorem continuous_spatialFourier (X : Finset ℤ) (f : ℤ → ℂ) (sign : ℤ) :
    Continuous (spatialFourier X f sign) := by
  unfold spatialFourier
  exact continuous_finset_sum _ (fun x _ => continuous_const.mul (fourier _).continuous)

private theorem integral_fourier_unit (n : ℤ) :
    (∫ θ : Circle, fourier n θ ∂normalizedCircleMeasure) = if n = 0 then 1 else 0 := by
  by_cases hn : n = 0
  · subst n
    simp [fourier_zero]
  · rw [if_neg hn]
    exact integral_eq_zero_of_add_right_eq_neg (μ := normalizedCircleMeasure)
      (fourier_add_half_inv_index hn (show (0 : ℝ) < 1 by norm_num))

/-- Fourier inversion of a finite translated product. Both transforms use
the same spatial support and opposite frequency signs. -/
theorem integral_spatialFourier_product
    (X : Finset ℤ) (f g : ℤ → ℂ) (sign shift : ℤ) (hSign : sign ≠ 0)
    (hg : SupportedOn X g) :
    (∫ θ : Circle, (spatialFourier X f sign θ * spatialFourier X g (-sign) θ) *
        fourier (sign * shift) θ ∂normalizedCircleMeasure) =
      ∑ x ∈ X, f x * g (x + shift) := by
  classical
  let term := fun x z : ℤ => fun θ : Circle =>
    (f x * g z) * fourier (sign * (x + shift - z)) θ
  have hterm (x z : ℤ) : Continuous (term x z) :=
    continuous_const.mul (fourier _).continuous
  have hExpand (θ : Circle) :
      (spatialFourier X f sign θ * spatialFourier X g (-sign) θ) *
        fourier (sign * shift) θ = ∑ x ∈ X, ∑ z ∈ X, term x z θ := by
    unfold spatialFourier
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro z hz
    unfold term
    rw [show sign * (x + shift - z) = (sign * x + (-sign) * z) + sign * shift by ring]
    rw [fourier_add, fourier_add]
    ring
  simp_rw [hExpand]
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro x hx
    rw [integral_finset_sum]
    · have hEval (z : ℤ) :
          (∫ θ : Circle, term x z θ ∂normalizedCircleMeasure) =
            if x + shift = z then f x * g z else 0 := by
        unfold term
        rw [integral_const_mul, integral_fourier_unit]
        by_cases h : x + shift = z
        · simp [h]
        · have hd : sign * (x + shift - z) ≠ 0 := mul_ne_zero hSign (sub_ne_zero.mpr h)
          simp [h, hd]
      simp_rw [hEval]
      rw [Finset.sum_ite_eq]
      by_cases h : x + shift ∈ X
      · simp [h]
      · simp [h, hg _ h]
    · intro z hz
      exact (hterm x z).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · intro x hx
    exact (continuous_finset_sum _ (fun z _ => hterm x z)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)


/-- Plancherel for the finite Fourier transform, using normalized Haar
measure on the circle. -/
theorem integral_norm_spatialFourier_sq (X : Finset ℤ) (f : ℤ → ℂ) (sign : ℤ)
    (hSign : sign ≠ 0) (hf : SupportedOn X f) :
    (∫ θ : Circle, ‖spatialFourier X f sign θ‖ ^ 2 ∂normalizedCircleMeasure) =
      ∑ x ∈ X, ‖f x‖ ^ 2 := by
  have hConj (θ : Circle) :
      spatialFourier X (fun x => conj (f x)) (-sign) θ =
        conj (spatialFourier X f sign θ) := by
    unfold spatialFourier
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [map_mul, neg_mul, fourier_neg]
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal, Complex.ofReal_sum]
  calc
    _ = ∫ θ : Circle, (spatialFourier X f sign θ *
        spatialFourier X (fun x => conj (f x)) (-sign) θ) *
        fourier (sign * 0) θ ∂normalizedCircleMeasure := by
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall fun θ => by
        dsimp only
        rw [hConj θ, Complex.mul_conj, Complex.sq_norm, mul_zero, fourier_zero, mul_one]
    _ = ∑ x ∈ X, f x * conj (f x) := by
      simpa using integral_spatialFourier_product X f (fun x => conj (f x)) sign 0 hSign
        (fun x hx => by simp [hf x hx])
    _ = _ := by simp only [Complex.mul_conj, Complex.sq_norm]

/-- The parameter Fourier sum in the two-input inversion identity. -/
noncomputable def parameterFourier (M : ℕ) (P : Polynomial ℤ) (v : ℤ → ℂ)
    (θ : Circle) : ℂ :=
  ∑ y ∈ positiveInterval M, v y * fourier (P.eval y) θ

private theorem continuous_parameterFourier (M : ℕ) (P : Polynomial ℤ) (v : ℤ → ℂ) :
    Continuous (parameterFourier M P v) := by
  unfold parameterFourier
  exact continuous_finset_sum _ (fun y _ => continuous_const.mul (fourier _).continuous)

/-- The manuscript's two-input counting form, expressed exactly as a circle
integral with its original spatial and parameter normalization. -/
theorem countingForm_twoInput_fourier (N M : ℕ) (X : Finset ℤ)
    (P : Fin 2 → Polynomial ℤ) (v : ℤ → ℂ) (f : Fin 2 → ℤ → ℂ)
    (hP : P 0 = 0) (hf : SupportedOn X (f 1)) :
    countingForm N M X P v f =
      (∫ θ : Circle, (spatialFourier X (f 0) 1 θ * spatialFourier X (f 1) (-1) θ) *
        parameterFourier M (P 1) v θ ∂normalizedCircleMeasure) / ((N : ℂ) * (M : ℂ)) := by
  unfold countingForm
  congr 1
  simp only [Fin.prod_univ_two, hP, eval_zero, add_zero]
  rw [Finset.sum_comm]
  let A : Circle → ℂ := fun θ => spatialFourier X (f 0) 1 θ * spatialFourier X (f 1) (-1) θ
  change _ = ∫ θ : Circle, A θ * parameterFourier M (P 1) v θ ∂normalizedCircleMeasure
  have hCont : Continuous A := (continuous_spatialFourier _ _ _).mul
    (continuous_spatialFourier _ _ _)
  have hExpand (θ : Circle) :
      A θ * parameterFourier M (P 1) v θ =
        ∑ y ∈ positiveInterval M, v y * (A θ * fourier ((P 1).eval y) θ) := by
    unfold parameterFourier
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    ring
  simp_rw [hExpand]
  rw [MeasureTheory.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro y hy
    rw [MeasureTheory.integral_const_mul, ← Finset.mul_sum]
    have h := integral_spatialFourier_product X (f 0) (f 1) 1 ((P 1).eval y) (by norm_num) hf
    simpa [A] using congrArg (fun c : ℂ => v y * c) h.symm
  · intro y hy
    exact (continuous_const.mul (hCont.mul (fourier _).continuous)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)


private theorem interval_card (M : ℕ) : (positiveInterval M).card = M := by
  simp [positiveInterval, Int.card_Icc]

private theorem norm_phase (x : ℝ) : ‖phase x‖ = 1 := by
  simp [phase, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

private theorem norm_parameterFourier_le (M d : ℕ) (P : Polynomial ℤ) (v : ℤ → ℂ)
    (hM : 0 < M) (hDegree : P.natDegree ≤ d)
    (hv : OneBoundedOn (positiveInterval M) v) (θ : Circle) :
    ‖parameterFourier M P v θ‖ ≤
      (M : ℝ) * phaseNorm (d + 1) (positiveInterval M) v := by
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
  let φ := C (-t) * P.map (Int.castRingHom ℝ)
  have hφ : φ.natDegree < d + 1 := by
    have h := (natDegree_C_mul_le (-t) (P.map (Int.castRingHom ℝ))).trans
      (natDegree_map_le.trans hDegree)
    exact Nat.lt_succ_of_le h
  have hPhase (y : ℤ) :
      fourier (P.eval y) (t : Circle) = phase (-(φ.eval (y : ℝ))) := by
    rw [fourier_coe_apply, phase]
    have hEval : (P.map (Int.castRingHom ℝ)).eval (y : ℝ) = ((P.eval y : ℤ) : ℝ) := by
      rw [eval_map]
      exact eval₂_at_apply (p := P) (Int.castRingHom ℝ) y
    simp only [φ, eval_mul, eval_C, hEval, mul_one, Complex.ofReal_neg, Complex.ofReal_mul,
      Complex.ofReal_intCast, Complex.ofReal_one, div_one]
    congr 1
    ring
  have hMReal : (0 : ℝ) < M := by exact_mod_cast hM
  have hΦ (ψ : Polynomial ℝ) : ‖phaseAverage (positiveInterval M) v ψ‖ ≤ 1 := by
    rw [phaseAverage, Complex.norm_div, Complex.norm_natCast, interval_card]
    apply (div_le_iff₀ hMReal).2
    refine (norm_sum_le _ _).trans ?_
    have hSum := Finset.sum_le_sum (s := positiveInterval M)
      (f := fun y => ‖v y * phase (-(ψ.eval (y : ℝ)))‖) (g := fun _ => (1 : ℝ))
      (fun y hy => by
        dsimp only
        rw [Complex.norm_mul, norm_phase, mul_one]
        exact hv y hy)
    simpa only [Finset.sum_const, interval_card, nsmul_eq_mul, mul_one, one_mul] using hSum
  have hBdd : BddAbove {a : ℝ | ∃ ψ : Polynomial ℝ, ψ.natDegree < d + 1 ∧
      a = ‖phaseAverage (positiveInterval M) v ψ‖} :=
    ⟨1, by rintro _ ⟨ψ, hψ, rfl⟩; exact hΦ ψ⟩
  have hNorm : ‖phaseAverage (positiveInterval M) v φ‖ ≤
      phaseNorm (d + 1) (positiveInterval M) v :=
    le_csSup hBdd ⟨φ, hφ, rfl⟩
  rw [phaseAverage, Complex.norm_div, Complex.norm_natCast, interval_card] at hNorm
  unfold parameterFourier
  simp_rw [hPhase]
  exact mul_comm (phaseNorm (d + 1) (positiveInterval M) v) (M : ℝ) ▸
    (div_le_iff₀ hMReal).mp hNorm

/-- The two-input bound, with the full parameter interval as its only test.
The bound is valid for any positive spatial and parameter lengths. -/
theorem countingForm_twoInput_le (N M d : ℕ) (X : Finset ℤ) (P : Fin 2 → Polynomial ℤ)
    (v : ℤ → ℂ) (f : Fin 2 → ℤ → ℂ) (hN : 0 < N) (hM : 0 < M)
    (hP : P 0 = 0) (hDegree : (P 1).natDegree ≤ d)
    (hv : OneBoundedOn (positiveInterval M) v)
    (hf : ∀ i, OneBoundedOn X (f i)) (hFs : ∀ i, SupportedOn X (f i)) :
    ‖countingForm N M X P v f‖ ≤
      ((X.card : ℝ) / N) * phaseNorm (d + 1) (positiveInterval M) v := by
  let U := phaseNorm (d + 1) (positiveInterval M) v
  let A := spatialFourier X (f 0) 1
  let B := spatialFourier X (f 1) (-1)
  let W := parameterFourier M (P 1) v
  have hA : Continuous A := continuous_spatialFourier _ _ _
  have hB : Continuous B := continuous_spatialFourier _ _ _
  have hW : Continuous W := continuous_parameterFourier _ _ _
  have hWeight : ∀ θ, ‖W θ‖ ≤ (M : ℝ) * U := norm_parameterFourier_le M d (P 1) v hM hDegree hv
  have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
  have hMReal : (0 : ℝ) < M := by exact_mod_cast hM
  have hMU : 0 ≤ (M : ℝ) * U := (norm_nonneg _).trans (hWeight 0)
  have hParsA : ∫ θ : Circle, ‖A θ‖ ^ 2 ∂normalizedCircleMeasure = ∑ x ∈ X, ‖f 0 x‖ ^ 2 :=
    integral_norm_spatialFourier_sq _ _ _ (by norm_num) (hFs 0)
  have hParsB : ∫ θ : Circle, ‖B θ‖ ^ 2 ∂normalizedCircleMeasure = ∑ x ∈ X, ‖f 1 x‖ ^ 2 :=
    integral_norm_spatialFourier_sq _ _ _ (by norm_num) (hFs 1)
  have hParsSum (i : Fin 2) : (∑ x ∈ X, ‖f i x‖ ^ 2) ≤ (X.card : ℝ) := by
    have hSum := Finset.sum_le_sum (s := X) (f := fun x => ‖f i x‖ ^ 2) (g := fun _ => (1 : ℝ))
      (fun x hx => by simpa using pow_le_pow_left₀ (norm_nonneg (f i x)) (hf i x hx) 2)
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using hSum
  have hPoint (θ : Circle) :
      ‖A θ * B θ * W θ‖ ≤ ((M : ℝ) * U) * ((‖A θ‖ ^ 2 + ‖B θ‖ ^ 2) / 2) := by
    rw [Complex.norm_mul, Complex.norm_mul]
    calc
      _ ≤ (‖A θ‖ * ‖B θ‖) * ((M : ℝ) * U) :=
        mul_le_mul_of_nonneg_left (hWeight θ) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ ≤ _ := by
        rw [mul_comm (‖A θ‖ * ‖B θ‖)]
        apply mul_le_mul_of_nonneg_left _ hMU
        nlinarith only [sq_nonneg (‖A θ‖ - ‖B θ‖)]
  have hIntegrable {G : Type} [NormedAddCommGroup G] {g : Circle → G} (hg : Continuous g) :
      Integrable g normalizedCircleMeasure :=
    hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hIntegral :
      ‖∫ θ : Circle, A θ * B θ * W θ ∂normalizedCircleMeasure‖ ≤
        ((M : ℝ) * U) * (X.card : ℝ) := by
    refine (norm_integral_le_integral_norm _).trans ?_
    refine (integral_mono (hIntegrable ((hA.mul hB).mul hW).norm)
      (hIntegrable (continuous_const.mul (((hA.norm.pow 2).add (hB.norm.pow 2)).div_const 2)))
      hPoint).trans ?_
    rw [integral_const_mul, integral_div, integral_add (hIntegrable (hA.norm.pow 2))
      (hIntegrable (hB.norm.pow 2)), hParsA, hParsB]
    apply mul_le_mul_of_nonneg_left _ hMU
    linarith [hParsSum 0, hParsSum 1]
  rw [countingForm_twoInput_fourier N M X P v f hP (hFs 1),
    Complex.norm_div, Complex.norm_mul, Complex.norm_natCast, Complex.norm_natCast]
  refine (div_le_div_of_nonneg_right hIntegral (mul_nonneg hNReal.le hMReal.le)).trans_eq ?_
  field_simp
  ring


private theorem card_spatialInterval_le (C : ℝ) (N : ℕ) (hC : 1 ≤ C) (hN : 0 < N) :
    ((spatialInterval C N).card : ℝ) ≤ 3 * C * N := by
  have hNReal : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hCN : 0 ≤ C * (N : ℝ) := by positivity
  have hFloor : (0 : ℤ) ≤ ⌊C * (N : ℝ)⌋ := Int.floor_nonneg.2 hCN
  have hCeil : ⌈-C * (N : ℝ)⌉ ≤ (0 : ℤ) := Int.ceil_le.2 (by simp; linarith)
  have hNat :
      ((spatialInterval C N).card : ℤ) = ⌊C * (N : ℝ)⌋ + 1 - ⌈-C * (N : ℝ)⌉ := by
    rw [spatialInterval, Int.card_Icc, Int.toNat_of_nonneg (by omega)]
  have hReal : ((spatialInterval C N).card : ℝ) =
      (⌊C * (N : ℝ)⌋ : ℤ) + 1 - (⌈-C * (N : ℝ)⌉ : ℤ) := by exact_mod_cast hNat
  have hProduct : 1 ≤ C * (N : ℝ) :=
    one_le_mul_of_one_le_of_one_le hC hNReal
  have hUpper := Int.floor_le (C * (N : ℝ))
  have hLower := Int.le_ceil (-C * (N : ℝ))
  nlinarith only [hReal, hProduct, hUpper, hLower]

/-- The two-input case of the manuscript's local generalized von Neumann
theorem. Only the whole parameter interval is tested. The stronger bound
holds throughout the theorem's range without the small-scale error terms. -/
theorem localGeneralizedVonNeumann_twoInput (C : ℝ) (N M d : ℕ)
    (P : Fin 2 → Polynomial ℤ) (v : ℤ → ℂ) (f : Fin 2 → ℤ → ℂ)
    (hC : 1 ≤ C) (hN : 0 < N) (hM : 0 < M)
    (hP : P 0 = 0) (hDegree : (P 1).natDegree ≤ d)
    (hv : OneBoundedOn (positiveInterval M) v)
    (hf : ∀ i, OneBoundedOn (spatialInterval C N) (f i))
    (hFs : ∀ i, SupportedOn (spatialInterval C N) (f i)) :
    ‖countingForm N M (spatialInterval C N) P v f‖ ≤
      (3 * C) * phaseNorm (d + 1) (positiveInterval M) v := by
  refine (countingForm_twoInput_le _ _ _ _ _ _ _ hN hM hP hDegree hv hf hFs).trans ?_
  have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
  have hMReal : (0 : ℝ) < M := by exact_mod_cast hM
  have hPhaseNonneg : 0 ≤ phaseNorm (d + 1) (positiveInterval M) v :=
    nonneg_of_mul_nonneg_right
      ((norm_nonneg _).trans (norm_parameterFourier_le M d (P 1) v hM hDegree hv 0)) hMReal
  exact mul_le_mul_of_nonneg_right
    ((div_le_iff₀ hNReal).2 (card_spatialInterval_le C N hC hN)) hPhaseNonneg

end NilBohr
