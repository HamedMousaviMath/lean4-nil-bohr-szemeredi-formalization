import NilBohr.DensityIncrementParameters

/-! Proposition 3.1 from the selector comparison and the quoted weak
regularity theorem. -/

open Filter MeasureTheory
open scoped BigOperators Topology NNReal

namespace NilBohr

private theorem power_threshold_le {δ E K w : ℝ} (hδ : 0 < δ)
    (hδ₁ : δ ≤ 1) (hK : 1 ≤ K) (h : K * δ^(-E) ≤ w) {p : ℝ} (hp : p ≤ E) :
    δ^(-p) ≤ w := calc
  _ ≤ δ^(-E) := Real.rpow_le_rpow_of_exponent_ge hδ hδ₁ (by linarith)
  _ ≤ _ := (le_mul_of_one_le_left (Real.rpow_nonneg hδ.le _) hK).trans h

private lemma cutoff_log_bound {c₀ : ℝ} {N : ℕ} :
    (Real.log N)^c₀ ≤ Real.log (cramerCutoff c₀ N) := by
  have hl := Nat.le_ceil (Real.exp ((Real.log (N : ℝ))^c₀))
  have hh := Real.log_le_log (Real.exp_pos _) hl
  simpa only [Real.log_exp] using hh

private lemma weightedCutoff_zero {V : ℤ → ℝ} {J : OpenArc}
    (F : Circle → ℝ) (hsupp : tsupport F ⊆ J.carrier) {q M : ℕ} :
    ∀ y ∈ positiveInterval M,
      (q * y.toNat + 1).Prime →
      ¬ J.Contains (V ((((q * y.toNat + 1 : ℕ) : ℤ)) - 1)) →
      selectorWeight V (fun x => (F x : ℂ)) q y = 0 := by
  intro y hy _ hnot
  have hy₁ := (Finset.mem_Icc.mp hy).1
  have hEq : (((q * y.toNat + 1 : ℕ) : ℤ) - 1) = (q : ℤ) * y := by
    push_cast
    rw [Int.toNat_of_nonneg (by omega)]
    ring
  rw [hEq] at hnot
  have hF : F (V ((q : ℤ) * y) : Circle) = 0 := by
    by_contra hne
    apply hnot
    exact hsupp (subset_tsupport F (show (V ((q : ℤ) * y) : Circle) ∈ Function.support F from hne))
  simp only [selectorWeight, hF, Complex.ofReal_zero]

set_option maxHeartbeats 1800000 in
/-- The quantitative density increment follows from the relative selector
comparison for one minorant and the precise quoted weak regularity theorem. -/
theorem densityIncrementFor_of_relativeSelectorComparison
    (hreg : KMTTLocalWeakRegularity)
    {ℓ : ℕ} (P : Fin (ℓ + 1) → Polynomial ℤ) (hP : FixedPolynomialFamily P)
    {c₀ C : ℝ} (hc₀ : 0 < c₀) (hC : 1 ≤ C)
    (hcoeff : ∀ i, i ≠ 0 → HasCoefficients C 1 (P i))
    (V : ℤ → ℝ) (J : OpenArc) (F : Circle → ℝ)
    (hsupp : tsupport F ⊆ J.carrier) (hF : ∀ x, 0 ≤ F x ∧ F x ≤ 1)
    (hμ : 0 < (∫ x, F x ∂AddCircle.haarAddCircle))
    (hcmp : RelativeSelectorComparison c₀ C (P (Fin.last ℓ)).natDegree ℓ V (fun x => (F x : ℂ))) :
    DensityIncrementFor P (fun p => J.Contains (V ((p : ℤ) - 1))) := by
  classical
  let d := (P (Fin.last ℓ)).natDegree
  let k := ℓ + 1
  let τ := densityModelCutoff C d
  let c₃ := τ / 4
  let μ := ∫ x, F x ∂AddCircle.haarAddCircle
  let r := (P 1).natDegree
  let sel := fun p : ℕ => J.Contains (V ((p : ℤ) - 1))
  have hd : 0 < d := by
    have hNE : (Fin.last ℓ) ≠ (0 : Fin (ℓ+1)) := by
      intro he
      have hh : ℓ = 0 := by simpa only [Fin.val_last, Fin.val_zero] using congrArg Fin.val he
      have hℓ := hP.1
      omega
    exact (hcoeff _ hNE).2.2.1
  have hτ : 0 < τ := by dsimp [τ, densityModelCutoff]; positivity
  have hτ₁ : τ ≤ 1 := by
    dsimp [τ, densityModelCutoff]
    apply inv_le_one_of_one_le₀
    have hdR : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    nlinarith [mul_nonneg (show 0 ≤ C^2 - 1 by nlinarith) hdR]
  have hc₃ : 0 < c₃ := div_pos hτ (by norm_num)
  have hk : 0 < k := by dsimp [k]; omega
  obtain ⟨a₀, a₁, D₁, c₁, D₂, B₀, ha₀, ha₁, hD₁, hc₁, hD₂, hstep⟩ :=
    density_progression_of_count_comparison hreg hC (d := d) hP.1
  obtain ⟨cRel, σ, B, w₀, N₀, hcRel, hσ, hB, hw₀, hcmp⟩ := hcmp
  let c := min (1/4 : ℝ) (c₀*cRel)
  let η := min 1 (c₃ / (16 * (k : ℝ) * (2 : ℝ)^ℓ))
  let E := max (k : ℝ) (max ((k : ℝ) * a₀) ((k : ℝ) / σ))
  let K := max (w₀ : ℝ) (max 1 (max ((c₃ / 8)^(-a₀)) ((4*B/(μ*c₃))^(σ⁻¹))))
  let C₁ := (k : ℝ) * D₂
  let c₄ := c₁ * (c₃ / 8)^D₂
  have hc : 0 < c := lt_min (by norm_num) (mul_pos hc₀ hcRel)
  have hc_quarter : c ≤ 1/4 := min_le_left _ _
  have hc_rel : c ≤ c₀*cRel := min_le_right _ _
  have hη : 0 < η := lt_min zero_lt_one (by positivity)
  have hη₁ : η ≤ 1 := min_le_left _ _
  have hE_k : (k : ℝ) ≤ E := le_max_left _ _
  have hE_pos : 0 < E := (Nat.cast_pos.mpr hk).trans_le hE_k
  have hE_a : (k : ℝ) * a₀ ≤ E := (le_max_left _ _).trans (le_max_right _ _)
  have hE_σ : (k : ℝ) ≤ E*σ :=
    (div_le_iff₀ hσ).mp ((le_max_right _ _).trans (le_max_right _ _))
  have hK₁ : 1 ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hK₂ : ((c₃ / 8)^(-a₀)) ≤ K :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hK₃ : ((4*B/(μ*c₃))^(σ⁻¹)) ≤ K :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hC₁ : 0 < C₁ := mul_pos (Nat.cast_pos.mpr hk) hD₂
  have hc₄ : 0 < c₄ := by dsimp [c₄]; positivity
  have hlarge := densityIncrement_parameter_bounds (k := k) hd hτ hc₃ ha₁ hD₁
    (B := μ * c₃ / 4) (by positivity)
  have ht := (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun x : ℕ => (x : ℝ)) atTop atTop)).eventually_ge_atTop 1
  obtain ⟨Nmin, hNmin⟩ := eventually_atTop.mp
    (hlarge.and (ht.and (eventually_ge_atTop N₀)))
  let constants : DensityIncrementConstants :=
    ⟨c, η, K, E, C₁, c₄, B₀, Nmin, hc, hη, zero_lt_one.trans_le hK₁, hE_pos, hC₁, hc₄⟩
  refine ⟨constants, ?_⟩
  intro N q w A hNlarge hN hq hA δ hδ hδ₁ hwLow hwUp hdiv hsmooth hlogqL hno
  obtain ⟨hscale, ht, hN₀⟩ := hNmin N hNlarge
  let t := Real.log (N : ℝ)
  let M := parameterLength N q d
  let v := c₃ * δ^k
  let R := fun i => rescalePolynomial (q : ℤ) (P i)
  let Fq := selectorWeight V (fun x => (F x : ℂ)) q
  let W := fun y => (lambdaModulus q y : ℂ) * Fq y
  let f : Fin (ℓ + 1) → ℤ → ℂ := fun _ x => if x ∈ A then 1 else 0
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hqZ : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
  have hq₁ : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hRdeg (i : Fin (ℓ+1)) : (R i).natDegree = (P i).natDegree :=
    natDegree_rescalePolynomial _ _ hqZ
  have hPmax (i : Fin (ℓ+1)) : (P i).natDegree ≤ d :=
    hP.2.2.2.monotone (Fin.le_last _)
  have hRcoeff (i : Fin (ℓ+1)) (hi : i ≠ 0) : HasCoefficients C q (R i) :=
    (hcoeff i hi).rescale hq
  have ht1 : (1 : ℝ) ≤ t := ht
  have hwUp' : (w : ℝ) ≤ t^c := hwUp
  have hwLow' : K * δ^(-E) ≤ (w : ℝ) := hwLow
  have hδE : 1 ≤ δ^(-E) := by
    rw [← Real.rpow_zero δ]
    exact Real.rpow_le_rpow_of_exponent_ge hδ hδ₁ (by linarith)
  have hwK : K ≤ (w : ℝ) :=
    (le_mul_of_one_le_right (zero_le_one.trans hK₁) hδE).trans hwLow'
  have hw₀w : w₀ ≤ w := by
    exact_mod_cast ((le_max_left _ _).trans hwK : (w₀ : ℝ) ≤ (w : ℝ))
  have hwR : (0 : ℝ) < w := by exact_mod_cast (show 0 < w by omega)
  have hlogq : Real.log q ≤ Real.sqrt t := calc
    _ ≤ (w : ℝ)^2 := hlogqL
    _ ≤ (t^c)^2 := pow_le_pow_left₀ hwR.le hwUp' 2
    _ = t^(c*2) := by rw [Real.rpow_mul (by linarith : 0 ≤ t), Real.rpow_two]
    _ ≤ _ := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
  have hδbound : δ^(-(k : ℝ)) ≤ t :=
    (power_threshold_le hδ hδ₁ hK₁ hwLow' hE_k).trans (hwUp'.trans (by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le ht1 (show c ≤ (1 : ℝ) by linarith)))
  obtain ⟨hM, hMτ, hMweak, hexception⟩ := hscale hq hδ hlogq hδbound
  have hrel : RelativeModulus c₀ cRel w₀ N q w := by
    refine ⟨hw₀w, hq, ?_, (eight_mul_primeProduct_dvd_initialModulus (hw₀.trans hw₀w)).trans hdiv,
      hsmooth, hlogqL⟩
    calc
      _ ≤ t^c := hwUp'
      _ ≤ t^(c₀*cRel) := Real.rpow_le_rpow_of_exponent_le ht1 hc_rel
      _ = (t^c₀)^cRel := Real.rpow_mul (by linarith) _ _
      _ ≤ _ := Real.rpow_le_rpow (by positivity) cutoff_log_bound hcRel.le
  have hmean : circleMean (fun x => (F x : ℂ)) = (μ : ℂ) := integral_complex_ofReal
  have hCompareBound : B * (w : ℝ)^(-σ) ≤ μ * v / 4 := by
    have hbase : 0 ≤ 4*B/(μ*c₃) := by positivity
    have hp : 4*B/(μ*c₃) ≤ K^σ := by
      have hh := Real.rpow_le_rpow (Real.rpow_nonneg hbase _) hK₃ hσ.le
      rwa [← Real.rpow_mul hbase, inv_mul_cancel₀ hσ.ne', Real.rpow_one] at hh
    have hp' : B * K^(-σ) ≤ μ*c₃/4 := by
      rw [Real.rpow_neg (zero_le_one.trans hK₁), ← div_eq_mul_inv]
      apply (div_le_iff₀ (Real.rpow_pos_of_pos (zero_lt_one.trans_le hK₁) _)).mpr
      have hh := (div_le_iff₀ (mul_pos hμ hc₃)).mp hp
      linarith only [hh, mul_comm (K ^ σ) (μ * c₃)]
    have hpow_e : δ^(-E * -σ) ≤ δ^k := by
      rw [← Real.rpow_natCast]
      apply Real.rpow_le_rpow_of_exponent_ge hδ hδ₁
      nlinarith only [hE_σ]
    calc
      _ ≤ B * (K * δ^(-E))^(-σ) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos (mul_pos (zero_lt_one.trans_le hK₁)
            (Real.rpow_pos_of_pos hδ _)) hwLow' (by linarith)) hB.le
      _ = B * K^(-σ) * δ^(-E * -σ) := by
        rw [Real.mul_rpow (zero_le_one.trans hK₁) (Real.rpow_nonneg hδ.le _),
          ← Real.rpow_mul hδ.le, mul_assoc]
      _ ≤ (μ*c₃/4) * δ^k := mul_le_mul hp' hpow_e (by positivity) (by positivity)
      _ = _ := by dsimp [v]; ring
  have hCompare : ‖countingForm N M (positiveInterval N) R W f -
        (μ : ℂ) * countingForm N M (positiveInterval N) R (fun _ => 1) f‖ ≤ μ * v / 4 := by
    have hfb : ∀ i, OneBoundedOn (positiveInterval N) (f i) := by
      intro i x _
      dsimp [f]; split_ifs <;> simp
    have hfs : ∀ i, SupportedOn (positiveInterval N) (f i) := fun _ _ hx =>
      if_neg (fun hxA => hx (hA hxA))
    have hh := hcmp N q w hN₀ hrel R (fixedPolynomialFamily_rescale hq P hP)
      (hRdeg _) hRcoeff f hfb hfs
    rw [hmean] at hh
    exact hh.trans hCompareBound
  have hweighted : ‖countingForm N M (positiveInterval N) R W f‖ ≤ μ * v / 4 := by
    have hFq : ∀ y ∈ positiveInterval M, ‖Fq y‖ ≤ 1 := by
      intro y _
      dsimp [Fq, selectorWeight]
      rw [Complex.norm_of_nonneg (hF _).1]
      exact (hF _).2
    have hh := norm_selected_count_le_exception_mass hq hN hM P A hP.2.2.2.injective
      hPmax sel hno Fq hFq (weightedCutoff_zero F hsupp)
    calc
      _ ≤ densityExceptionMass k d q M := hh
      _ ≤ (μ*c₃/4) * δ^k := hexception
      _ = _ := by dsimp [v]; ring
  have hmodel : v ≤ ‖countingForm N M (positiveInterval N) R (fun _ => 1)
      (fun _ => densityModel N δ)‖ :=
    density_model_lower_from_coefficients hC hN hq hd R
      (fixedPolynomialFamily_rescale hq P hP).2.1
      (fun i => (hRdeg i).trans_le (hPmax i)) hRcoeff hδ.le hMτ
  have hε : 0 < v / 8 := by dsimp [v]; positivity
  have hε₁ : v / 8 < 1 / 2 := by
    have hvδ : δ^k ≤ 1 := pow_le_one₀ hδ.le hδ₁
    have hvτ : v ≤ c₃ := by dsimp [v]; exact mul_le_of_le_one_right hc₃.le hvδ
    dsimp [c₃] at hvτ
    linarith
  have hεeq : v / 8 = (c₃ / 8) * δ^k := by dsimp [v]; ring
  have hεcut : (v / 8)^(-a₀) ≤ (w : ℝ) := calc
    _ = (c₃ / 8)^(-a₀) * δ^(-((k : ℝ)*a₀)) := by
      rw [hεeq, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast,
        ← Real.rpow_mul hδ.le]
      congr 2
      ring
    _ ≤ K * δ^(-E) := mul_le_mul hK₂
      (Real.rpow_le_rpow_of_exponent_ge hδ hδ₁ (by linarith)) (by positivity) (by positivity)
    _ ≤ _ := hwLow'
  have hgain : (k : ℝ) * (2*η*δ) * ((1+η)*δ)^ℓ < 3*v/8 := by
    have hscale' : η * (16 * (k : ℝ) * 2^ℓ) ≤ c₃ :=
      (le_div_iff₀ (by positivity : 0 < 16 * (k : ℝ) * (2 : ℝ)^ℓ)).mp (min_le_right _ _)
    have hpow : (1 + η)^ℓ ≤ (2 : ℝ)^ℓ :=
      pow_le_pow_left₀ (by linarith) (by linarith) _
    have hηgain : (k : ℝ)*2*η*(1+η)^ℓ ≤ c₃/8 := by
      have hh := mul_le_mul_of_nonneg_left hpow
        (show 0 ≤ (k : ℝ)*2*η by positivity)
      calc
        _ ≤ (k : ℝ)*2*η*(2:ℝ)^ℓ := hh
        _ = (η * (16 * (k : ℝ) * 2^ℓ))/8 := by ring
        _ ≤ _ := div_le_div_of_nonneg_right hscale' (by norm_num)
    calc
      _ = ((k : ℝ)*2*η*(1+η)^ℓ) * δ^k := by
        rw [mul_pow]
        dsimp [k]
        rw [pow_succ']
        ring
      _ ≤ (c₃/8)*δ^k := mul_le_mul_of_nonneg_right hηgain (pow_nonneg hδ.le _)
      _ < _ := by dsimp [v]; nlinarith [mul_pos hc₃ (pow_pos hδ k)]
  obtain ⟨B', a, N', hB', hB'₀, hprog, hnew, hlen⟩ := hstep hN hq hM
    (le_refl M) R (fixedPolynomialFamily_rescale hq P hP) (hRdeg _) hRcoeff A hA
    W hμ hη.le (mul_pos hc₃ (pow_pos hδ _)) hε₁ hεcut hdiv hMweak hweighted
    hCompare hmodel hgain
  refine ⟨B', a, N', hB', hB'₀, hprog, hnew, ?_⟩
  have heq : ((q : ℝ) / (v/8))^(-D₂) =
      (q : ℝ)^(-D₂) * (c₃/8)^D₂ * δ^C₁ := by
    rw [Real.div_rpow hqR.le hε.le, Real.rpow_neg hε.le, div_inv_eq_mul, hεeq,
      Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hδ.le, mul_assoc]
  rw [hRdeg] at hlen
  change c₄ * (q : ℝ)^(-C₁) * δ^C₁ * (M : ℝ)^r ≤ (N' : ℝ)
  apply le_trans _ hlen
  rw [heq]
  have hqpow : (q : ℝ)^(-C₁) ≤ (q : ℝ)^(-D₂) := by
    apply Real.rpow_le_rpow_of_exponent_le hq₁
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
    dsimp [C₁]
    nlinarith only [mul_le_mul_of_nonneg_right hkR hD₂.le]
  calc
    _ ≤ c₄ * (q : ℝ)^(-D₂) * δ^C₁ * (M : ℝ)^r := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hqpow hc₄.le) (by positivity)) (by positivity)
    _ = _ := by dsimp [c₄, r]; ring

/-- Theorems 3.2 and 3.1 connect to Theorem 1.2 with the manuscript's
parameters and selector. The only quoted ingredient in this deduction is
the local weak regularity theorem. -/
theorem heisenbergRecurrence_of_relativeSelectorComparison
    (hreg : KMTTLocalWeakRegularity) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hcmp : ∀ (C : ℝ) (d ℓ : ℕ), 1 ≤ C → 0 < d → 0 < ℓ →
      ∀ α β : ℝ, BadlyApproximable α → AdmissibleBeta β →
      ∀ F : Circle → ℂ, (∃ K : ℝ≥0, LipschitzWith K F) →
        RelativeSelectorComparison c₀ C d ℓ (heisenbergPhase α β) F) :
    HeisenbergRecurrence := by
  apply heisenbergRecurrence_of_density_increment
  intro ℓ P hP α β hα hβ J
  obtain ⟨C, hC, hcoeff⟩ := exists_family_coefficientBound P hP
  obtain ⟨F, K, hLip, hSupp, hUnit, hMean⟩ := J.exists_supported_lipschitz_minorant
  have hLipC : LipschitzWith K (fun x => (F x : ℂ)) := by
    simpa only [one_mul] using Complex.isometry_ofReal.lipschitz.comp hLip
  have hd : 0 < (P (Fin.last ℓ)).natDegree := by
    have hne : (Fin.last ℓ) ≠ (0 : Fin (ℓ+1)) := by
      intro he
      have hh : ℓ = 0 := by simpa only [Fin.val_last, Fin.val_zero] using congrArg Fin.val he
      have hℓ := hP.1
      omega
    exact (hcoeff _ hne).2.2.1
  exact densityIncrementFor_of_relativeSelectorComparison hreg P hP hc₀ hC hcoeff
    (heisenbergPhase α β) J F hSupp hUnit hMean
    (hcmp C (P (Fin.last ℓ)).natDegree ℓ hC hd hP.1 α β hα hβ _ ⟨K, hLipC⟩)

end NilBohr
