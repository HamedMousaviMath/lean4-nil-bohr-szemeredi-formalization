import NilBohr.PointwiseSelector

/-! Product circle rotations for the quadratic twists in Corollary 1.5. -/

namespace NilBohr

open Filter MeasureTheory Polynomial
open scoped BigOperators Topology ENNReal NNReal

variable {X Y : Type*}

private def prodPermHom : (Equiv.Perm X × Equiv.Perm Y) →* Equiv.Perm (X × Y) where
  toFun ef := ef.1.prodCongr ef.2
  map_one' := by ext x <;> rfl
  map_mul' e f := by ext x <;> rfl

private theorem prodCongr_zpow (e : Equiv.Perm X) (f : Equiv.Perm Y) (m : ℤ) :
    (e.prodCongr f) ^ m = (e ^ m).prodCongr (f ^ m) := by
  have h := (map_zpow (prodPermHom (X := X) (Y := Y)) (e, f) m).symm
  exact h

/-- Haar probability measure of the two rotation coordinates. -/
noncomputable def twoTorusHaar : Measure (Circle × Circle) :=
  AddCircle.haarAddCircle.prod AddCircle.haarAddCircle

instance : IsProbabilityMeasure twoTorusHaar := by
  unfold twoTorusHaar
  infer_instance

variable [MeasurableSpace X] {μ : Measure X}

private def rotationPerm (ω₁ ω₂ : ℝ) : Equiv.Perm (Circle × Circle) :=
  (Equiv.addRight (ω₁ : Circle)).prodCongr (Equiv.addRight (ω₂ : Circle))

private theorem rotationPerm_apply_zpow (ω₁ ω₂ : ℝ) (m : ℤ) (t : Circle × Circle) :
    (rotationPerm ω₁ ω₂ ^ m) t =
      (t.1 + m • (ω₁ : Circle), t.2 + m • (ω₂ : Circle)) := by
  rw [rotationPerm, prodCongr_zpow, Equiv.zpow_addRight, Equiv.zpow_addRight]
  rfl

/-- The product of the original system with two translations of the
additive circle equipped with Haar probability measure. -/
def circleRotationExtension [IsFiniteMeasure μ] (T : ProbabilitySystem X μ)
    (ω₁ ω₂ : ℝ) : ProbabilitySystem (X × (Circle × Circle)) (μ.prod twoTorusHaar) where
  transform := T.transform.prodCongr (rotationPerm ω₁ ω₂)
  preserves m := by
    let ν : Measure Circle := AddCircle.haarAddCircle
    have h₁ := measurePreserving_add_right ν (m • (ω₁ : Circle))
    have h₂ := measurePreserving_add_right ν (m • (ω₂ : Circle))
    have hp := (T.preserves m).prod (h₁.prod h₂)
    rw [prodCongr_zpow]
    convert hp using 1
    funext z
    change ((T.transform ^ m) z.1, (rotationPerm ω₁ ω₂ ^ m) z.2) = _
    rw [rotationPerm_apply_zpow]
    rfl

theorem circleRotationExtension_zpow_apply [IsFiniteMeasure μ] (T : ProbabilitySystem X μ)
    (ω₁ ω₂ : ℝ) (m : ℤ) (x : X) (t : Circle × Circle) :
    ((circleRotationExtension T ω₁ ω₂).transform ^ m) (x, t) =
      ((T.transform ^ m) x, t.1 + m • (ω₁ : Circle), t.2 + m • (ω₂ : Circle)) := by
  unfold circleRotationExtension
  rw [prodCongr_zpow]
  exact congrArg (Prod.mk ((T.transform ^ m) x)) (rotationPerm_apply_zpow ω₁ ω₂ m t)

/-- The first Fourier character of the additive circle. -/
noncomputable def circleCharacter (t : Circle) : ℂ :=
  fourier (T := 1) 1 t

private theorem circleCharacter_coe (u : ℝ) : circleCharacter (u : Circle) = phase u := by
  rw [circleCharacter, fourier_coe_apply, phase]
  simp

private theorem circleCharacter_add (t u : Circle) :
    circleCharacter (t + u) = circleCharacter t * circleCharacter u := by
  simp only [circleCharacter, fourier_one, AddCircle.toCircle_add, _root_.Circle.coe_mul]

private theorem norm_circleCharacter (t : Circle) : ‖circleCharacter t‖ = 1 := by
  simp [circleCharacter, fourier_one]

private theorem phase_add (s t : ℝ) : phase (s + t) = phase s * phase t := by
  simp only [phase, Complex.ofReal_add, mul_add, Complex.exp_add]

private theorem circleCharacter_zsmul (t : Circle) (w : ℝ) (n : ℤ) :
    circleCharacter (t + n • (w : Circle)) = circleCharacter t * phase ((n : ℝ) * w) := by
  rw [circleCharacter_add, ← QuotientAddGroup.mk_zsmul, circleCharacter_coe, zsmul_eq_mul]

/-- Insert the first circle character at one input and the second
circle character at another input. -/
noncomputable def rotationInputs {ℓ : ℕ} (f : Fin ℓ → X → ℂ) (i₁ i₂ : Fin ℓ)
    (i : Fin ℓ) (z : X × (Circle × Circle)) : ℂ :=
  f i z.1 * (if i = i₁ then circleCharacter z.2.1 else 1) *
    (if i = i₂ then circleCharacter z.2.2 else 1)

/-- Rotation input functions preserve (L^infty) membership. -/
theorem memLp_rotationInputs [IsFiniteMeasure μ]
    {ℓ : ℕ} (f : Fin ℓ → X → ℂ) (hf : ∀ i, MemLp (f i) ∞ μ)
    (i₁ i₂ i : Fin ℓ) : MemLp (rotationInputs f i₁ i₂ i) ∞ (μ.prod twoTorusHaar) := by
  let F : X × (Circle × Circle) → ℂ := fun z => f i z.1
  let c₁ : (X × (Circle × Circle)) → ℂ :=
    fun z => if i = i₁ then circleCharacter z.2.1 else 1
  let c₂ : (X × (Circle × Circle)) → ℂ :=
    fun z => if i = i₂ then circleCharacter z.2.2 else 1
  have hF : AEStronglyMeasurable F (μ.prod twoTorusHaar) :=
    (hf i).1.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
  have hc : Continuous circleCharacter := (fourier (T := 1) 1).continuous
  have hc₁ : AEStronglyMeasurable c₁ (μ.prod twoTorusHaar) := by
    by_cases h : i = i₁
    · simpa only [c₁, h, if_true] using
        (hc.measurable.comp (measurable_fst.comp measurable_snd :
          Measurable (fun z : X × (Circle × Circle) => z.2.1))).aestronglyMeasurable
    · simpa only [c₁, h, if_false] using
        (aestronglyMeasurable_const :
          AEStronglyMeasurable (fun _ : X × (Circle × Circle) => (1 : ℂ)) (μ.prod twoTorusHaar))
  have hc₂ : AEStronglyMeasurable c₂ (μ.prod twoTorusHaar) := by
    by_cases h : i = i₂
    · simpa only [c₂, h, if_true] using
        (hc.measurable.comp (measurable_snd.comp measurable_snd :
          Measurable (fun z : X × (Circle × Circle) => z.2.2))).aestronglyMeasurable
    · simpa only [c₂, h, if_false] using
        (aestronglyMeasurable_const :
          AEStronglyMeasurable (fun _ : X × (Circle × Circle) => (1 : ℂ)) (μ.prod twoTorusHaar))
  have h_b : ∃ B : ℝ≥0, ∀ᵐ x ∂μ, ‖f i x‖₊ ≤ B :=
    eLpNormEssSup_lt_top_iff_isBoundedUnder.mp (by
      simpa [eLpNorm_exponent_top] using (hf i).2)
  obtain ⟨B, hB⟩ := h_b
  apply MemLp.of_bound ((hF.mul hc₁).mul hc₂) (B : ℝ)
  have hB' : ∀ᵐ z ∂μ.prod twoTorusHaar, ‖f i z.1‖₊ ≤ B :=
    Measure.quasiMeasurePreserving_fst.ae hB
  filter_upwards [hB'] with z hz
  change ‖rotationInputs f i₁ i₂ i z‖ ≤ (B : ℝ)
  simp only [rotationInputs, norm_mul]
  have h₁ : ‖(if i = i₁ then circleCharacter z.2.1 else 1)‖ = 1 := by
    split_ifs <;> simp [norm_circleCharacter]
  have h₂ : ‖(if i = i₂ then circleCharacter z.2.2 else 1)‖ = 1 := by
    split_ifs <;> simp [norm_circleCharacter]
  rw [h₁, h₂, mul_one, mul_one]
  exact hz

/-- Equation (53) of Corollary 1.5, before the constant term of the
test phase is put back. All inputs away from the two twisting indices
are the corresponding inputs of the enlarged family. -/
theorem ergodicSequence_circleRotationExtension [IsFiniteMeasure μ]
    (T : ProbabilitySystem X μ) {ℓ : ℕ} (Q : Fin ℓ → Polynomial ℤ)
    (f : Fin ℓ → X → ℂ) (i₁ i₂ : Fin ℓ) (ω₁ ω₂ : ℝ)
    (n : ℤ) (x : X) (t : Circle × Circle) :
    ergodicSequence (circleRotationExtension T ω₁ ω₂) Q (rotationInputs f i₁ i₂) n (x,t) =
      (circleCharacter t.1 * circleCharacter t.2) *
      (phase (ω₁ * (((Q i₁).eval n : ℤ) : ℝ) + ω₂ * (((Q i₂).eval n : ℤ) : ℝ)) *
        ergodicSequence T Q f n x) := by
  unfold ergodicSequence
  simp_rw [circleRotationExtension_zpow_apply, rotationInputs]
  simp only [Finset.prod_mul_distrib]
  have h₁ : (∏ i, if i = i₁ then circleCharacter (t.1 + (Q i).eval n • (ω₁ : Circle)) else 1) =
        circleCharacter (t.1 + (Q i₁).eval n • (ω₁ : Circle)) := by
    rw [Finset.prod_eq_single i₁] <;> simp_all
  have h₂ : (∏ i, if i = i₂ then circleCharacter (t.2 + (Q i).eval n • (ω₂ : Circle)) else 1) =
        circleCharacter (t.2 + (Q i₂).eval n • (ω₂ : Circle)) := by
    rw [Finset.prod_eq_single i₂] <;> simp_all
  rw [h₁, h₂, circleCharacter_zsmul, circleCharacter_zsmul, phase_add,
    mul_comm ω₁, mul_comm ω₂]
  ring

private theorem primeAverage_const_mul (g : ℕ → ℂ) (c : ℂ) (N : ℕ) :
    primeAverage (fun p => c * g p) N = c * primeAverage g N := by
  unfold primeAverage
  rw [← mul_div_assoc, Finset.mul_sum]

/-- Fubini removes the two rotation variables from a centered prime
comparison on the product space. The scalar weight (v) is unchanged. -/
theorem ae_tendsto_primeAverage_twisted_of_rotation [IsFiniteMeasure μ]
    (T : ProbabilitySystem X μ) {ℓ : ℕ} (Q : Fin ℓ → Polynomial ℤ)
    (f : Fin ℓ → X → ℂ) (i₁ i₂ : Fin ℓ) (ω₁ ω₂ : ℝ) (v : ℕ → ℂ)
    (h : ∀ᵐ z ∂μ.prod twoTorusHaar,
      Tendsto (primeAverage (fun p => v p * ergodicSequence (circleRotationExtension T ω₁ ω₂)
        Q (rotationInputs f i₁ i₂) ((p : ℤ) - 1) z)) atTop (𝓝 0)) :
    ∀ᵐ x ∂μ, Tendsto (primeAverage (fun p => v p *
      phase (ω₁ * (((Q i₁).eval ((p : ℤ) - 1) : ℤ) : ℝ) +
        ω₂ * (((Q i₂).eval ((p : ℤ) - 1) : ℤ) : ℝ)) *
      ergodicSequence T Q f ((p : ℤ) - 1) x)) atTop (𝓝 0) := by
  filter_upwards [Measure.ae_ae_of_ae_prod h] with x hx
  obtain ⟨t, ht⟩ := hx.exists
  let c := circleCharacter t.1 * circleCharacter t.2
  have hc : c ≠ 0 := by
    have hnorm : ‖c‖ = 1 := by simp [c, norm_mul, norm_circleCharacter]
    exact norm_ne_zero_iff.mp (by simp [hnorm])
  let a (p : ℕ) := v p *
    phase (ω₁ * (((Q i₁).eval ((p : ℤ) - 1) : ℤ) : ℝ) +
      ω₂ * (((Q i₂).eval ((p : ℤ) - 1) : ℤ) : ℝ)) *
    ergodicSequence T Q f ((p : ℤ) - 1) x
  have hpoint (p : ℕ) :
      v p * ergodicSequence (circleRotationExtension T ω₁ ω₂)
        Q (rotationInputs f i₁ i₂) ((p : ℤ) - 1) (x,t) = c * a p := by
    rw [ergodicSequence_circleRotationExtension]
    dsimp [c, a]
    ring
  simp_rw [hpoint] at ht
  have ht' : Tendsto (fun N => c * primeAverage a N) atTop (𝓝 0) := by
    exact ht.congr (fun N => primeAverage_const_mul a c N)
  simpa only [mul_zero, ← mul_assoc, inv_mul_cancel₀ hc, one_mul] using ht'.const_mul c⁻¹


private theorem eval_of_natDegree_le_two {R : Type*} [CommSemiring R]
    (P : Polynomial R) (hP : P.natDegree ≤ 2) (x : R) :
    P.eval x = P.coeff 0 + P.coeff 1 * x + P.coeff 2 * x ^ 2 := by
  have h := congrArg (eval x) (P.as_sum_range' 3 (by omega))
  simpa only [eval_finset_sum, eval_monomial, eval_add, Finset.sum_range_succ, Finset.sum_range_zero,
    zero_add, pow_zero, pow_one, mul_one] using h

/-- Any real quadratic test, after subtracting its constant term, lies in
the span of the designated linear and quadratic integer shifts. -/
theorem quadratic_test_span {Q₁ Q₂ : Polynomial ℤ}
    (hd₁ : Q₁.natDegree = 1) (hd₂ : Q₂.natDegree = 2)
    (hz₁ : Q₁.coeff 0 = 0) (hz₂ : Q₂.coeff 0 = 0)
    (ψ : Polynomial ℝ) (hψ : ψ.natDegree ≤ 2) :
    ∃ ω₁ ω₂ : ℝ, ∀ n : ℤ, ψ.eval (n : ℝ) - ψ.eval 0 =
      ω₁ * ((Q₁.eval n : ℤ) : ℝ) + ω₂ * ((Q₂.eval n : ℤ) : ℝ) := by
  let a : ℝ := (Q₁.coeff 1 : ℝ)
  let b : ℝ := (Q₂.coeff 2 : ℝ)
  let c : ℝ := (Q₂.coeff 1 : ℝ)
  have ha : a ≠ 0 := by
    have h : Q₁.coeff 1 ≠ 0 := by
      rw [← hd₁, coeff_natDegree, leadingCoeff_ne_zero]
      intro hz
      simp [hz] at hd₁
    change (Q₁.coeff 1 : ℝ) ≠ 0
    exact_mod_cast h
  have hb : b ≠ 0 := by
    have h : Q₂.coeff 2 ≠ 0 := by
      rw [← hd₂, coeff_natDegree, leadingCoeff_ne_zero]
      intro hz
      simp [hz] at hd₂
    change (Q₂.coeff 2 : ℝ) ≠ 0
    exact_mod_cast h
  let ω₂ := ψ.coeff 2 / b
  let ω₁ := (ψ.coeff 1 - ω₂ * c) / a
  refine ⟨ω₁, ω₂, fun n => ?_⟩
  have h21 : Q₁.coeff 2 = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have hlin : ((Q₁.eval n : ℤ) : ℝ) = a * (n : ℝ) := by
    rw [eval_of_natDegree_le_two Q₁ (by omega), hz₁, h21]
    push_cast
    simp [a]
  have hquad : ((Q₂.eval n : ℤ) : ℝ) = c * (n : ℝ) + b * (n : ℝ) ^ 2 := by
    rw [eval_of_natDegree_le_two Q₂ (by omega), hz₂]
    push_cast
    simp [b, c]
  have hzero : ψ.eval 0 = ψ.coeff 0 := by simpa using eval_of_natDegree_le_two ψ hψ 0
  rw [eval_of_natDegree_le_two ψ hψ, hzero, hlin, hquad]
  dsimp [ω₁, ω₂]
  field_simp [ha, hb]
  ring

/-- For a family with a linear and a quadratic member, a centered
comparison in every product rotation gives all real quadratic twists. -/
theorem ae_tendsto_primeAverage_quadratic_twist [IsFiniteMeasure μ]
    (T : ProbabilitySystem X μ) {ℓ : ℕ} (Q : Fin ℓ → Polynomial ℤ)
    (f : Fin ℓ → X → ℂ) (i₁ i₂ : Fin ℓ) (v : ℕ → ℂ)
    (hd₁ : (Q i₁).natDegree = 1) (hd₂ : (Q i₂).natDegree = 2)
    (hz₁ : (Q i₁).coeff 0 = 0) (hz₂ : (Q i₂).coeff 0 = 0)
    (ψ : Polynomial ℝ) (hψ : ψ.natDegree ≤ 2)
    (h : ∀ ω₁ ω₂ : ℝ, ∀ᵐ z ∂μ.prod twoTorusHaar,
      Tendsto (primeAverage (fun p => v p * ergodicSequence (circleRotationExtension T ω₁ ω₂)
        Q (rotationInputs f i₁ i₂) ((p : ℤ) - 1) z)) atTop (𝓝 0)) :
    ∀ᵐ x ∂μ, Tendsto (primeAverage (fun p => v p *
      phase (ψ.eval ((p : ℝ) - 1)) *
      ergodicSequence T Q f ((p : ℤ) - 1) x)) atTop (𝓝 0) := by
  obtain ⟨ω₁, ω₂, hω⟩ := quadratic_test_span hd₁ hd₂ hz₁ hz₂ ψ hψ
  filter_upwards [ae_tendsto_primeAverage_twisted_of_rotation T Q f i₁ i₂ ω₁ ω₂ v
    (h ω₁ ω₂)] with x hx
  let c := phase (ψ.eval 0)
  have hphase (p : ℕ) :
      phase (ψ.eval ((p : ℝ) - 1)) =
        c * phase (ω₁ * (((Q i₁).eval ((p : ℤ) - 1) : ℤ) : ℝ) +
          ω₂ * (((Q i₂).eval ((p : ℤ) - 1) : ℤ) : ℝ)) := by
    have He := hω ((p : ℤ) - 1)
    push_cast at He
    rw [← He]
    dsimp only [c]
    rw [← phase_add]
    congr 1
    ring
  have he (p : ℕ) :
      v p * phase (ψ.eval ((p : ℝ) - 1)) * ergodicSequence T Q f ((p : ℤ) - 1) x =
        c * (v p * phase (ω₁ * (((Q i₁).eval ((p : ℤ) - 1) : ℤ) : ℝ) +
          ω₂ * (((Q i₂).eval ((p : ℤ) - 1) : ℤ) : ℝ)) *
            ergodicSequence T Q f ((p : ℤ) - 1) x) := by
    rw [hphase]
    ring
  simp_rw [he]
  have hh := hx.const_mul c
  rw [mul_zero] at hh
  exact hh.congr (fun N => (primeAverage_const_mul _ c N).symm)


/-- Insert the missing linear and quadratic shifts with constant inputs.
Filling any further missing degrees in the enlarged finite degree range
gives a simply indexed distinct-degree family with the same product. -/
theorem exists_quadratic_completion [IsFiniteMeasure μ]
    (T : ProbabilitySystem X μ) {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ)
    (hP : ErgodicPolynomialFamily P) (f : Fin ℓ → X → ℂ)
    (hf : ∀ i, MemLp (f i) ∞ μ) :
    ∃ (d : ℕ) (Q : Fin d → Polynomial ℤ) (g : Fin d → X → ℂ) (i₁ i₂ : Fin d),
      ErgodicPolynomialFamily Q ∧
      (Q i₁).natDegree = 1 ∧ (Q i₂).natDegree = 2 ∧
      (∀ i, MemLp (g i) ∞ μ) ∧
      ∀ n x, ergodicSequence T Q g n x = ergodicSequence T P f n x := by
  classical
  let d := max 2 (Finset.univ.sup (fun i => (P i).natDegree))
  have hd : 2 ≤ d := le_max_left _ _
  have hle (i : Fin ℓ) : (P i).natDegree ≤ d :=
    (Finset.le_sup (s := Finset.univ) (f := fun j => (P j).natDegree)
      (Finset.mem_univ i)).trans (le_max_right _ _)
  let Q (j : Fin d) : Polynomial ℤ :=
    if h : ∃ i, (P i).natDegree = (j : ℕ) + 1 then P (Classical.choose h)
    else Polynomial.X ^ ((j : ℕ) + 1)
  let g (j : Fin d) : X → ℂ :=
    if h : ∃ i, (P i).natDegree = (j : ℕ) + 1 then f (Classical.choose h)
    else fun _ => 1
  have hdeg (j : Fin d) : (Q j).natDegree = (j : ℕ) + 1 := by
    unfold Q
    split_ifs with h
    · exact Classical.choose_spec h
    · exact natDegree_X_pow ((j : ℕ) + 1)
  have hz (j : Fin d) : (Q j).coeff 0 = 0 := by
    unfold Q
    split_ifs with h
    · exact (hP.2.1 _).2
    · rw [coeff_X_pow]
      simp
  have hQ : ErgodicPolynomialFamily Q := by
    refine ⟨by omega, fun j => ⟨by rw [hdeg]; omega, hz j⟩, ?_⟩
    intro i j hij
    simp only [hdeg]
    omega
  have hg (j : Fin d) : MemLp (g j) ∞ μ := by
    unfold g
    split_ifs
    · exact hf _
    · exact memLp_const _
  let e : Fin ℓ ↪ Fin d := {
    toFun := fun i => ⟨(P i).natDegree - 1, by
      have := (hP.2.1 i).1
      have := hle i
      omega⟩
    inj' := by
      intro i j hij
      apply hP.2.2.injective
      change (P i).natDegree = (P j).natDegree
      have h0 := congrArg Fin.val hij
      change (P i).natDegree - 1 = (P j).natDegree - 1 at h0
      have := (hP.2.1 i).1
      have := (hP.2.1 j).1
      omega }
  have he (i : Fin ℓ) : (e i : ℕ) + 1 = (P i).natDegree := by
    change (P i).natDegree - 1 + 1 = (P i).natDegree
    have := (hP.2.1 i).1
    omega
  have h_orig (i : Fin ℓ) : Q (e i) = P i ∧ g (e i) = f i := by
    have hd' : ∃ k, (P k).natDegree = (e i : ℕ) + 1 := ⟨i, (he i).symm⟩
    have hc : Classical.choose hd' = i := hP.2.2.injective
      ((Classical.choose_spec hd').trans (he i))
    simp [Q, g, hd', hc]
  have h_new (j : Fin d) (hj : j ∉ Finset.univ.map e) : g j = fun _ => 1 := by
    unfold g
    split_ifs with h
    · exfalso
      apply hj
      obtain ⟨i, hi⟩ := h
      have h_ij : e i = j := by
        apply Fin.ext
        have heq := he i
        omega
      exact Finset.mem_map.mpr ⟨i, Finset.mem_univ i, h_ij⟩
    · rfl
  let i₁ : Fin d := ⟨0, by omega⟩
  let i₂ : Fin d := ⟨1, by omega⟩
  refine ⟨d, Q, g, i₁, i₂, hQ, hdeg i₁, hdeg i₂, hg, ?_⟩
  intro n x
  unfold ergodicSequence
  let productTerm j := g j ((T.transform ^ (Q j).eval n) x)
  have hsub : Finset.univ.map e ⊆ Finset.univ := Finset.subset_univ _
  have hprod : (∏ j ∈ Finset.univ.map e, productTerm j) =
      ∏ j, productTerm j := by
    apply Finset.prod_subset hsub
    intro j _ hj
    simp [productTerm, h_new j hj]
  change (∏ j, productTerm j) = _
  rw [← hprod, Finset.prod_map]
  apply Finset.prod_congr rfl
  intro i _
  simp [productTerm, (h_orig i).1, (h_orig i).2]

/-- The rotation reduction applies to every original distinct-degree
family, including families whose first degree is above two. The premise
is the centered prime comparison on the product probability space. -/
theorem ae_tendsto_primeAverage_quadratic_twist_of_centered [IsProbabilityMeasure μ]
    (T : ProbabilitySystem X μ) {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ)
    (hP : ErgodicPolynomialFamily P) (f : Fin ℓ → X → ℂ)
    (hf : ∀ i, MemLp (f i) ∞ μ) (v : ℕ → ℂ)
    (ψ : Polynomial ℝ) (hψ : ψ.natDegree ≤ 2)
    (h : ∀ (S : ProbabilitySystem (X × (Circle × Circle)) (μ.prod twoTorusHaar))
      {d : ℕ} (Q : Fin d → Polynomial ℤ), ErgodicPolynomialFamily Q →
      ∀ (g : Fin d → X × (Circle × Circle) → ℂ),
        (∀ i, MemLp (g i) ∞ (μ.prod twoTorusHaar)) →
      ∀ᵐ z ∂μ.prod twoTorusHaar,
        Tendsto (primeAverage (fun p => v p *
          ergodicSequence S Q g ((p : ℤ) - 1) z)) atTop (𝓝 0)) :
    ∀ᵐ x ∂μ, Tendsto (primeAverage (fun p => v p *
      phase (ψ.eval ((p : ℝ) - 1)) *
      ergodicSequence T P f ((p : ℤ) - 1) x)) atTop (𝓝 0) := by
  obtain ⟨d, Q, g, i₁, i₂, hQ, hd₁, hd₂, hg, h_eq⟩ :=
    exists_quadratic_completion T P hP f hf
  have h_rot := ae_tendsto_primeAverage_quadratic_twist T Q g i₁ i₂ v hd₁ hd₂
    (hQ.2.1 i₁).2 (hQ.2.1 i₂).2 ψ hψ
    (fun ω₁ ω₂ => h (circleRotationExtension T ω₁ ω₂) Q hQ (rotationInputs g i₁ i₂)
      (memLp_rotationInputs g hg i₁ i₂))
  simpa only [h_eq] using h_rot


/-- Every Fourier character is Lipschitz for the quotient circle metric. -/
theorem exists_lipschitzWith_fourier (h : ℤ) :
    ∃ K : ℝ≥0, LipschitzWith K (fourier (T := 1) h : Circle → ℂ) := by
  let K := ‖(2 * (Real.pi : ℂ) * Complex.I * (h : ℂ) / (1 : ℂ))‖₊
  let F : ℝ → ℂ := fun x => fourier (T := 1) h (x : Circle)
  have hd (x : ℝ) : HasDerivAt F
      (2 * (Real.pi : ℂ) * Complex.I * (h : ℂ) / 1 * F x) x := by
    simpa only [F, Complex.ofReal_one] using hasDerivAt_fourier (1 : ℝ) h x
  have hR : LipschitzWith K F := by
    refine lipschitzWith_of_nnnorm_deriv_le (fun x => (hd x).differentiableAt) (fun x => ?_)
    rw [(hd x).deriv, nnnorm_mul]
    have hx : ‖F x‖₊ = 1 := by
      apply NNReal.eq
      change ‖fourier (T := 1) h (x : Circle)‖ = (1 : ℝ)
      rw [fourier_apply]
      exact _root_.Circle.norm_coe _
    rw [hx, mul_one]
  refine ⟨K, LipschitzWith.of_dist_le_mul (fun x y => ?_)⟩
  obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective x
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective y
  let m : ℤ := round (u - v)
  have hm : ((m : ℝ) : Circle) = 0 := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨m, by simp⟩
  have hrep : ((u - (m : ℝ) : ℝ) : Circle) = (u : Circle) := by
    rw [AddCircle.coe_sub, hm, sub_zero]
  have hdist : dist (u - (m : ℝ)) v = dist (u : Circle) (v : Circle) := by
    rw [Real.dist_eq, dist_eq_norm, ← AddCircle.coe_sub, AddCircle.norm_eq]
    simp only [inv_one, one_mul, mul_one]
    change |u - (m : ℝ) - v| = |u - v - (m : ℝ)|
    congr 1
    ring
  simpa only [F, hrep, hdist] using hR.dist_le_mul (u - (m : ℝ)) v

/-- A nonzero Fourier character has zero average against Haar measure. -/
theorem circleMean_fourier_eq_zero {h : ℤ} (hh : h ≠ 0) :
    circleMean (fourier (T := 1) h) = 0 :=
  integral_eq_zero_of_add_right_eq_neg (μ := (AddCircle.haarAddCircle : Measure Circle))
    (fourier_add_half_inv_index hh (by norm_num : (0 : ℝ) < 1))

private theorem fourier_coe_eq_phase (h : ℤ) (u : ℝ) :
    fourier (T := 1) h (u : Circle) = phase ((h : ℝ) * u) := by
  simp only [fourier_coe_apply, Complex.ofReal_one, div_one, phase,
    Complex.ofReal_mul, Complex.ofReal_intCast, mul_assoc]

/-- Equation (52) for any phase whose centered smooth prime comparison
is available on the product systems. This proof uses the Lipschitz
Fourier character directly in Proposition 7.1, thereby avoiding the
step-function approximation of that character. -/
theorem ae_tendsto_primeAverage_fourier_quadratic_twist [IsProbabilityMeasure μ]
    (T : ProbabilitySystem X μ) {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ)
    (hP : ErgodicPolynomialFamily P) (f : Fin ℓ → X → ℂ)
    (hf : ∀ i, MemLp (f i) ∞ μ) (V : ℤ → ℝ) (h : ℤ) (hh : h ≠ 0)
    (ψ : Polynomial ℝ) (hψ : ψ.natDegree ≤ 2)
    (h_smooth : ∀ (S : ProbabilitySystem (X × (Circle × Circle)) (μ.prod twoTorusHaar))
      {d : ℕ} (Q : Fin d → Polynomial ℤ), ErgodicPolynomialFamily Q →
      SmoothPrimeLimit S Q V) :
    ∀ᵐ x ∂μ, Tendsto (primeAverage (fun p =>
      phase ((h : ℝ) * V ((p : ℤ) - 1) + ψ.eval ((p : ℝ) - 1)) *
      ergodicSequence T P f ((p : ℤ) - 1) x)) atTop (𝓝 0) := by
  have h_rot := ae_tendsto_primeAverage_quadratic_twist_of_centered
    T P hP f hf (fun p => phase ((h : ℝ) * V ((p : ℤ) - 1))) ψ hψ ?_
  · simpa only [phase_add] using h_rot
  · intro S d Q hQ g hg
    have h' := h_smooth S Q hQ g hg (fourier (T := 1) h) (exists_lipschitzWith_fourier h)
    simpa only [circleMean_fourier_eq_zero hh, sub_zero, fourier_coe_eq_phase] using h'


/-- The centered interval version of the rotation reduction, equation (54),
from the smooth comparison on all product systems. -/
theorem ae_quadratic_twisted_interval_of_smooth [IsProbabilityMeasure μ]
    (T : ProbabilitySystem X μ) {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ)
    (hP : ErgodicPolynomialFamily P) (f : Fin ℓ → X → ℂ)
    (hf : ∀ i, MemLp (f i) ∞ μ) (V : ℤ → ℝ) (J : OpenArc)
    (ψ : Polynomial ℝ) (hψ : ψ.natDegree ≤ 2)
    (h_smooth : ∀ (S : ProbabilitySystem (X × (Circle × Circle)) (μ.prod twoTorusHaar))
      {d : ℕ} (Q : Fin d → Polynomial ℤ), ErgodicPolynomialFamily Q →
      SmoothPrimeLimit S Q V) :
    ∀ᵐ x ∂μ, Tendsto (primeAverage (fun p =>
      ((J.indicator (V ((p : ℤ) - 1)) : ℂ) - (J.length : ℂ)) *
      phase (ψ.eval ((p : ℝ) - 1)) *
      ergodicSequence T P f ((p : ℤ) - 1) x)) atTop (𝓝 0) := by
  refine ae_tendsto_primeAverage_quadratic_twist_of_centered T P hP f hf
    (fun p => (J.indicator (V ((p : ℤ) - 1)) : ℂ) - (J.length : ℂ)) ψ hψ ?_
  intro S d Q hQ g hg
  have hs := ae_centered_selector_of_smooth_limits S Q g hg V J (h_smooth S Q hQ)
  filter_upwards [hs] with z hz
  let a (p : ℕ) := ergodicSequence S Q g ((p : ℤ) - 1) z
  change Tendsto (fun N => selectedOverPrimes V J a N - (J.length : ℂ) * primeAverage a N)
    atTop (𝓝 0) at hz
  have hcounts (N : ℕ) : selectedOverPrimes V J a N - (J.length : ℂ) * primeAverage a N =
      primeAverage (fun p => ((J.indicator (V ((p : ℤ) - 1)) : ℂ) - (J.length : ℂ)) * a p) N := by
    rw [selectedOverPrimes_eq_weighted]
    simp only [primeAverage, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, sub_div, mul_div_assoc]
  exact hz.congr hcounts

/-- The two horizontal cells in the bracket Fourier expansion. The seam
(t=1-eta) is included in the second cell. -/
theorem phase_bracket_eq_piecewise (α β : ℝ) (n h : ℤ)
    (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1) :
    let t := Int.fract (β * (n : ℝ))
    phase ((h : ℝ) * bracketPhase α β n) =
      phase (-(h : ℝ) * heisenbergPhase α β n +
        (h : ℝ) * (α * β / 2) * ((n : ℝ)^2 + n)) *
      (if t < 1 - β then phase (-(h : ℝ) * α * t)
       else phase ((h : ℝ) * α * (n : ℝ)) * phase ((h : ℝ) * α * (1 - t))) := by
  dsimp only
  have hc := bracketPhase_add_heisenbergPhase α β n hβ₀ hβ₁
  split_ifs with ht
  · simp only [horizontalCarry, not_le.mpr ht, if_false, Int.cast_zero, mul_zero, add_zero] at hc
    rw [← phase_add]
    congr 1
    linear_combination (h : ℝ) * hc
  · simp only [horizontalCarry, le_of_not_gt ht, if_true, Int.cast_one, mul_one] at hc
    rw [← phase_add, ← phase_add]
    congr 1
    linear_combination (h : ℝ) * hc

end NilBohr
