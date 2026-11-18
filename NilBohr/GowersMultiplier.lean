import NilBohr.GowersComparison

/-! Fourier multipliers for the interval Gowers quantities. The proof uses
the pointwise Fourier reconstruction theorem already available in Mathlib. -/

open Filter AddCircle
open scoped Topology BigOperators NNReal ComplexConjugate

namespace NilBohr

private theorem cubeProduct_const_complex (steps : List ℤ) (hs : 1 ≤ steps.length)
    (z : ℂ) (x : ℤ) :
    cubeProduct steps (fun _ => z) x = ((‖z‖^(2^steps.length : ℕ) : ℝ) : ℂ) := by
  induction steps generalizing x with
  | nil => simp at hs
  | cons t ts ih =>
    by_cases ht : ts = []
    · subst ts
      simpa [cubeProduct, Complex.normSq_eq_norm_sq] using Complex.mul_conj z
    · have hts : 1 ≤ ts.length := by
        cases ts <;> simp_all
      rw [cubeProduct, ih hts x, ih hts (x+t), Complex.conj_ofReal, ← Complex.ofReal_mul]
      simp only [List.length_cons, pow_succ (2 : ℕ), pow_mul, pow_two]

private theorem cubePower_complex_scale (L U : ℤ) (S : ℕ) (hS : 1 ≤ S)
    (z : ℂ) (f : ℤ → ℂ) :
    gowersCubePower S L U (fun n => z*f n) =
      gowersCubePower S L U (fun n => (‖z‖ : ℂ)*f n) := by
  have hzero (c : ℂ) : zeroOutside L U (fun n => c*f n) =
      (fun n => c*zeroOutside L U f n) := by
    funext n
    unfold zeroOutside
    split_ifs <;> simp
  let dirs (h : Fin S → Fin (2*(U-L).toNat+1)) : List ℤ :=
    List.ofFn (fun j => ((h j).val : ℤ) - ((U-L).toNat : ℤ))
  change (∑ x ∈ Finset.Icc L U, ∑ h, cubeProduct (dirs h)
      (zeroOutside L U (fun n => z*f n)) x) =
    ∑ x ∈ Finset.Icc L U, ∑ h, cubeProduct (dirs h)
      (zeroOutside L U (fun n => (‖z‖ : ℂ)*f n)) x
  simp only [hzero, cubeProduct_mul]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun h _ => ?_
  have hd : 1 ≤ (dirs h).length := by simpa [dirs] using hS
  rw [cubeProduct_const_complex _ hd z, cubeProduct_const_complex _ hd (‖z‖ : ℂ)]
  simp

/-- A complex coefficient costs precisely its modulus in the normalized
Gowers quantity. -/
theorem normalizedGowers_complex_scale (L U : ℤ) (S : ℕ) (hS : 1 ≤ S)
    (z : ℂ) (f : ℤ → ℂ) :
    normalizedGowers S L U (fun n => z*f n) = ‖z‖ * normalizedGowers S L U f := by
  rw [show normalizedGowers S L U (fun n => z*f n) =
    normalizedGowers S L U (fun n => (‖z‖ : ℂ)*f n) by
    unfold normalizedGowers
    rw [cubePower_complex_scale L U S hS z]]
  exact normalizedGowers_real_scale L U S hS ‖z‖ (norm_nonneg _) f

private theorem cubeDifference_affine_phase_zero (A B : ℝ) (steps : List ℤ)
    (hs : 2 ≤ steps.length) (x : ℤ) :
    cubeDifference steps (fun n => A*n+B) x = 0 := by
  induction steps generalizing x with
  | nil => simp at hs
  | cons t ts ih =>
    by_cases hts : 2 ≤ ts.length
    · rw [cubeDifference, ih hts x, ih hts (x+t), sub_self]
    · cases ts with
      | nil => simp at hs
      | cons t' ts' =>
        cases ts' with
        | nil =>
          simp only [cubeDifference, Int.cast_add]
          ring
        | cons t'' ts'' => simp at hts

/-- Multiplication by an ordinary linear character preserves the exact
interval Gowers quantity in orders at least two. -/
theorem normalizedGowers_mul_linear_phase (L U : ℤ) (S : ℕ) (hS : 2 ≤ S)
    (A B : ℝ) (f : ℤ → ℂ) :
    normalizedGowers S L U (fun n => f n * phaseExponential (A*n+B)) =
      normalizedGowers S L U f := by
  have hzero : zeroOutside L U (fun n => f n * phaseExponential (A*n+B)) =
      (fun n => zeroOutside L U f n * phaseExponential (A*n+B)) := by
    funext n
    unfold zeroOutside
    split_ifs <;> simp
  have heq : gowersCubePower S L U (fun n => f n * phaseExponential (A*n+B)) =
      gowersCubePower S L U f := by
    let dirs (h : Fin S → Fin (2*(U-L).toNat+1)) : List ℤ :=
      List.ofFn (fun j => ((h j).val : ℤ) - ((U-L).toNat : ℤ))
    change (∑ x ∈ Finset.Icc L U, ∑ h, cubeProduct (dirs h)
      (zeroOutside L U (fun n => f n*phaseExponential (A*n+B))) x) =
      ∑ x ∈ Finset.Icc L U, ∑ h, cubeProduct (dirs h) (zeroOutside L U f) x
    rw [hzero]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun h _ => ?_
    have hd : 2 ≤ (dirs h).length := by simpa [dirs] using hS
    simp only [cubeProduct_mul, cubeProduct_phaseExponential,
      cubeDifference_affine_phase_zero A B _ hd x, phaseExponential_zero, mul_one]
  unfold normalizedGowers
  rw [heq]

private theorem continuous_cube_zeroOutside (L U : ℤ) (steps : List ℤ) (x : ℤ) :
    Continuous (fun f : ℤ → ℂ => cubeProduct steps (zeroOutside L U f) x) := by
  induction steps generalizing x with
  | nil =>
    by_cases hx : x ∈ Finset.Icc L U
    · simpa [cubeProduct, zeroOutside, hx] using
        (continuous_apply x : Continuous fun f : ℤ → ℂ => f x)
    · simpa [cubeProduct, zeroOutside, hx] using
        (continuous_const : Continuous fun _ : ℤ → ℂ => (0 : ℂ))
  | cons t ts ih =>
    simpa only [cubeProduct] using
      (ih x).mul (Complex.continuous_conj.comp (ih (x+t)))

/-- The explicit normalization is continuous for pointwise convergence
of the input functions. Only the finitely many cube values occur. -/
theorem continuous_normalizedGowers (L U : ℤ) (S : ℕ) :
    Continuous (fun f : ℤ → ℂ => normalizedGowers S L U f) := by
  let dirs (h : Fin S → Fin (2*(U-L).toNat+1)) : List ℤ :=
    List.ofFn (fun j => ((h j).val : ℤ) - ((U-L).toNat : ℤ))
  have hCube : Continuous (fun f : ℤ → ℂ => gowersCubePower S L U f) := by
    change Continuous (fun f : ℤ → ℂ => ∑ x ∈ Finset.Icc L U, ∑ h,
      cubeProduct (dirs h) (zeroOutside L U f) x)
    refine continuous_finset_sum _ fun x _ => continuous_finset_sum _ fun h _ => ?_
    exact continuous_cube_zeroOutside L U (dirs h) x
  unfold normalizedGowers
  exact ((Complex.continuous_re.comp hCube).rpow_const (fun _ => Or.inr (by positivity))).div_const _

private theorem normalizedGowers_finset_sum_le {ι : Type*} (L U : ℤ) (S : ℕ)
    (hS : 1 ≤ S) (hLU : L ≤ U) (hG : NormalizedGowersLaws S)
    (I : Finset ι) (v : ι → ℤ → ℂ) :
    normalizedGowers S L U (fun x => ∑ i ∈ I, v i x) ≤
      ∑ i ∈ I, normalizedGowers S L U (v i) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    simpa using (normalizedGowers_real_scale L U S hS 0 le_rfl (fun _ => 0)).le
  | insert i I hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hG.triangle L U hLU _ _).trans (add_le_add_left ih _)

private theorem fourier_affine_as_phase (k : ℤ) (A B : ℝ) (x : ℤ) :
    fourier k ((A*x+B : ℝ) : Circle) =
      phaseExponential (((k : ℝ)*A)*x+(k : ℝ)*B) := by
  rw [fourier_coe_apply]
  unfold phaseExponential
  congr 1
  push_cast
  ring

/-- Multiplication by a circle function along an affine parameter. The
proof passes from finite Fourier sums to the Mathlib Fourier expansion. -/
theorem normalizedGowers_mul_circle_pullback (L U : ℤ) (hLU : L ≤ U) (S : ℕ)
    (hS : 2 ≤ S) (hG : NormalizedGowersLaws S) (χ : C(Circle, ℂ))
    (hAbs : Summable fun k : ℤ => ‖fourierCoeff χ k‖)
    (A B : ℝ) (f : ℤ → ℂ) :
    normalizedGowers S L U (fun x => f x * χ ((A*x+B : ℝ) : Circle)) ≤
      (∑' k : ℤ, ‖fourierCoeff χ k‖) * normalizedGowers S L U f := by
  let α (k : ℤ) (x : ℤ) := fourierCoeff χ k * (f x * fourier k ((A*x+B : ℝ) : Circle))
  have hα (k : ℤ) : normalizedGowers S L U (α k) =
      ‖fourierCoeff χ k‖ * normalizedGowers S L U f := by
    simp only [α, fourier_affine_as_phase, normalizedGowers_complex_scale L U S (by omega)]
    rw [normalizedGowers_mul_linear_phase L U S hS]
  have hαsum (x : ℤ) : HasSum (fun k => α k x) (f x * χ ((A*x+B : ℝ) : Circle)) := by
    have hF := has_pointwise_sum_fourier_series_of_summable hAbs.of_norm
      ((A*x+B : ℝ) : Circle)
    simpa [α, smul_eq_mul, mul_left_comm, mul_assoc] using hF.mul_left (f x)
  have hL : Tendsto (fun I : Finset ℤ => normalizedGowers S L U
      (fun x => ∑ i ∈ I, α i x)) atTop
      (𝓝 (normalizedGowers S L U (fun x => f x * χ ((A*x+B : ℝ) : Circle)))) :=
    ((continuous_normalizedGowers L U S).tendsto _).comp
      (tendsto_pi_nhds.mpr fun x => hαsum x)
  have hR := hAbs.hasSum.mul_right (normalizedGowers S L U f)
  refine le_of_tendsto_of_tendsto hL hR ?_
  filter_upwards [] with I
  simpa only [hα] using normalizedGowers_finset_sum_le L U S (by omega) hLU hG I α

/-- Lemma 4.5 for a cutoff with absolutely summable Fourier coefficients.
Here the support condition is expressed on the real fundamental domain. -/
theorem localized_vertical_fourier_multiplier
    (L U : ℤ) (hLU : L ≤ U) (S : ℕ) (hS : 3 ≤ S)
    (hG : NormalizedGowersLaws S) (χ : C(Circle, ℂ))
    (hAbs : Summable fun k : ℤ => ‖fourierCoeff χ k‖)
    (lo hi : ℝ) (hshort : 2*(hi-lo) < 1)
    (hχ : ∀ x : ℝ, x ∈ Set.Ico (0 : ℝ) 1 → χ (x : Circle) ≠ 0 → x ∈ Set.Icc lo hi)
    (α β : ℝ) (a v h : ℤ) (f : ℤ → ℂ) :
    normalizedGowers S L U (fun t =>
      f t * χ ((β*((a+v*t : ℤ) : ℝ) : ℝ) : Circle) *
        phaseExponential ((h : ℝ)*heisenbergPhase α β (a+v*t))) ≤
      (∑' k : ℤ, ‖fourierCoeff χ k‖) * normalizedGowers S L U f := by
  let cutoff (x : ℝ) := if x ∈ Set.Ico (0 : ℝ) 1 then χ (x : Circle) else 0
  have hcut (x : ℝ) (hx : cutoff x ≠ 0) : x ∈ Set.Icc lo hi := by
    by_cases hMem : x ∈ Set.Ico (0 : ℝ) 1
    · exact hχ x hMem (fun hz => hx ((if_pos hMem).trans hz))
    · exact False.elim (hx (if_neg hMem))
  have hfract (x : ℝ) : cutoff (Int.fract x) = χ (x : Circle) := by
    have hmem : Int.fract x ∈ Set.Ico (0 : ℝ) 1 := ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
    change (if Int.fract x ∈ Set.Ico (0 : ℝ) 1 then χ ((Int.fract x : ℝ) : Circle) else 0) = _
    rw [if_pos hmem, AddCircle.coe_fract]
  have hEq := normalizedGowers_localized_vertical S hS L U α β lo hi hshort a v h f cutoff hcut
  simp_rw [hfract] at hEq
  rw [hEq]
  have hAffine (t : ℤ) : β*((a+v*t : ℤ) : ℝ) =
      (β*(v : ℝ))*(t : ℝ)+β*(a : ℝ) := by push_cast; ring
  simp_rw [hAffine]
  exact normalizedGowers_mul_circle_pullback L U hLU S (by omega) hG χ hAbs _ _ f

/-- Bernstein's absolutely convergent Fourier series theorem on the unit
circle, in the Lipschitz case. See Katznelson, An Introduction to Harmonic
Analysis, §I.6.3, taking Hölder exponent one. -/
def BernsteinCircleLipschitzFourier : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ χ : C(Circle, ℂ), ∀ K : ℝ≥0,
    LipschitzWith K χ →
      Summable (fun k : ℤ => ‖fourierCoeff χ k‖) ∧
      (∑' k : ℤ, ‖fourierCoeff χ k‖) ≤ C * (‖χ‖ + (K : ℝ))


/-- Lemma 4.5 from the standard interval Gowers triangle inequality
and Bernstein's theorem for the cutoff's Fourier coefficients. -/
theorem localized_vertical_multiplier_of_bernstein
    (hBernstein : BernsteinCircleLipschitzFourier)
    (L U : ℤ) (hLU : L ≤ U) (S : ℕ) (hS : 3 ≤ S)
    (hG : NormalizedGowersLaws S) (χ : C(Circle, ℂ)) (K : ℝ≥0)
    (hLip : LipschitzWith K χ)
    (lo hi : ℝ) (hshort : 2*(hi-lo) < 1)
    (hχ : ∀ x : ℝ, x ∈ Set.Ico (0 : ℝ) 1 → χ (x : Circle) ≠ 0 → x ∈ Set.Icc lo hi)
    (α β : ℝ) (a v h : ℤ) (f : ℤ → ℂ) :
    normalizedGowers S L U (fun t =>
      f t * χ ((β*((a+v*t : ℤ) : ℝ) : ℝ) : Circle) *
        phaseExponential ((h : ℝ)*heisenbergPhase α β (a+v*t))) ≤
      (∑' k : ℤ, ‖fourierCoeff χ k‖) * normalizedGowers S L U f := by
  obtain ⟨_, _, hb⟩ := hBernstein
  exact localized_vertical_fourier_multiplier L U hLU S hS hG χ (hb χ K hLip).1 lo hi
    hshort hχ α β a v h f

end NilBohr
