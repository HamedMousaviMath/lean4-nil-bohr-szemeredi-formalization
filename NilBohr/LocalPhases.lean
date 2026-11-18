import NilBohr.Counting

/-! Exact reduction from spatial linear phases to polynomial-phase tests. -/

open scoped BigOperators
open Polynomial

namespace NilBohr

theorem phase_add (a b : ℝ) : phase (a + b) = phase a * phase b := by
  rw [phase, phase, phase, Complex.ofReal_add, mul_add, Complex.exp_add]

@[simp] theorem phase_zero : phase 0 = 1 := by simp [phase]

@[simp] theorem norm_phase (a : ℝ) : ‖phase a‖ = 1 := by
  rw [phase, Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im]

noncomputable def localTestPolynomial {ι : Type*} [Fintype ι]
    (P : ι → Polynomial ℤ) (x : ℤ) (θ γ : ι → ℝ) : Polynomial ℝ :=
  ∑ i, (C (θ i) * (C (x : ℝ) + (P i).map (Int.castRingHom ℝ)) + C (γ i))

theorem localTestPolynomial_degree {ι : Type*} [Fintype ι]
    (P : ι → Polynomial ℤ) (d : ℕ) (hP : ∀ i, (P i).natDegree ≤ d)
    (x : ℤ) (θ γ : ι → ℝ) :
    (localTestPolynomial P x θ γ).natDegree ≤ d := by
  unfold localTestPolynomial
  apply natDegree_sum_le_of_forall_le
  intro i _
  apply (natDegree_add_le _ _).trans
  apply max_le
  · apply (natDegree_C_mul_le _ _).trans
    apply (natDegree_add_le _ _).trans
    exact max_le (by simp) (natDegree_map_le.trans (hP i))
  · simp

theorem localTestPolynomial_eval {ι : Type*} [Fintype ι]
    (P : ι → Polynomial ℤ) (x y : ℤ) (θ γ : ι → ℝ) :
    (localTestPolynomial P x θ γ).eval (y : ℝ) =
      ∑ i, (θ i * ((x + (P i).eval y : ℤ) : ℝ) + γ i) := by
  rw [localTestPolynomial, eval_finset_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [eval_add, eval_mul, eval_C, Int.cast_add]
  rw [eval_intCast_map]
  rfl

theorem phase_sum {ι : Type*} (I : Finset ι) (f : ι → ℝ) :
    phase (∑ i ∈ I, f i) = ∏ i ∈ I, phase (f i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | insert a I ha ih => simp [Finset.sum_insert ha, Finset.prod_insert ha, phase_add, ih]

theorem product_local_linear_phases {ι : Type*} [Fintype ι]
    (P : ι → Polynomial ℤ) (x y : ℤ) (θ γ : ι → ℝ) :
    (∏ i, phase (θ i * ((x + (P i).eval y : ℤ) : ℝ) + γ i)) =
      phase ((localTestPolynomial P x θ γ).eval (y : ℝ)) := by
  rw [localTestPolynomial_eval, phase_sum]

theorem norm_phaseAverage_le {I : Finset ℤ} (v : ℤ → ℂ) (Q : Polynomial ℝ) :
    ‖phaseAverage I v Q‖ ≤ (∑ y ∈ I, ‖v y‖) / (I.card : ℝ) := by
  rw [phaseAverage, norm_div]
  have hn : ‖(I.card : ℂ)‖ = (I.card : ℝ) := by simp
  rw [hn]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact (norm_sum_le _ _).trans_eq (by simp [norm_mul])

theorem norm_phaseAverage_le_phaseNorm {I : Finset ℤ} (v : ℤ → ℂ) (Q : Polynomial ℝ)
    {s : ℕ} (hQ : Q.natDegree < s) : ‖phaseAverage I v Q‖ ≤ phaseNorm s I v := by
  apply le_csSup
  · refine ⟨(∑ y ∈ I, ‖v y‖) / (I.card : ℝ), ?_⟩
    rintro _ ⟨P, _, rfl⟩
    exact norm_phaseAverage_le v P
  · exact ⟨Q, hQ, rfl⟩

/-- On a parameter cell on which every shifted argument sees one fixed linear
phase, the weighted average is one of the polynomial tests in Theorem 4.2. -/
theorem norm_local_phase_product_average_le {ι : Type*} [Fintype ι]
    (P : ι → Polynomial ℤ) (d : ℕ) (hP : ∀ i, (P i).natDegree ≤ d)
    (x : ℤ) (I : Finset ℤ) (v : ℤ → ℂ) (ψ : ι → ℤ → ℂ)
    (θ γ : ι → ℝ)
    (hψ : ∀ y ∈ I, ∀ i, ψ i (x + (P i).eval y) =
      phase (θ i * ((x + (P i).eval y : ℤ) : ℝ) + γ i)) :
    ‖(∑ y ∈ I, v y * ∏ i, ψ i (x + (P i).eval y)) / (I.card : ℂ)‖ ≤
      phaseNorm (d + 1) I v := by
  let Q := localTestPolynomial P x θ γ
  have hQ : (-Q).natDegree < d + 1 := by
    simpa [Q] using Nat.lt_succ_of_le (localTestPolynomial_degree P d hP x θ γ)
  convert norm_phaseAverage_le_phaseNorm v (-Q) hQ using 2
  unfold phaseAverage
  congr 1
  apply Finset.sum_congr rfl
  intro y hy
  simp_rw [hψ y hy, product_local_linear_phases]
  simp [Q]

end NilBohr
