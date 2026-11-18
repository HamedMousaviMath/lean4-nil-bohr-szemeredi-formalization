import NilBohr.Definitions

/-! Algebraic reductions for the smooth-modulus comparison. -/

open scoped BigOperators
open Polynomial

namespace NilBohr

theorem countingForm_add_weight {k : ℕ} (N M : ℕ) (X : Finset ℤ)
    (P : Fin k → Polynomial ℤ) (v w : ℤ → ℂ) (f : Fin k → ℤ → ℂ) :
    countingForm N M X P (fun y => v y + w y) f =
      countingForm N M X P v f + countingForm N M X P w f := by
  simp only [countingForm, add_mul, Finset.sum_add_distrib, add_div]

theorem countingForm_mul_weight {k : ℕ} (N M : ℕ) (X : Finset ℤ)
    (P : Fin k → Polynomial ℤ) (v : ℤ → ℂ) (c : ℂ) (f : Fin k → ℤ → ℂ) :
    countingForm N M X P (fun y => c * v y) f = c * countingForm N M X P v f := by
  unfold countingForm
  simp only [mul_assoc, ← Finset.mul_sum, mul_div_assoc]

theorem countingForm_mono_window {k : ℕ} (N M : ℕ) {X X' : Finset ℤ}
    (hXX' : X ⊆ X') (P : Fin (k + 1) → Polynomial ℤ) (hP : P 0 = 0)
    (v : ℤ → ℂ) (f : Fin (k + 1) → ℤ → ℂ) (hf : SupportedOn X (f 0)) :
    countingForm N M X P v f = countingForm N M X' P v f := by
  unfold countingForm
  congr 1
  apply Finset.sum_subset hXX'
  intro x _ hx
  apply Finset.sum_eq_zero
  intro y _
  have hzero : f 0 (x + (P 0).eval y) = 0 := by simpa [hP] using hf x hx
  rw [Finset.prod_eq_zero (Finset.mem_univ (0 : Fin (k + 1))) hzero, mul_zero]

theorem oneBounded_of_supported {I : Finset ℤ} {f : ℤ → ℂ}
    (hI : OneBoundedOn I f) (hs : SupportedOn I f) (x : ℤ) : ‖f x‖ ≤ 1 := by
  by_cases hx : x ∈ I
  · exact hI x hx
  · simp [hs x hx]

/-- The exact split in Theorem 3.2, with uniformity left to the estimates for the
two summands. The weights can be complex and arbitrarily large. -/
theorem selector_count_split {k : ℕ} (N M : ℕ) (X : Finset ℤ)
    (P : Fin k → Polynomial ℤ) (lam Fq : ℤ → ℂ) (μ : ℂ) (f : Fin k → ℤ → ℂ) :
    countingForm N M X P (fun y => lam y * Fq y) f -
      μ * countingForm N M X P (fun _ => 1) f =
    countingForm N M X P (fun y => (lam y - 1) * Fq y) f +
      countingForm N M X P (fun y => Fq y - μ) f := by
  have hweight : (fun y => lam y * Fq y) =
      (fun y => (lam y - 1) * Fq y + ((Fq y - μ) + μ * 1)) := by
    funext y
    ring
  rw [hweight, countingForm_add_weight, countingForm_add_weight, countingForm_mul_weight]
  abel

theorem norm_selector_count_sub_le {k : ℕ} (N M : ℕ) (X : Finset ℤ)
    (P : Fin k → Polynomial ℤ) (lam Fq : ℤ → ℂ) (μ : ℂ) (f : Fin k → ℤ → ℂ) :
    ‖countingForm N M X P (fun y => lam y * Fq y) f -
      μ * countingForm N M X P (fun _ => 1) f‖ ≤
    ‖countingForm N M X P (fun y => (lam y - 1) * Fq y) f‖ +
      ‖countingForm N M X P (fun y => Fq y - μ) f‖ := by
  rw [selector_count_split]
  exact norm_add_le _ _

/-- A weighted finite average is dominated by the corresponding scalar average
of a nonnegative upper weight. The denominator is totalized at zero. -/
theorem norm_weighted_sum_div_le {ι : Type*} (I : Finset ι) (a : ι → ℂ)
    (v g : ι → ℝ) (D B : ℝ)
    (hD : 0 ≤ D) (_hB : 0 ≤ B)
    (hv : ∀ i ∈ I, |v i| ≤ g i) (ha : ∀ i ∈ I, ‖a i‖ ≤ B) :
    ‖(∑ i ∈ I, (v i : ℂ) * a i) / (D : ℂ)‖ ≤
      B * ((∑ i ∈ I, g i) / D) := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hD, ← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ hD
  calc
    ‖∑ i ∈ I, (v i : ℂ) * a i‖ ≤ ∑ i ∈ I, ‖(v i : ℂ) * a i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ I, B * g i := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm B]
      exact mul_le_mul (hv i hi) (ha i hi) (norm_nonneg _) ((abs_nonneg _).trans (hv i hi))
    _ = B * ∑ i ∈ I, g i := by rw [Finset.mul_sum]

end NilBohr
