import NilBohr.Differencing

/-! Dual functions and phase replacements for the local generalized von
Neumann estimate. All counts retain their original normalization. -/

open scoped BigOperators
open Polynomial

namespace NilBohr

noncomputable def countDual {k : ℕ} (M : ℕ) (X : Finset ℤ) (P : Fin k → Polynomial ℤ)
    (v : ℤ → ℂ) (f : Fin k → ℤ → ℂ) (i : Fin k) (z : ℤ) : ℂ :=
  (∑ y ∈ positiveInterval M, if z - (P i).eval y ∈ X then
    v y * ∏ j ∈ Finset.univ.erase i, f j (z - (P i).eval y + (P j).eval y)
    else 0) / (M : ℂ)

theorem countDual_update {k : ℕ} (M : ℕ) (X : Finset ℤ) (P : Fin k → Polynomial ℤ)
    (v : ℤ → ℂ) (f : Fin k → ℤ → ℂ) (i : Fin k) (g : ℤ → ℂ) :
    countDual M X P v (Function.update f i g) i = countDual M X P v f i := by
  funext z
  unfold countDual
  congr 1
  apply Finset.sum_congr rfl
  intro y _
  split_ifs <;> try rfl
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]

theorem countDual_support {k : ℕ} (M : ℕ) (X Z : Finset ℤ) (P : Fin k → Polynomial ℤ)
    (v : ℤ → ℂ) (f : Fin k → ℤ → ℂ) (i : Fin k)
    (hZ : ∀ x ∈ X, ∀ y ∈ positiveInterval M, x + (P i).eval y ∈ Z) :
    SupportedOn Z (countDual M X P v f i) := by
  intro z hz
  unfold countDual
  have hsum : (∑ y ∈ positiveInterval M, if z - (P i).eval y ∈ X then
      v y * ∏ j ∈ Finset.univ.erase i, f j (z - (P i).eval y + (P j).eval y)
      else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro y hy
    apply if_neg
    intro hx
    exact hz (sub_add_cancel z ((P i).eval y) ▸ hZ _ hx y hy)
  simp [hsum]

theorem norm_countDual_le_one {k : ℕ} (M : ℕ) (X : Finset ℤ) (P : Fin k → Polynomial ℤ)
    (v : ℤ → ℂ) (f : Fin k → ℤ → ℂ) (i : Fin k)
    (hv : OneBoundedOn (positiveInterval M) v) (hf : ∀ j z, ‖f j z‖ ≤ 1) :
    ∀ z, ‖countDual M X P v f i z‖ ≤ 1 := by
  intro z
  by_cases hM : M = 0
  · simp [countDual, hM]
  rw [countDual, norm_div, Complex.norm_natCast, div_le_iff₀ (by positivity), one_mul]
  refine (norm_sum_le _ _).trans ?_
  have hcard : (positiveInterval M).card = M := by simp [positiveInterval, Int.card_Icc]
  simpa only [Finset.sum_const, hcard, nsmul_eq_mul, mul_one] using
    (Finset.sum_le_sum (s := positiveInterval M) (g := fun _ => (1 : ℝ))
      (fun y hy => by
        split_ifs
        · rw [norm_mul, norm_prod]
          apply mul_le_one₀ (hv y hy) (by positivity)
          simpa using (Finset.prod_le_prod (s := Finset.univ.erase i)
            (f := fun j => ‖f j (z - (P i).eval y + (P j).eval y)‖)
            (g := fun _ => (1 : ℝ)) (fun _ _ => norm_nonneg _) (fun j _ => hf j _))
        · simp))

private theorem count_slice_reanchor {k : ℕ} (X Z : Finset ℤ)
    (P : Fin k → Polynomial ℤ) (v : ℤ → ℂ) (f : Fin k → ℤ → ℂ)
    (i : Fin k) (y : ℤ) (hZ : ∀ x ∈ X, x + (P i).eval y ∈ Z) :
    (∑ x ∈ X, v y * ∏ j, f j (x + (P j).eval y)) =
      ∑ z ∈ Z, f i z * (if z - (P i).eval y ∈ X then
        v y * ∏ j ∈ Finset.univ.erase i, f j (z - (P i).eval y + (P j).eval y) else 0) := by
  let g := fun z : ℤ => f i z * (if z - (P i).eval y ∈ X then
    v y * ∏ j ∈ Finset.univ.erase i, f j (z - (P i).eval y + (P j).eval y) else 0)
  calc
    _ = ∑ z ∈ Z.filter (fun z => z - (P i).eval y ∈ X), g z := by
      apply Finset.sum_bij (fun x _ => x + (P i).eval y)
      · intro x hx
        exact Finset.mem_filter.mpr ⟨hZ x hx, by simpa⟩
      · intro x _ x' _ hx
        omega
      · intro z hz
        obtain ⟨_, hx⟩ := Finset.mem_filter.mp hz
        refine ⟨z - (P i).eval y, hx, by omega⟩
      · intro x hx
        simp only [g, add_sub_cancel_right, if_pos hx]
        rw [← Finset.mul_prod_erase Finset.univ (fun j => f j (x + (P j).eval y))
          (Finset.mem_univ i)]
        ring
    _ = ∑ z ∈ Z, g z := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro z _ hz
      have : z - (P i).eval y ∉ X := fun hx => hz (Finset.mem_filter.mpr ⟨‹z ∈ Z›, hx⟩)
      simp [g, this]

/-- Exact reanchoring at any input of the count. -/
theorem countingForm_eq_dual {k N M : ℕ} (X Z : Finset ℤ) (P : Fin k → Polynomial ℤ)
    (v : ℤ → ℂ) (f : Fin k → ℤ → ℂ) (i : Fin k)
    (hZ : ∀ x ∈ X, ∀ y ∈ positiveInterval M, x + (P i).eval y ∈ Z) :
    countingForm N M X P v f =
      (∑ z ∈ Z, f i z * countDual M X P v f i z) / (N : ℂ) := by
  simp only [countingForm, countDual, ← mul_div_assoc, ← Finset.sum_div, div_div]
  rw [mul_comm (M : ℂ) (N : ℂ)]
  congr 1
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm (s := X), Finset.sum_comm (s := Z)]
  apply Finset.sum_congr rfl
  intro y hy
  exact count_slice_reanchor X Z P v f i y (fun x hx => hZ x hx y hy)

theorem countingForm_update_eq_dual {k N M : ℕ} (X Z : Finset ℤ) (P : Fin k → Polynomial ℤ)
    (v : ℤ → ℂ) (f : Fin k → ℤ → ℂ) (i : Fin k) (g : ℤ → ℂ)
    (hZ : ∀ x ∈ X, ∀ y ∈ positiveInterval M, x + (P i).eval y ∈ Z) :
    countingForm N M X P v (Function.update f i g) =
      (∑ z ∈ Z, g z * countDual M X P v f i z) / (N : ℂ) := by
  rw [countingForm_eq_dual X Z P v (Function.update f i g) i hZ, countDual_update]
  simp

/-- Replacing a spatial input by the conjugate of its dual yields exactly
the normalized nonnegative mass of that dual. -/
theorem countingForm_update_conj_dual_eq {k N M : ℕ}
    (X Z : Finset ℤ) (P : Fin k → Polynomial ℤ) (v : ℤ → ℂ)
    (f : Fin k → ℤ → ℂ) (i : Fin k)
    (hZ : ∀ x ∈ X, ∀ y ∈ positiveInterval M, x + (P i).eval y ∈ Z) :
    countingForm N M X P v (Function.update f i (fun z => (starRingEnd ℂ) (countDual M X P v f i z))) =
      Complex.ofReal ((∑ z ∈ Z, ‖countDual M X P v f i z‖ ^ 2) / (N : ℝ)) := by
  rw [countingForm_update_eq_dual X Z P v f i _ hZ, Complex.ofReal_div, Complex.ofReal_natCast,
    Complex.ofReal_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro z _
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- The dual replacement costs at most a square and the fixed spatial-size
constant. No inverse correlation is used to gain the lower bound. -/
theorem countingForm_update_conj_dual_lower {k N M : ℕ} (hN : 0 < N)
    (X Z : Finset ℤ) (P : Fin k → Polynomial ℤ) (v : ℤ → ℂ)
    (f : Fin k → ℤ → ℂ) (i : Fin k)
    (hZ : ∀ x ∈ X, ∀ y ∈ positiveInterval M, x + (P i).eval y ∈ Z)
    (hunit : ∀ z ∈ Z, ‖f i z‖ ≤ 1) {K : ℝ} (hK : 0 < K)
    (hsize : (Z.card : ℝ) ≤ K * N) :
    ‖countingForm N M X P v f‖ ^ 2 / K ≤
      ‖countingForm N M X P v (Function.update f i (fun z => (starRingEnd ℂ) (countDual M X P v f i z)))‖ := by
  let D := countDual M X P v f i
  have h := norm_sum_mul_sq_le_of_norm_le_one Z (f i) D hunit
  have hS : 0 ≤ ∑ z ∈ Z, ‖D z‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  rw [countingForm_eq_dual X Z P v f i hZ, countingForm_update_conj_dual_eq X Z P v f i hZ,
    norm_div, Complex.norm_natCast, div_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg hS (by positivity))]
  change (‖∑ z ∈ Z, f i z * D z‖ ^ 2 / (N : ℝ)^2) / K ≤ (∑ z ∈ Z, ‖D z‖ ^ 2) / (N : ℝ)
  have h' := h.trans (mul_le_mul_of_nonneg_right hsize hS)
  rw [div_div]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  linear_combination (N : ℝ) * h'

/-- A local inverse correlation with the conjugate dual is precisely a count
with the new conjugated phase input. -/
theorem norm_countingForm_replace_phase {k N M : ℕ}
    (X Z : Finset ℤ) (P : Fin k → Polynomial ℤ) (v : ℤ → ℂ)
    (f : Fin k → ℤ → ℂ) (i : Fin k) (ψ : ℤ → ℂ)
    (hZ : ∀ x ∈ X, ∀ y ∈ positiveInterval M, x + (P i).eval y ∈ Z) :
    ‖countingForm N M X P v (Function.update f i (fun z => (starRingEnd ℂ) (ψ z)))‖ =
      ‖∑ z ∈ Z, (starRingEnd ℂ) (countDual M X P v f i z) * ψ z‖ / (N : ℝ) := by
  rw [countingForm_update_eq_dual X Z P v f i _ hZ, norm_div, Complex.norm_natCast]
  congr 1
  conv_rhs => rw [← Complex.norm_conj]
  simp only [map_sum, map_mul, Complex.conj_conj, mul_comm]

end NilBohr
