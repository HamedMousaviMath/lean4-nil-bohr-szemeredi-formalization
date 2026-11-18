import NilBohr.Differencing

/-! The finite energy pigeonhole and support translation in Lemma 5.1. -/

open scoped BigOperators
open Polynomial

namespace NilBohr

private theorem diff_tuple_product {k : ℕ} (P : Fin (k + 1) → Polynomial ℤ)
    (hP : P 0 = 0) (f : Fin (k + 1) → ℤ → ℂ) (X : Finset ℤ)
    (h₀ : SupportedOn X (f 0)) (h x y : ℤ) (hx : x + h ∉ X) :
    (∏ i, spatialMultiplicativeDifference (f i) h (x + (P i).eval y)) = 0 := by
  apply Finset.prod_eq_zero (Finset.mem_univ 0)
  simp [spatialMultiplicativeDifference, hP, h₀ _ hx]

private theorem spatial_pair_fiber_sum {k : ℕ} (P : Fin (k + 1) → Polynomial ℤ)
    (hP : P 0 = 0) (f : Fin (k + 1) → ℤ → ℂ) (X : Finset ℤ)
    (h₀ : SupportedOn X (f 0)) (h y : ℤ) :
    (∑ ux ∈ (X ×ˢ X).filter (fun ux => ux.1 - ux.2 = h),
      ∏ i, spatialMultiplicativeDifference (f i) h (ux.2 + (P i).eval y)) =
     ∑ x ∈ X, ∏ i, spatialMultiplicativeDifference (f i) h (x + (P i).eval y) := by
  let A := fun x : ℤ => ∏ i, spatialMultiplicativeDifference (f i) h
    (x + (P i).eval y)
  calc
    _ = ∑ x ∈ X.filter (fun x => x + h ∈ X), A x := by
      apply Finset.sum_bij (fun ux _ => ux.2)
      · intro ux hux
        obtain ⟨hmem, hdiff⟩ := Finset.mem_filter.mp hux
        obtain ⟨h₁,h₂⟩ := Finset.mem_product.mp hmem
        exact Finset.mem_filter.mpr ⟨h₂, (show ux.2 + h = ux.1 by omega) ▸ h₁⟩
      · intro ux hu vx hv he
        obtain ⟨_, hd₁⟩ := Finset.mem_filter.mp hu
        obtain ⟨_, hd₂⟩ := Finset.mem_filter.mp hv
        exact Prod.ext (by omega) he
      · intro x hx
        obtain ⟨h₁,h₂⟩ := Finset.mem_filter.mp hx
        exact ⟨(x+h,x), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h₂,h₁⟩,
          by simp⟩, rfl⟩
      · intros
        rfl
    _ = ∑ x ∈ X, A x := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro x hx hnot
      exact diff_tuple_product P hP f X h₀ h x y
        (fun hbad => hnot (Finset.mem_filter.mpr ⟨hx,hbad⟩))

/-- The sum of unweighted differenced counts is the normalized spatial energy.
The anchor support is used to remove the extra fiber restriction on the first
endpoint of the pair. -/
theorem sum_differenced_counts_eq_energy {k N M : ℕ} (X : Finset ℤ)
    (P : Fin (k + 1) → Polynomial ℤ) (hP : P 0 = 0)
    (f : Fin (k + 1) → ℤ → ℂ) (h₀ : SupportedOn X (f 0)) :
    (∑ h ∈ spatialDifferenceSupport X,
       countingForm N M X P (fun _ => 1) (fun i => spatialMultiplicativeDifference (f i) h)) =
      Complex.ofReal (∑ y ∈ positiveInterval M, ‖spatialSlice X P f y‖ ^ 2) /
        ((N : ℂ) * (M : ℂ)) := by
  simp only [countingForm, one_mul, ← Finset.sum_div]
  congr 1
  conv_lhs =>
    arg 2
    ext h
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  push_cast
  apply Finset.sum_congr rfl
  intro y _
  rw [← Complex.ofReal_pow, spatial_slice_square_eq_differences]
  apply Finset.sum_congr rfl
  intro h _
  exact (spatial_pair_fiber_sum P hP f X h₀ h y).symm

/-- Norm bound on a normalized count with arbitrary finite spatial window. -/
theorem norm_countingForm_le_window {k N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (X : Finset ℤ) (P : Fin k → Polynomial ℤ) (v : ℤ → ℂ)
    (f : Fin k → ℤ → ℂ) (hv : OneBoundedOn (positiveInterval M) v)
    (hf : ∀ i x, ‖f i x‖ ≤ 1) :
    ‖countingForm N M X P v f‖ ≤ (X.card : ℝ) / N := by
  have hcard : (positiveInterval M).card = M := by simp [positiveInterval, Int.card_Icc]
  rw [countingForm, norm_div, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
  calc
    _ ≤ ((X.card : ℝ) * M) / ((N : ℝ) * M) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply (norm_sum_le _ _).trans
      have hh : ∀ x ∈ X, ‖∑ y ∈ positiveInterval M, v y * ∏ i, f i (x + (P i).eval y)‖ ≤ M := by
        intro x _
        apply (norm_sum_le _ _).trans
        simpa only [Finset.sum_const, hcard, nsmul_eq_mul, mul_one] using
          (Finset.sum_le_sum (s := positiveInterval M) (g := fun _ => (1 : ℝ))
            (fun y hy => by
              rw [norm_mul, norm_prod]
              apply mul_le_one₀ (hv y hy) (by positivity)
              simpa using (Finset.prod_le_prod (s := Finset.univ)
                (f := fun i => ‖f i (x + (P i).eval y)‖) (g := fun _ => (1 : ℝ))
                (fun i _ => norm_nonneg _) (fun i _ => hf i _))))
      simpa only [Finset.sum_const,nsmul_eq_mul] using Finset.sum_le_sum hh
    _ = _ := by
      rw [mul_comm ((X.card : ℝ)) (M : ℝ), mul_comm (N : ℝ) (M : ℝ),
        ← div_div, mul_div_cancel_left₀ _ (by positivity : (M : ℝ) ≠ 0)]

/-- Pigeonhole bound with an explicit cutoff, valid even for empty sets. -/
theorem finite_threshold_bound {ι : Type*} (I : Finset ι) (g : ι → ℝ)
    {U τ : ℝ} (hτ : 0 ≤ τ) (hg : ∀ h ∈ I, g h ≤ U) :
    ∑ h ∈ I, g h ≤
      (((I.filter (fun h => τ ≤ g h)).card : ℕ) : ℝ) * U + (I.card : ℝ) * τ := by
  classical
  let J := I.filter (fun h => τ ≤ g h)
  have hJ : J ⊆ I := Finset.filter_subset _ _
  have hbad : ∑ h ∈ I \ J, g h ≤ (I.card : ℝ) * τ := by
    calc
      _ ≤ ∑ h ∈ I \ J, τ := by
        apply Finset.sum_le_sum
        intro h hh
        obtain ⟨hi,hj⟩ := Finset.mem_sdiff.mp hh
        exact (lt_of_not_ge (fun ht => hj (Finset.mem_filter.mpr ⟨hi,ht⟩))).le
      _ ≤ _ := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr
          (Finset.card_le_card Finset.sdiff_subset)) hτ
  have hgood : ∑ h ∈ J, g h ≤ (J.card : ℝ) * U := by
    simpa only [Finset.sum_const, nsmul_eq_mul] using
      Finset.sum_le_sum (s := J) (g := fun _ => U) (fun h hh => hg h (hJ hh))
  rw [← Finset.sum_sdiff hJ]
  exact (add_le_add hbad hgood).trans_eq (add_comm _ _)

/-- A large weighted count produces many differences with large unweighted
counts. The explicit support budgets can be instantiated with the manuscript's
spatial interval bounds, uniformly for every bounded parameter weight. -/
theorem compare_large_weighted_to_differenced {k N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (X : Finset ℤ) (P : Fin (k + 1) → Polynomial ℤ) (hP : P 0 = 0)
    (f : Fin (k + 1) → ℤ → ℂ) (h₀ : SupportedOn X (f 0))
    (hf : ∀ i x, ‖f i x‖ ≤ 1) (v : ℤ → ℂ) (hv : OneBoundedOn (positiveInterval M) v)
    {δ K : ℝ} (hδ : 0 < δ) (hK : 0 < K)
    (hD : ((spatialDifferenceSupport X).card : ℝ) ≤ K * N)
    (hX : (X.card : ℝ) ≤ K * N)
    (hlarge : δ ≤ ‖countingForm N M X P v f‖) :
    ∃ Y : Finset ℤ, Y ⊆ spatialDifferenceSupport X ∧
      δ^2 * N / (2*K) ≤ (Y.card : ℝ) ∧
      ∀ h ∈ Y, δ^2 / (2*K) ≤
        ‖countingForm N M X P (fun _ => 1) (fun i => spatialMultiplicativeDifference (f i) h)‖ := by
  classical
  let T (h : ℤ) := countingForm N M X P (fun _ => 1)
    (fun i => spatialMultiplicativeDifference (f i) h)
  let I := spatialDifferenceSupport X
  let τ := δ^2 / (2*K)
  let Y := I.filter (fun h => τ ≤ ‖T h‖)
  have hτ : 0 ≤ τ := by positivity
  refine ⟨Y, Finset.filter_subset _ _, ?_, fun h hh => (Finset.mem_filter.mp hh).2⟩
  have hE := (pow_le_pow_left₀ hδ.le hlarge 2).trans
    (countingForm_sq_le_spatial_energy hM X P f v hv)
  have he0 : 0 ≤ (∑ y ∈ positiveInterval M, ‖spatialSlice X P f y‖ ^ 2 : ℝ) :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have he : δ^2 * (N : ℝ) ≤ ‖∑ h ∈ I, T h‖ := by
    change δ^2 * (N : ℝ) ≤ ‖∑ h ∈ spatialDifferenceSupport X, T h‖
    rw [show (∑ h ∈ spatialDifferenceSupport X, T h) = _ from
      sum_differenced_counts_eq_energy X P hP f h₀,
      norm_div, norm_mul, Complex.norm_natCast, Complex.norm_natCast, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg he0]
    apply (le_div_iff₀ (by positivity)).mpr
    convert (le_div_iff₀ (by positivity)).mp hE using 1
    ring
  have hU (h : ℤ) : ‖T h‖ ≤ K := by
    refine (norm_countingForm_le_window hN hM X P (fun _ => 1) _ (by intro y hy; simp)
      (fun i x => ?_)).trans ((div_le_iff₀ (by positivity : 0 < (N : ℝ))).mpr hX)
    rw [spatialMultiplicativeDifference, norm_mul, Complex.norm_conj]
    exact mul_le_one₀ (hf i _) (norm_nonneg _) (hf i _)
  have hT := ((he.trans (norm_sum_le I T)).trans (finite_threshold_bound I
    (fun h => ‖T h‖) hτ (fun h _ => hU h)))
  have hh : (I.card : ℝ) * τ ≤ δ^2 * (N : ℝ) / 2 := by
    refine (mul_le_mul_of_nonneg_right hD hτ).trans_eq ?_
    dsimp [τ]
    field_simp
    ring
  change δ^2 * N ≤ (Y.card : ℝ) * K + (I.card : ℝ) * τ at hT
  rw [div_le_iff₀ (by positivity)]
  linarith

/-- Moving a common spatial support window by an integer preserves the count
at the same normalization and leaves all polynomial shifts unchanged. -/
theorem countingForm_translate_window {k : ℕ} (N M : ℕ)
    (X : Finset ℤ) (P : Fin k → Polynomial ℤ) (v : ℤ → ℂ)
    (f : Fin k → ℤ → ℂ) (a : ℤ) :
    countingForm N M (X.image (fun x => x - a)) P v (fun i z => f i (z + a)) =
      countingForm N M X P v f := by
  rw [countingForm,countingForm,Finset.sum_image (by intro x _ y _ hh; omega)]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  simp [sub_add_eq_add_sub]

end NilBohr
