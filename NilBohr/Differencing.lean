import NilBohr.LocalPhases

/-! Finite Cauchy–Schwarz and the spatial square identity for Lemma 5.1. -/

open scoped BigOperators
open Polynomial

namespace NilBohr

theorem norm_sum_mul_sq_le {ι : Type*} (I : Finset ι) (v a : ι → ℂ) :
    ‖∑ y ∈ I, v y * a y‖ ^ 2 ≤
      (∑ y ∈ I, ‖v y‖ ^ 2) * ∑ y ∈ I, ‖a y‖ ^ 2 := by
  have hnorm : ‖∑ y ∈ I, v y * a y‖ ≤ ∑ y ∈ I, ‖v y‖ * ‖a y‖ := by
    simpa only [norm_mul] using norm_sum_le I (fun y => v y * a y)
  exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq I (fun y => ‖v y‖) (fun y => ‖a y‖))

theorem norm_sum_mul_sq_le_of_norm_le_one {ι : Type*} (I : Finset ι) (v a : ι → ℂ)
    (hv : ∀ y ∈ I, ‖v y‖ ≤ 1) :
    ‖∑ y ∈ I, v y * a y‖ ^ 2 ≤ (I.card : ℝ) * ∑ y ∈ I, ‖a y‖ ^ 2 := by
  apply (norm_sum_mul_sq_le I v a).trans
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun y _ => sq_nonneg ‖a y‖))
  calc
    (∑ y ∈ I, ‖v y‖ ^ 2) ≤ ∑ _y ∈ I, (1 : ℝ) := by
      exact Finset.sum_le_sum (fun y hy => by nlinarith [hv y hy, norm_nonneg (v y)])
    _ = I.card := by simp

theorem sum_mul_star_eq_norm_sq_sum {ι : Type*} (I : Finset ι) (a : ι → ℂ) :
    (∑ u ∈ I, ∑ x ∈ I, a u * (starRingEnd ℂ) (a x)) =
      ((‖∑ x ∈ I, a x‖ ^ 2 : ℝ) : ℂ) := by
  simp only [← Finset.mul_sum, ← Finset.sum_mul, ← map_sum, Complex.mul_conj,
    Complex.normSq_eq_norm_sq]

def spatialDifferenceSupport (X : Finset ℤ) : Finset ℤ :=
  (X ×ˢ X).image (fun ux => ux.1 - ux.2)

theorem spatial_square_by_difference (X : Finset ℤ) (a : ℤ → ℂ) :
    (∑ h ∈ spatialDifferenceSupport X,
      ∑ ux ∈ (X ×ˢ X).filter (fun ux => ux.1 - ux.2 = h),
       a ux.1 * (starRingEnd ℂ) (a ux.2)) =
      ((‖∑ x ∈ X, a x‖ ^ 2 : ℝ) : ℂ) := by
  unfold spatialDifferenceSupport
  rw [Finset.sum_fiberwise_of_maps_to
    (fun ux hux => Finset.mem_image_of_mem (fun ux : ℤ × ℤ => ux.1 - ux.2) hux)
    (fun ux : ℤ × ℤ => a ux.1 * (starRingEnd ℂ) (a ux.2))]
  rw [Finset.sum_product]
  exact sum_mul_star_eq_norm_sq_sum X a

noncomputable def spatialSlice {k : ℕ} (X : Finset ℤ) (P : Fin k → Polynomial ℤ)
    (f : Fin k → ℤ → ℂ) (y : ℤ) : ℂ :=
  ∑ x ∈ X, ∏ i, f i (x + (P i).eval y)

def spatialMultiplicativeDifference (f : ℤ → ℂ) (h x : ℤ) : ℂ :=
  f (x + h) * (starRingEnd ℂ) (f x)

/-- Pairwise spatial differencing fully expands the square of the unweighted
spatial slice. The pair support records both spatial endpoints. -/
theorem spatial_slice_square_eq_differences {k : ℕ} (X : Finset ℤ)
    (P : Fin k → Polynomial ℤ) (f : Fin k → ℤ → ℂ) (y : ℤ) :
    ((‖spatialSlice X P f y‖ ^ 2 : ℝ) : ℂ) =
      ∑ h ∈ spatialDifferenceSupport X,
      ∑ ux ∈ (X ×ˢ X).filter (fun ux => ux.1 - ux.2 = h),
        ∏ i, spatialMultiplicativeDifference (f i) h (ux.2 + (P i).eval y) := by
  rw [spatialSlice, ← spatial_square_by_difference]
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro ux hux
  have hh := (Finset.mem_filter.mp hux).2
  simp only [map_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  have he : ux.2 + (P i).eval y + h = ux.1 + (P i).eval y := by omega
  rw [spatialMultiplicativeDifference, he]

/-- The first inequality of the proof of Lemma 5.1. The exterior parameter
weight disappears by Cauchy–Schwarz with no additional hypothesis on it. -/
theorem countingForm_sq_le_spatial_energy {k : ℕ} {M N : ℕ} (hM : 0 < M)
    (X : Finset ℤ) (P : Fin k → Polynomial ℤ) (f : Fin k → ℤ → ℂ)
    (v : ℤ → ℂ) (hv : OneBoundedOn (positiveInterval M) v) :
    ‖countingForm N M X P v f‖ ^ 2 ≤
      (∑ y ∈ positiveInterval M, ‖spatialSlice X P f y‖ ^ 2) /
        ((N : ℝ)^2 * M) := by
  have hcard : (positiveInterval M).card = M := by
    rw [positiveInterval, Int.card_Icc]
    simp
  have hc : countingForm N M X P v f =
      (∑ y ∈ positiveInterval M, v y * spatialSlice X P f y) / ((N : ℂ) * M) := by
    unfold countingForm spatialSlice
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [hc, norm_div, norm_mul, Complex.norm_natCast, Complex.norm_natCast, div_pow, mul_pow]
  have h := norm_sum_mul_sq_le_of_norm_le_one (positiveInterval M) v (spatialSlice X P f) hv
  rw [hcard] at h
  apply (div_le_div_of_nonneg_right h (by positivity)).trans
  apply le_of_eq
  rw [show (N : ℝ)^2 * (M : ℝ)^2 = ((N : ℝ)^2 * M) * M by ring,
    mul_comm (M : ℝ)]
  rw [mul_comm ((N : ℝ)^2 * M) (M : ℝ), ← div_div,
    mul_div_cancel_right₀ _ (by positivity : (M : ℝ) ≠ 0)]

end NilBohr
