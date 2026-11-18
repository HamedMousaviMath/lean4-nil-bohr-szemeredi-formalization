import NilBohr.GowersDilation
import NilBohr.GowersOrderComparison
import NilBohr.BareSelectorComparison

/-! Interval Gowers estimates transferred to finite arithmetic progressions. -/

open Polynomial
open scoped BigOperators

namespace NilBohr

/-- The zero-extended Gowers norm on a finite set, normalized by its indicator.
The finite cube sum uses the smallest closed interval containing the set. -/
noncomputable def progressionGowers (S : ℕ) (P : Finset ℤ) (f : ℤ → ℂ) : ℝ :=
  if hP : P.Nonempty then
    (gowersCubePower S (P.min' hP) (P.max' hP)
      (fun x => if x ∈ P then f x else 0)).re ^ ((2 : ℝ)^S)⁻¹ /
    (gowersCubePower S (P.min' hP) (P.max' hP)
      (fun x => if x ∈ P then 1 else 0)).re ^ ((2 : ℝ)^S)⁻¹
  else 0

/-- In the ratio defining the normalized Gowers norm on a progression,
affine reindexing transports both cube sums exactly. -/
theorem progressionGowers_eq_interval (S M q : ℕ) (hM : 0 < M) (hq : 0 < q)
    (b : ℤ) (f : ℤ → ℂ) :
    progressionGowers S ((positiveInterval M).image (fun n => b+(q:ℤ)*n)) f =
      normalizedGowers S 1 (M : ℤ) (fun n => f (b+(q:ℤ)*n)) := by
  let P := (positiveInterval M).image (fun n => b+(q:ℤ)*n)
  have hMZ : (1 : ℤ) ≤ (M : ℤ) := by exact_mod_cast hM
  have hP : P.Nonempty := ⟨b+(q:ℤ)*1, Finset.mem_image.mpr
    ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hMZ⟩, rfl⟩⟩
  have hqZ : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq
  have hImg (n : ℤ) (hn : n ∈ Finset.Icc (1 : ℤ) (M : ℤ)) :
      (q : ℤ)*n+b ∈ Finset.Icc (P.min' hP) (P.max' hP) := by
    have hx : (q : ℤ)*n+b ∈ P :=
      Finset.mem_image.mpr ⟨n, hn, add_comm _ _⟩
    exact Finset.mem_Icc.mpr ⟨P.min'_le _ hx, P.le_max' _ hx⟩
  have hHull : P.min' hP ≤ P.max' hP :=
    (Finset.mem_Icc.mp (hImg 1 (Finset.mem_Icc.mpr ⟨le_rfl, hMZ⟩))).1.trans
      (Finset.mem_Icc.mp (hImg 1 (Finset.mem_Icc.mpr ⟨le_rfl, hMZ⟩))).2
  have hcut (g : ℤ → ℂ) :
      (fun x => if x ∈ P then g x else 0) =
        affineIntervalRestriction b (q : ℤ) 1 (M : ℤ) g := by
    classical
    funext x
    have heq : x ∈ P ↔ ∃ n ∈ Finset.Icc (1 : ℤ) (M : ℤ), x = (q : ℤ)*n+b := by
      simp only [P, Finset.mem_image, positiveInterval]
      simp only [eq_comm, add_comm]
    simp only [affineIntervalRestriction, heq]
  change progressionGowers S P f = _
  unfold progressionGowers normalizedGowers
  rw [dif_pos hP, hcut f, hcut (fun _ => 1),
    gowersCubePower_affine_interval S b hqZ hMZ hHull hImg f,
    gowersCubePower_affine_interval S b hqZ hMZ hHull hImg (fun _ => 1)]
  simp only [add_comm b]

/-- At order one the normalized Gowers norm is the absolute value
of the average on the progression. -/
theorem progressionGowers_one_eq_norm_mean (M q : ℕ) (hM : 0 < M) (hq : 0 < q)
    (b : ℤ) (f : ℤ → ℂ) :
    let P := (positiveInterval M).image (fun n => b+(q:ℤ)*n)
    progressionGowers 1 P f = ‖(∑ x ∈ P, f x) / (P.card : ℂ)‖ := by
  classical
  dsimp only
  rw [progressionGowers_eq_interval 1 M q hM hq b f, normalizedGowers_one_eq_norm_mean M hM]
  have hqZ : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
  have hinj : Function.Injective (fun n : ℤ => b+(q:ℤ)*n) :=
    fun _ _ h => mul_left_cancel₀ hqZ (add_left_cancel h)
  rw [Finset.card_image_of_injective _ hinj, card_positiveInterval,
    Finset.sum_image (fun _ _ _ _ h => hinj h)]

/-- Repeated adjacent-order comparison, uniform over all interval lengths. -/
theorem normalizedGowers_le_of_le {r s : ℕ} (hr : 1 ≤ r) (hrs : r ≤ s) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 0 < M → ∀ f : ℤ → ℂ,
      normalizedGowers r 1 (M : ℤ) f ≤ C * normalizedGowers s 1 (M : ℤ) f := by
  induction s, hrs using Nat.le_induction with
  | base =>
    exact ⟨1, one_pos, by simp⟩
  | succ k hrk ih =>
    obtain ⟨A, hA, hA_bound⟩ := ih
    obtain ⟨B, hB, hB_bound⟩ := normalizedGowersAdjacentMonotonicity k (hr.trans hrk)
    refine ⟨A*B, mul_pos hA hB, fun M hM f => (hA_bound M hM f).trans ?_⟩
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hB_bound M hM f) hA.le

/-- Normalized Gowers monotonicity on all nonempty finite arithmetic
progressions, with a constant depending only on the two orders. -/
theorem progressionGowers_le_of_le {r s : ℕ} (hr : 1 ≤ r) (hrs : r ≤ s) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M q : ℕ), 0 < M → 0 < q → ∀ b : ℤ, ∀ f : ℤ → ℂ,
      progressionGowers r ((positiveInterval M).image (fun n => b+(q:ℤ)*n)) f ≤
        C * progressionGowers s ((positiveInterval M).image (fun n => b+(q:ℤ)*n)) f := by
  obtain ⟨C, hC, hB⟩ := normalizedGowers_le_of_le hr hrs
  refine ⟨C, hC, fun M q hM hq b f => ?_⟩
  rw [progressionGowers_eq_interval r M q hM hq b f, progressionGowers_eq_interval s M q hM hq b f]
  exact hB M hM _

/-- The phase supremum on the positive interval is bounded by the
normalized Gowers norm at the same order. -/
theorem phaseNorm_positiveInterval_le_gowers {S : ℕ} (hS : 1 ≤ S) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 0 < M → ∀ f : ℤ → ℂ,
      phaseNorm S (positiveInterval M) f ≤ C * normalizedGowers S 1 (M : ℤ) f := by
  obtain ⟨C, hC, hmean⟩ :=
    normalizedGowers_meanBound_of_adjacent normalizedGowersAdjacentMonotonicity S hS
  refine ⟨C, hC, fun M hM f => ?_⟩
  unfold phaseNorm
  refine csSup_le ⟨‖phaseAverage (positiveInterval M) f 0‖, 0, by simpa using hS, rfl⟩ ?_
  rintro _ ⟨φ, hφ, rfl⟩
  have hdeg : (-φ).natDegree < S := by simpa only [natDegree_neg] using hφ
  have h := hmean M hM (fun n => f n * phaseExponential ((-φ).eval (n : ℝ)))
  rw [normalizedGowers_mul_polynomial_phase 1 (M : ℤ) S (-φ) hdeg f] at h
  simpa only [phaseAverage, card_positiveInterval, eval_neg, phase, phaseExponential] using h

/-- The ordinary phase seminorm is bounded by the project’s normalized
Gowers norm on every nonempty finite arithmetic progression. This is
the manuscript’s inequality `e:u-below-U`. -/
theorem phaseNorm_le_progressionGowers {S : ℕ} (hS : 1 ≤ S) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M q : ℕ), 0 < M → 0 < q → ∀ b : ℤ, ∀ f : ℤ → ℂ,
      phaseNorm S ((positiveInterval M).image (fun n => b+(q:ℤ)*n)) f ≤
        C * progressionGowers S ((positiveInterval M).image (fun n => b+(q:ℤ)*n)) f := by
  obtain ⟨C, hC, hB⟩ := phaseNorm_positiveInterval_le_gowers hS
  refine ⟨C, hC, fun M q hM hq b f => ?_⟩
  rw [progressionGowers_eq_interval S M q hM hq b f]
  exact (phaseNorm_le_affine_pullback (by omega) hq b f).trans (hB M hM _)

/-- The manuscript's actual interval/residue presentation of the tested
progressions obeys the same order-uniform bound. -/
theorem phaseNorm_localProgression_le_gowers {S : ℕ} (hS : 1 ≤ S) :
    ∃ C : ℝ, 0 < C ∧ ∀ (l r u : ℤ) (q : ℕ), 0 < q →
      (localProgression l r u q).Nonempty → ∀ f : ℤ → ℂ,
      phaseNorm S (localProgression l r u q) f ≤ C * progressionGowers S (localProgression l r u q) f := by
  obtain ⟨C, hC, hB⟩ := phaseNorm_le_progressionGowers hS
  refine ⟨C, hC, fun l r u q hq hP f => ?_⟩
  obtain ⟨b, _, h⟩ := localProgression_as_affine hq hP
  conv_lhs => rw [h]
  conv_rhs => rw [h]
  exact hB _ q (Finset.card_pos.mpr hP) hq b f

end NilBohr
