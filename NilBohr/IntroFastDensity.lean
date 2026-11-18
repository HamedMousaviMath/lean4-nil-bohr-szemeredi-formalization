import Mathlib

/-! Exact growth of the scales used by the very-fast-approximation
counterexample in the introduction. -/

open Filter
open scoped Topology

namespace NilBohr

/-- The spatial scale chosen for a denominator and its index. -/
noncomputable def fastApproximationScale (r j : ℕ) : ℕ :=
  ⌊Real.exp ((r : ℝ)^j/6)⌋₊

private theorem tendsto_fastExponent (r : ℕ → ℕ) (hr : ∀ j, 2 ≤ r j) :
    Tendsto (fun j => (r j : ℝ)^j/6) atTop atTop := by
  have h := (tendsto_pow_atTop_atTop_of_one_lt (show (1 : ℝ)<2 by norm_num)).const_mul_atTop
    (show (0 : ℝ)<1/6 by norm_num)
  apply tendsto_atTop_mono' atTop ?_ h
  apply Eventually.of_forall
  intro j
  have hr' : (2 : ℝ) ≤ r j := by exact_mod_cast hr j
  have hj := pow_le_pow_left₀ (by norm_num : (0 : ℝ)≤2) hr' j
  change (1/6 : ℝ)*2^j ≤ (r j : ℝ)^j/6
  linarith only [hj]

/-- The floored exponential scales are unbounded. -/
theorem tendsto_fastApproximationScale (r : ℕ → ℕ) (hr : ∀ j, 2 ≤ r j) :
    Tendsto (fun j => fastApproximationScale (r j) j) atTop atTop :=
  tendsto_nat_floor_atTop.comp (Real.tendsto_exp_atTop.comp (tendsto_fastExponent r hr))

/-- A nondecreasing sequence of denominators at least two gives
nondecreasing floored scales. -/
theorem monotone_fastApproximationScale {r : ℕ → ℕ} (hr : Monotone r)
    (hr₂ : ∀ j, 2 ≤ r j) :
    Monotone (fun j => fastApproximationScale (r j) j) := by
  intro i j hij
  apply Nat.floor_mono
  apply Real.exp_le_exp.mpr
  apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 6)
  have h₁ : (r i : ℝ) ≤ (r j : ℝ) := by exact_mod_cast hr hij
  have h₂ : (1 : ℝ) ≤ (r j : ℝ) := by exact_mod_cast (show 1 ≤ r j by have := hr₂ j; omega)
  exact (pow_le_pow_left₀ (Nat.cast_nonneg _) h₁ _).trans (pow_le_pow_right₀ h₂ hij)

/-- Consecutive floored scales eventually differ strictly. -/
theorem eventually_fastApproximationScale_lt_succ {r : ℕ → ℕ} (hr : Monotone r)
    (hr₂ : ∀ j, 2 ≤ r j) :
    ∀ᶠ j : ℕ in atTop, fastApproximationScale (r j) j <
      fastApproximationScale (r (j+1)) (j+1) := by
  let x (j : ℕ) := (r j : ℝ)^j/6
  have hx : Tendsto x atTop atTop := tendsto_fastExponent r hr₂
  filter_upwards [(Real.tendsto_exp_atTop.comp hx).eventually_ge_atTop 2] with j hj
  change 2 ≤ Real.exp (x j) at hj
  have hrj : (r j : ℝ) ≤ r (j+1) := by exact_mod_cast hr (show j ≤ j+1 by omega)
  have hrj₂ : (2 : ℝ) ≤ r (j+1) := by exact_mod_cast hr₂ (j+1)
  have hx₂ : 2*x j ≤ x (j+1) := by
    dsimp [x]
    rw [pow_succ]
    exact (show 2*((r j : ℝ)^j/6) = ((r j : ℝ)^j*2)/6 by ring).trans_le
      (div_le_div_of_nonneg_right
        (mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) hrj _) hrj₂
          (by norm_num) (by positivity)) (by norm_num))
  have hExp : Real.exp (x j) + 1 ≤ Real.exp (x (j+1)) := by
    calc
      _ ≤ Real.exp (x j) * Real.exp (x j) := by nlinarith only [hj, sq_nonneg (Real.exp (x j)-2)]
      _ = Real.exp (2*x j) := by rw [← Real.exp_add, two_mul]
      _ ≤ _ := Real.exp_le_exp.mpr hx₂
  apply Nat.lt_of_succ_le
  apply (Nat.le_floor_iff (Real.exp_pos _).le).mpr
  push_cast
  exact (add_le_add_right (Nat.floor_le (Real.exp_pos (x j)).le) 1).trans hExp

/-- Eventually the parameter interval contains at least two complete
blocks of length equal to the current denominator. -/
theorem eventually_two_mul_le_fastApproximationScale {r : ℕ → ℕ} (hr : StrictMono r) :
    ∀ᶠ j : ℕ in atTop, 2*r j ≤ fastApproximationScale (r j) j := by
  filter_upwards [hr.tendsto_atTop.eventually_ge_atTop 12, eventually_ge_atTop (2 : ℕ)]
    with j hj hIndex
  have hR : (12 : ℝ) ≤ r j := by exact_mod_cast hj
  have hR₁ : (1 : ℝ) ≤ r j := by linarith
  have hPower := pow_le_pow_right₀ hR₁ hIndex
  apply (Nat.le_floor_iff (Real.exp_pos _).le).mpr
  push_cast
  have h := Real.add_one_le_exp ((r j : ℝ)^j/6)
  nlinarith only [hPower, h,
    mul_nonneg (Nat.cast_nonneg (r j) : (0 : ℝ) ≤ r j) (sub_nonneg.mpr hR)]

/-- Rounding the spatial scale loses at most half its logarithm at
sufficiently large indices. -/
theorem eventually_fastApproximationScale_log_lower (r : ℕ → ℕ) (hr : ∀ j, 2 ≤ r j) :
    ∀ᶠ j : ℕ in atTop,
      (r j : ℝ)^j/12 ≤ Real.log (fastApproximationScale (r j) j : ℝ) := by
  let x (j : ℕ) := (r j : ℝ)^j/6
  have hx : Tendsto x atTop atTop := tendsto_fastExponent r hr
  filter_upwards [hx.eventually_ge_atTop (2*Real.log 2),
    (Real.tendsto_exp_atTop.comp hx).eventually_ge_atTop 2] with j hLog hx₂
  change 2*Real.log 2 ≤ x j at hLog
  change 2 ≤ Real.exp (x j) at hx₂
  let N := fastApproximationScale (r j) j
  have hN : Real.exp (x j)/2 ≤ (N : ℝ) := by
    have h : Real.exp (x j) < (N : ℝ)+1 := Nat.lt_floor_add_one _
    linarith only [h,hx₂]
  have h := Real.log_le_log (div_pos (Real.exp_pos _) (by norm_num : (0 : ℝ)<2)) hN
  rw [Real.log_div (Real.exp_ne_zero _) (by norm_num), Real.log_exp] at h
  change (r j : ℝ)^j/12 ≤ Real.log (N : ℝ)
  dsimp only [x] at h hLog
  linarith only [h,hLog]

/-- On these spatial scales any fixed positive multiple of the reciprocal
denominator eventually exceeds the proposed power of the logarithm. -/
theorem eventually_fastApproximationScale_log_neg_rpow_lt {r : ℕ → ℕ} (hr : StrictMono r)
    (hr₂ : ∀ j, 2 ≤ r j) {κ c : ℝ} (hκ : 0 < κ) (hc : 0 < c) :
    ∀ᶠ j : ℕ in atTop,
      (Real.log (fastApproximationScale (r j) j : ℝ))^(-κ) < c/(r j : ℝ) := by
  have hI : Tendsto (fun j : ℕ => (j : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hR : Tendsto (fun j => (r j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hr.tendsto_atTop
  filter_upwards [eventually_fastApproximationScale_log_lower r hr₂,
    hI.eventually_ge_atTop (2/κ), hR.eventually_gt_atTop ((12 : ℝ)^κ/c)]
    with j hLog hj hLarge
  have hR' : (1 : ℝ) ≤ r j := by exact_mod_cast (show 1 ≤ r j by have := hr₂ j; omega)
  have hRp : (0 : ℝ) < r j := zero_lt_one.trans_le hR'
  have hjκ : 2 ≤ (j : ℝ)*κ := (div_le_iff₀ hκ).mp hj
  have hRat : (0 : ℝ) < (r j : ℝ)^j/12 := by positivity
  calc
    _ ≤ ((r j : ℝ)^j/12)^(-κ) :=
      Real.rpow_le_rpow_of_exponent_nonpos hRat hLog (neg_nonpos.mpr hκ.le)
    _ = (12 : ℝ)^κ * (r j : ℝ)^(-(j : ℝ)*κ) := by
      rw [Real.div_rpow (by positivity) (by norm_num : (0 : ℝ)≤12),
        Real.rpow_neg (by norm_num : (0 : ℝ)≤12), div_inv_eq_mul,
        ← Real.rpow_natCast, ← Real.rpow_mul hRp.le]
      rw [show (j : ℝ)*(-κ) = -(j : ℝ)*κ by ring, mul_comm]
    _ ≤ (12 : ℝ)^κ * (r j : ℝ)^(-2 : ℝ) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hR' (by linarith))
        (Real.rpow_nonneg (by norm_num) _)
    _ < _ := by
      have h := (div_lt_iff₀ hc).mp hLarge
      rw [Real.rpow_neg hRp.le, Real.rpow_two, ← div_eq_mul_inv]
      apply (div_lt_div_iff₀ (sq_pos_of_pos hRp) hRp).mpr
      nlinarith only [mul_lt_mul_of_pos_left h hRp]

/-- The full interval is short enough for the floor identity when the
slope error is bounded by the exponential prescribed in the introduction. -/
theorem fastApproximationScale_mul_expNeg_lt_one {r : ℕ} (hr : 0 < r) (j : ℕ) :
    (fastApproximationScale r j : ℝ) * Real.exp (-((r : ℝ)^j)) < 1 := by
  have h := Nat.floor_le (Real.exp_pos ((r : ℝ)^j/6)).le
  apply (mul_le_mul_of_nonneg_right h (Real.exp_pos _).le).trans_lt
  rw [← Real.exp_add, Real.exp_lt_one_iff]
  have hp : (0 : ℝ) < (r : ℝ)^j := pow_pos (Nat.cast_pos.mpr hr) _
  linarith only [hp]

end NilBohr
