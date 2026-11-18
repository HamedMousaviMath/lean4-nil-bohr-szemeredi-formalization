import NilBohr.Ergodic
import NilBohr.LcmMangoldt
import NilBohr.PrimePowers
import Mathlib.NumberTheory.Primorial

/-! The elementary Chebyshev upper bound used to initialize the
density increment. -/

namespace NilBohr

open Filter
open scoped Topology BigOperators

/-- The prime logarithm sum is the logarithm of the primorial. -/
theorem sum_log_primesThrough_eq_log_primorial (n : ℕ) :
    (∑ p ∈ primesThrough n, Real.log (p : ℝ)) = Real.log (primorial n : ℝ) := by
  have hcast : (primorial n : ℝ) = ∏ p ∈ primesThrough n, (p : ℝ) := by
    simp only [primorial, primesThrough, Nat.cast_prod]
  rw [hcast, Real.log_prod]
  intro p hp
  exact_mod_cast (Finset.mem_filter.mp hp).2.ne_zero

/-- Chebyshev's upper bound for the first prime logarithm sum follows
from Mathlib's primorial bound. -/
theorem sum_log_primesThrough_le (n : ℕ) :
    (∑ p ∈ primesThrough n, Real.log (p : ℝ)) ≤ Real.log 4 * (n : ℝ) := by
  rw [sum_log_primesThrough_eq_log_primorial]
  have hpos : 0 < (primorial n : ℝ) := by exact_mod_cast primorial_pos n
  have hle : (primorial n : ℝ) ≤ (4 : ℝ)^n := by exact_mod_cast primorial_le_4_pow n
  simpa only [Real.log_pow, mul_comm] using Real.log_le_log hpos hle

/-- Chebyshev's Mangoldt mass bound, with a single constant valid
also at the finite initial cutoffs. -/
theorem exists_sum_vonMangoldt_le_linear :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      (∑ m ∈ Finset.range (n + 1), ArithmeticFunction.vonMangoldt m) ≤ C * (n : ℝ) := by
  obtain ⟨K, hK⟩ := eventually_atTop.1
    (tendsto_higherPrimePowers_mangoldtMass_div.eventually_lt_const (by norm_num : (0 : ℝ) < 1))
  let C := max (Real.log 4 + 1) (2 * Real.log ((K : ℝ) + 1))
  have hlog4 : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
  refine ⟨C, lt_of_lt_of_le (by linarith) (le_max_left _ _), ?_⟩
  intro n
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  by_cases hcut : K ≤ n
  · have hErr := norm_sub_mangoldt_logPrime_le (u := fun _ => (1 : ℝ)) (B := 1)
      (fun _ => by simp) n
    simp only [smul_eq_mul, mul_one, one_mul, Real.norm_eq_abs, ← div_eq_inv_mul] at hErr
    have hMass := ((abs_le.mp hErr).2).trans (hK n hcut).le
    have hTheta := div_le_div_of_nonneg_right (sum_log_primesThrough_le n) hnR.le
    rw [mul_div_cancel_right₀ _ hnR.ne'] at hTheta
    have hquot : (∑ m ∈ Finset.range (n + 1), ArithmeticFunction.vonMangoldt m) / (n : ℝ) ≤
        Real.log 4 + 1 := by
      change _ - (∑ p ∈ primesThrough n, Real.log (p : ℝ)) / (n : ℝ) ≤ 1 at hMass
      linarith
    exact ((div_le_iff₀ hnR).mp hquot).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hnR.le)
  · have hlogK : 0 ≤ Real.log ((K : ℝ) + 1) :=
      Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) K])
    have hcut' : n ≤ K + 1 := by omega
    calc
      _ ≤ ∑ _m ∈ Finset.range (n + 1), Real.log ((K : ℝ) + 1) := by
        apply Finset.sum_le_sum
        intro m hm
        have hmn := Nat.le_of_lt_succ (Finset.mem_range.mp hm)
        rcases m.eq_zero_or_pos with rfl | hm₀
        · simpa only [ArithmeticFunction.map_zero] using hlogK
        · exact ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log
            (Nat.cast_pos.mpr hm₀) (by exact_mod_cast hmn.trans hcut'))
      _ = ((n : ℝ)+1) * Real.log ((K : ℝ)+1) := by simp
      _ ≤ (2 * Real.log ((K : ℝ)+1)) * (n : ℝ) := by
        have hnOne : 1 ≤ (n : ℝ) := by exact_mod_cast hn
        nlinarith only [mul_le_mul_of_nonneg_right hnOne hlogK]
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hnR.le

/-- The logarithm of the initial smooth modulus obeys the linear bound
used in Section 3. -/
theorem exists_log_initialModulus_le_linear :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℕ, Real.log (initialModulus w : ℝ) ≤ C * (w : ℝ) := by
  obtain ⟨C, hC, hBound⟩ := exists_sum_vonMangoldt_le_linear
  exact ⟨C, hC, fun w => by rw [log_initialModulus_eq_mangoldt_sum]; exact hBound w⟩

/-- Uniformly at the polylogarithmic initial density, the logarithm of
the initial smooth modulus is small compared with the logarithmic cutoff. -/
theorem eventually_log_initialModulus_at_density_le {K E κ ε : ℝ}
    (hK : 0 < K) (hE : 0 ≤ E) (hκ : 0 < κ) (hκE : κ*E < 1) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ δ : ℝ, Real.log (N : ℝ)^(-κ) ≤ δ →
      Real.log (initialModulus ⌈K * δ^(-E)⌉₊ : ℝ) ≤ ε * Real.log (N : ℝ) := by
  obtain ⟨C, hC, hBound⟩ := exists_log_initialModulus_le_linear
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hPow := (tendsto_rpow_atTop (sub_pos.mpr hκE)).comp hlog
  filter_upwards [hlog.eventually_ge_atTop 1,
    hPow.eventually_ge_atTop (C*(K+1)/ε)] with N ht hRate δ hδ
  let t := Real.log (N : ℝ)
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hPower : 1 ≤ t^(κ*E) := Real.one_le_rpow ht (mul_nonneg hκ.le hE)
  have hδPow := Real.rpow_le_rpow_of_exponent_nonpos (Real.rpow_pos_of_pos ht0 (-κ)) hδ
    (neg_nonpos.mpr hE)
  rw [← Real.rpow_mul ht0.le, neg_mul_neg] at hδPow
  have hCeil : (⌈K * δ^(-E)⌉₊ : ℝ) ≤ (K+1)*t^(κ*E) := by
    have h₁ := (Nat.ceil_lt_add_one (mul_nonneg hK.le
      (Real.rpow_nonneg ((Real.rpow_pos_of_pos ht0 (-κ)).le.trans hδ) (-E)))).le
    have h₂ := mul_le_mul_of_nonneg_left hδPow hK.le
    rw [add_mul, one_mul]
    linarith only [h₁, h₂, hPower]
  have hRate' : C*(K+1) ≤ ε*t^(1-κ*E) := by
    simpa only [mul_comm ε] using (div_le_iff₀ hε).mp hRate
  calc
    _ ≤ C * (⌈K * δ^(-E)⌉₊ : ℝ) := hBound _
    _ ≤ C * ((K+1)*t^(κ*E)) := mul_le_mul_of_nonneg_left hCeil hC.le
    _ ≤ (ε*t^(1-κ*E))*t^(κ*E) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hRate' (Real.rpow_nonneg ht0.le _)
    _ = ε*t := by rw [mul_assoc, ← Real.rpow_add ht0, sub_add_cancel, Real.rpow_one]

/-- The logarithmic modulus budget through the density-iteration horizon
is linear in the smoothing parameter and polynomial in inverse density. -/
theorem exists_log_iteration_modulus_le_linear_in_w {η b : ℝ} (hη : 0 < η) (hb : 1 ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ {δ : ℝ}, 0 < δ → δ ≤ 1 → ∀ {i q w : ℕ},
      i ≤ densityIterationSteps η δ →
      Real.log (q : ℝ) ≤ b^i * Real.log (initialModulus w : ℝ) →
      Real.log (q : ℝ) ≤ C * δ^(-(Real.log b / Real.log (1 + η))) * (w : ℝ) := by
  obtain ⟨C, hC, hBound⟩ := exists_log_initialModulus_le_linear
  have hb0 : 0 < b := zero_lt_one.trans_le hb
  refine ⟨C*b, mul_pos hC hb0, ?_⟩
  intro δ hδ hδ₁ i q w hi hq
  calc
    _ ≤ b^i * Real.log (initialModulus w : ℝ) := hq
    _ ≤ b^i * (C * (w : ℝ)) := mul_le_mul_of_nonneg_left (hBound w) (pow_nonneg hb0.le _)
    _ ≤ (b * δ^(-(Real.log b / Real.log (1 + η)))) * (C * (w : ℝ)) :=
      mul_le_mul_of_nonneg_right (modulus_growth_to_density_power hη hδ hδ₁ hb hi) (by positivity)
    _ = _ := by ring

end NilBohr
