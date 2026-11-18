import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic

/-! Reduced Dirichlet approximants with denominators growing at every large scale. -/

namespace NilBohr

open Filter
open scoped Topology

/-- The integer square root has the same order of growth as the real square root. -/
theorem natSqrt_bounds {N : ℕ} (hN : 0 < N) :
    Real.sqrt (N : ℝ) / 2 ≤ (N.sqrt : ℝ) ∧ (N.sqrt : ℝ) ≤ Real.sqrt (N : ℝ) := by
  have hsq : (N.sqrt : ℝ)^2 ≤ (N : ℝ) := by exact_mod_cast Nat.sqrt_le' N
  have h₁ : 1 ≤ N.sqrt := Nat.le_sqrt'.mpr (by simpa using hN)
  have h₁' : (1 : ℝ) ≤ (N.sqrt : ℝ) := by exact_mod_cast h₁
  have hNlt : (N : ℝ) < ((N.sqrt : ℝ) + 1)^2 := by
    exact_mod_cast Nat.lt_succ_sqrt' N
  constructor
  · rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2), mul_comm]
    have h : Real.sqrt (N : ℝ) ≤ (N.sqrt : ℝ) + 1 :=
      Real.sqrt_le_iff.mpr ⟨by positivity, hNlt.le⟩
    linarith
  · exact (Real.le_sqrt (by positivity) (by positivity)).mpr hsq

private theorem eventually_dirichlet_den_gt {α : ℝ} (hα : Irrational α) (B : ℕ) :
    ∀ᶠ R : ℕ in atTop, ∀ (q : ℕ) (a : ℤ), 0 < q →
      |(q : ℝ) * α - (a : ℝ)| ≤ 1 / (R : ℝ) → B < q := by
  have ht : Tendsto (fun R : ℕ => 1 / (R : ℝ)) atTop (𝓝 0) := by
    have h := tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [Function.comp_def, one_div] using h
  have hFinite : ∀ᶠ R : ℕ in atTop, ∀ q ∈ Finset.Icc 1 B,
      1 / (R : ℝ) < |(q : ℝ) * α - (round ((q : ℝ) * α) : ℝ)| := by
    apply (eventually_all_finset _).mpr
    intro q hq
    have hq' : 0 < q := (Finset.mem_Icc.mp hq).1
    have hi := irrational_natCast_mul_iff.mpr ⟨hq'.ne', hα⟩
    exact ht.eventually_lt_const (abs_pos.mpr (sub_ne_zero.mpr (hi.ne_int _)))
  filter_upwards [hFinite] with R hR q a hq hApp
  by_contra! hqB
  exact (not_le_of_gt (hR q (Finset.mem_Icc.mpr ⟨hq, hqB⟩)))
    ((round_le _ a).trans hApp)

/-- For every sufficiently large scale `R`, choose a reduced rational approximant
with denominator at most `R` and exceeding any previously fixed bound. -/
theorem eventually_irrational_dirichlet_approximation_at_scale {α : ℝ}
    (hα : Irrational α) (B : ℕ) : ∀ᶠ R : ℕ in atTop, ∃ (a : ℤ) (q : ℕ),
      0 < q ∧ B < q ∧ q ≤ R ∧ a.natAbs.Coprime q ∧
        |α - (a : ℝ) / (q : ℝ)| ≤ 1 / ((q : ℝ) * (R : ℝ)) := by
  filter_upwards [eventually_gt_atTop (0 : ℕ), eventually_dirichlet_den_gt hα B]
    with R hR hDen
  obtain ⟨r, hApp, hLe⟩ := Real.exists_rat_abs_sub_le_and_den_le α hR
  rw [Rat.cast_def] at hApp
  have hqpos : (0 : ℝ) < (r.den : ℝ) := Nat.cast_pos.mpr r.pos
  have hRpos : (0 : ℝ) < (R : ℝ) := Nat.cast_pos.mpr hR
  have hApp' : |α - (r.num : ℝ) / (r.den : ℝ)| ≤ 1 / ((r.den : ℝ) * (R : ℝ)) :=
    hApp.trans (one_div_le_one_div_of_le (mul_pos hqpos hRpos) (by
      rw [mul_comm (r.den : ℝ)]
      gcongr
      linarith))
  refine ⟨r.num, r.den, r.pos, hDen r.den r.num r.pos ?_, hLe, r.reduced, hApp'⟩
  calc
    |(r.den : ℝ) * α - (r.num : ℝ)| =
        |(r.den : ℝ) * (α - (r.num : ℝ) / (r.den : ℝ))| := by
      congr 1
      field_simp
      ring
    _ = (r.den : ℝ) * |α - (r.num : ℝ) / (r.den : ℝ)| := by
      rw [abs_mul, abs_of_pos hqpos]
    _ ≤ (r.den : ℝ) * (1 / ((r.den : ℝ) * (R : ℝ))) :=
      mul_le_mul_of_nonneg_left hApp' hqpos.le
    _ = 1 / (R : ℝ) := by field_simp

/-- Apply the all-scale approximants at the integer square root of the cutoff. -/
theorem eventually_irrational_dirichlet_approximation {α : ℝ}
    (hα : Irrational α) (B : ℕ) : ∀ᶠ N : ℕ in atTop, ∃ (a : ℤ) (q : ℕ),
      0 < q ∧ B < q ∧ q ≤ N.sqrt ∧ a.natAbs.Coprime q ∧
        |α - (a : ℝ) / (q : ℝ)| ≤ 1 / ((q : ℝ) * (N.sqrt : ℝ)) := by
  have hs : Tendsto Nat.sqrt atTop atTop := by
    apply tendsto_atTop.mpr
    intro R
    exact (eventually_ge_atTop (R^2)).mono fun _ h => Nat.le_sqrt'.mpr h
  exact hs.eventually (eventually_irrational_dirichlet_approximation_at_scale hα B)

/-- The logarithm from the Cramér normalization is absorbed by the
power gap between the sieve level and the square-root scale. -/
theorem tendsto_log_mul_sieveLevel_div_natSqrt :
    Tendsto (fun N : ℕ => Real.log (N : ℝ) *
      ((⌊(N : ℝ) ^ (1 / 20000 : ℝ)⌋₊ : ℕ) : ℝ) / (N.sqrt : ℝ)) atTop (𝓝 0) := by
  let a : ℝ := 1 / 20000
  let b : ℝ := 1 / 2 - a
  have hb : 0 < b := by norm_num [a, b]
  have hLimit : Tendsto (fun N : ℕ => 2 * (Real.log (N : ℝ) / (N : ℝ)^b)) atTop (𝓝 0) := by
    have ht := ((isLittleO_log_rpow_atTop hb).tendsto_div_nhds_zero.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul (2 : ℝ)
    simpa only [Function.comp_def, mul_zero] using ht
  apply squeeze_zero' (Eventually.of_forall fun N => by positivity) _ hLimit
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hX : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hLog := Real.log_natCast_nonneg N
  have hFloor : (⌊(N : ℝ) ^ a⌋₊ : ℝ) ≤ (N : ℝ)^a :=
    Nat.floor_le (Real.rpow_nonneg hX.le _)
  have hSqrt : 0 < Real.sqrt (N : ℝ) / 2 := by positivity
  calc
    _ ≤ (Real.log (N : ℝ) * (N : ℝ)^a) / (Real.sqrt (N : ℝ) / 2) := by
      apply div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hFloor hLog) hSqrt
      exact (natSqrt_bounds hN).1
    _ = _ := by
      rw [Real.sqrt_eq_rpow, div_div_eq_mul_div, mul_comm _ (2 : ℝ), ← mul_div_assoc,
        mul_div_assoc, mul_div_assoc, ← Real.rpow_sub hX]
      rw [show a - (1 / 2 : ℝ) = -b by dsimp [b]; ring, Real.rpow_neg hX.le, div_eq_mul_inv]
      ring

/-- The shorter interval-counting error also vanishes after logarithmic normalization. -/
theorem tendsto_log_mul_sieveLevel_div_cutoff :
    Tendsto (fun N : ℕ => Real.log (N : ℝ) *
      ((⌊(N : ℝ) ^ (1 / 20000 : ℝ)⌋₊ : ℕ) : ℝ) / (N : ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun N => by positivity) _
    tendsto_log_mul_sieveLevel_div_natSqrt
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hSqrt : 0 < N.sqrt := Nat.le_sqrt'.mpr (by simpa using hN)
  exact div_le_div_of_nonneg_left (by positivity) (Nat.cast_pos.mpr hSqrt)
    (Nat.cast_le.mpr (Nat.sqrt_le_self N))

/-- The sieve divisors eventually lie below half the square-root scale. -/
theorem eventually_twice_sieveLevel_le_natSqrt :
    ∀ᶠ N : ℕ in atTop, 2 * ⌊(N : ℝ) ^ (1 / 20000 : ℝ)⌋₊ ≤ N.sqrt := by
  have hN := tendsto_natCast_atTop_atTop (R := ℝ)
  filter_upwards [(Real.tendsto_log_atTop.comp hN).eventually_ge_atTop (1 : ℝ),
    eventually_gt_atTop (0 : ℕ),
    tendsto_log_mul_sieveLevel_div_natSqrt.eventually_lt_const (show (0 : ℝ) < 1/2 by norm_num)]
    with N hLog hN hLimit
  have hSqrt : 0 < N.sqrt := Nat.le_sqrt'.mpr (by simpa using hN)
  have hp : 0 < (N.sqrt : ℝ) := Nat.cast_pos.mpr hSqrt
  have hLimit' := (div_lt_iff₀ hp).mp hLimit
  have hFloor : (⌊(N : ℝ) ^ (1 / 20000 : ℝ)⌋₊ : ℝ) ≤
      Real.log (N : ℝ) * (⌊(N : ℝ) ^ (1 / 20000 : ℝ)⌋₊ : ℝ) :=
    le_mul_of_one_le_left (by positivity) hLog
  have hTwo : 2 * (⌊(N : ℝ) ^ (1 / 20000 : ℝ)⌋₊ : ℝ) ≤ (N.sqrt : ℝ) := by
    linarith
  exact_mod_cast hTwo

end NilBohr
