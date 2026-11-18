import NilBohr.ErgodicLimits
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Prime counting from the Chebyshev theta asymptotic

The two normalizations used for prime averages follow from the theta
form of the prime number theorem alone. For a fixed exponent between
zero and one, the primes at most the corresponding power of the cutoff
give a vanishing contribution to the normalized count.
-/

namespace NilBohr

open Filter
open scoped Topology BigOperators

private noncomputable def primeCountRatio (n : ℕ) : ℝ :=
  ((primesThrough n).card : ℝ) * Real.log (n : ℝ) / (n : ℝ)

private noncomputable def primeLogRatio (n : ℕ) : ℝ :=
  (∑ p ∈ primesThrough n, Real.log (p : ℝ)) / (n : ℝ)

private noncomputable def smallPrimeError (a : ℝ) (n : ℕ) : ℝ :=
  (((n : ℝ) ^ a + 1) * Real.log (n : ℝ)) / (n : ℝ)

private theorem primeLogRatio_le_primeCountRatio (n : ℕ) :
    primeLogRatio n ≤ primeCountRatio n := by
  unfold primeLogRatio primeCountRatio
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  rw [← nsmul_eq_mul, ← Finset.sum_const]
  apply Finset.sum_le_sum
  intro p hp
  obtain ⟨hp_range, hp_prime⟩ := Finset.mem_filter.mp hp
  exact Real.log_le_log (Nat.cast_pos.mpr hp_prime.pos)
    (Nat.cast_le.mpr (Nat.le_of_lt_succ (Finset.mem_range.mp hp_range)))

private theorem mul_primeCountRatio_le {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 0 < n) :
    a * primeCountRatio n ≤ primeLogRatio n + a * smallPrimeError a n := by
  classical
  have hn_real : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  let small (p : ℕ) : Prop := (p : ℝ) ≤ (n : ℝ) ^ a
  let S := (primesThrough n).filter small
  let T := (primesThrough n).filter (fun p => ¬small p)
  have hS : (S.card : ℝ) ≤ (n : ℝ) ^ a + 1 := by
    have hcard : S.card ≤ ⌊(n : ℝ) ^ a⌋₊ + 1 := by
      rw [← Finset.card_range (⌊(n : ℝ) ^ a⌋₊ + 1)]
      apply Finset.card_le_card
      intro p hp
      have hp' : (p : ℝ) ≤ (n : ℝ) ^ a := (Finset.mem_filter.mp hp).2
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor hp'))
    have hcast : (S.card : ℝ) ≤ (⌊(n : ℝ) ^ a⌋₊ : ℕ) + 1 := by exact_mod_cast hcard
    exact hcast.trans (add_le_add_right (Nat.floor_le (Real.rpow_nonneg hn_real.le _)) 1)
  have hS' : (S.card : ℝ) * (a * Real.log (n : ℝ)) ≤
      ((n : ℝ) ^ a + 1) * (a * Real.log (n : ℝ)) :=
    mul_le_mul_of_nonneg_right hS (mul_nonneg ha.le (Real.log_natCast_nonneg n))
  have hT : (T.card : ℝ) * (a * Real.log (n : ℝ)) ≤
      ∑ p ∈ primesThrough n, Real.log (p : ℝ) := calc
    _ = ∑ _p ∈ T, a * Real.log (n : ℝ) := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ p ∈ T, Real.log (p : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      have hp' : (n : ℝ) ^ a ≤ (p : ℝ) :=
        le_of_lt (lt_of_not_ge (Finset.mem_filter.mp hp).2)
      rw [← Real.log_rpow hn_real]
      exact Real.log_le_log (Real.rpow_pos_of_pos hn_real _) hp'
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _) (fun p _ _ => Real.log_natCast_nonneg p)
  have hsplit : ((primesThrough n).card : ℝ) * (a * Real.log (n : ℝ)) =
      (S.card : ℝ) * (a * Real.log (n : ℝ)) +
        (T.card : ℝ) * (a * Real.log (n : ℝ)) := by
    simpa only [Finset.sum_const, nsmul_eq_mul] using
      (Finset.sum_filter_add_sum_filter_not (primesThrough n) small
        (fun _ => a * Real.log (n : ℝ))).symm
  have hsum := add_le_add hS' hT
  rw [← hsplit] at hsum
  calc
    _ = (((primesThrough n).card : ℝ) * (a * Real.log (n : ℝ))) / (n : ℝ) := by
      unfold primeCountRatio
      ring
    _ ≤ (((n : ℝ) ^ a + 1) * (a * Real.log (n : ℝ)) +
        ∑ p ∈ primesThrough n, Real.log (p : ℝ)) / (n : ℝ) :=
      div_le_div_of_nonneg_right hsum hn_real.le
    _ = _ := by unfold primeLogRatio smallPrimeError; ring

private theorem tendsto_smallPrimeError {a : ℝ} (ha : a < 1) :
    Tendsto (smallPrimeError a) atTop (𝓝 0) := by
  have h_power : Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ) ^ (1 - a))
      atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (sub_pos.mpr ha)).tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop
  have h_log : Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have h_add : Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ) ^ (1 - a) +
      Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by simpa using h_power.add h_log
  apply h_add.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn_real : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  dsimp [smallPrimeError]
  rw [add_mul, add_div, one_mul, show (n : ℝ) ^ a * Real.log (n : ℝ) / (n : ℝ) =
    Real.log (n : ℝ) * ((n : ℝ) ^ a / (n : ℝ)) by ring,
    ← Real.rpow_sub_one hn_real.ne', show a - 1 = -(1 - a) by ring,
    Real.rpow_neg hn_real.le, div_eq_mul_inv (Real.log (n : ℝ)) ((n : ℝ) ^ (1 - a))]

/-- The theta asymptotic implies the normalized prime-count asymptotic
with the inclusive cutoff used throughout the project. -/
theorem tendsto_primeCount_of_tendsto_theta
    (h : Tendsto (fun n : ℕ => (∑ p ∈ primesThrough n, Real.log (p : ℝ)) /
      (n : ℝ)) atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => ((primesThrough n).card : ℝ) * Real.log (n : ℝ) /
      (n : ℝ)) atTop (𝓝 1) := by
  change Tendsto primeLogRatio atTop (𝓝 1) at h
  change Tendsto primeCountRatio atTop (𝓝 1)
  apply tendsto_order.mpr
  constructor
  · intro b hb
    filter_upwards [h.eventually_const_lt hb] with n hn
    exact hn.trans_le (primeLogRatio_le_primeCountRatio n)
  · intro b hb
    let a : ℝ := 2 / (1 + b)
    have hden : 0 < 1 + b := by linarith
    have ha_pos : 0 < a := div_pos (by norm_num) hden
    have ha_lt : a < 1 := (div_lt_one hden).mpr (by linarith)
    have hab : 1 < a * b := by
      rw [show a * b = 2 * b / (1 + b) by dsimp [a]; ring]
      exact (lt_div_iff₀ hden).mpr (by linarith)
    have h_upper : Tendsto (fun n => primeLogRatio n + a * smallPrimeError a n)
        atTop (𝓝 1) := by
      simpa using h.add ((tendsto_smallPrimeError ha_lt).const_mul a)
    filter_upwards [eventually_gt_atTop (0 : ℕ), h_upper.eventually_lt_const hab] with n hn hlim
    exact lt_of_mul_lt_mul_left ((mul_primeCountRatio_le ha_pos hn).trans_lt hlim) ha_pos.le

/-- The theta statement suffices to construct the existing prime number
theorem interface. -/
theorem PrimeNumberTheorem.of_theta
    (h : Tendsto (fun n : ℕ => (∑ p ∈ primesThrough n, Real.log (p : ℝ)) /
      (n : ℝ)) atTop (𝓝 1)) : PrimeNumberTheorem :=
  ⟨tendsto_primeCount_of_tendsto_theta h, h⟩

/-- The inclusive prime count asymptotic also supplies the theta asymptotic. -/
theorem PrimeNumberTheorem.of_count
    (h : Tendsto (fun n : ℕ => ((primesThrough n).card : ℝ) * Real.log (n : ℝ) /
      (n : ℝ)) atTop (𝓝 1)) : PrimeNumberTheorem := by
  refine ⟨h, ?_⟩
  change Tendsto primeCountRatio atTop (𝓝 1) at h
  change Tendsto primeLogRatio atTop (𝓝 1)
  apply tendsto_order.mpr
  constructor
  · intro b hb
    let a : ℝ := (max b 0 + 1) / 2
    have hab : b < a := by dsimp [a]; linarith [le_max_left b (0 : ℝ)]
    have ha_pos : 0 < a := by dsimp [a]; linarith [le_max_right b (0 : ℝ)]
    have ha_lt : a < 1 := by
      have hm : max b 0 < 1 := max_lt hb zero_lt_one
      dsimp [a]
      linarith
    have ht : Tendsto (fun n => a * primeCountRatio n - a * smallPrimeError a n)
        atTop (𝓝 a) := by
      simpa only [mul_one, mul_zero, sub_zero] using
        (h.const_mul a).sub ((tendsto_smallPrimeError ha_lt).const_mul a)
    filter_upwards [eventually_gt_atTop (0 : ℕ), ht.eventually_const_lt hab] with n hn hlim
    exact hlim.trans_le (sub_le_iff_le_add.mpr (mul_primeCountRatio_le ha_pos hn))
  · intro b hb
    filter_upwards [h.eventually_lt_const hb] with n hn
    exact (primeLogRatio_le_primeCountRatio n).trans_lt hn

/-- The Mangoldt form of the prime number theorem gives both normalizations
through the removal of higher prime powers. -/
theorem PrimeNumberTheorem.of_psi
    (h : Tendsto (fun n : ℕ => (∑ m ∈ Finset.range (n + 1),
      ArithmeticFunction.vonMangoldt m) / (n : ℝ)) atTop (𝓝 1)) : PrimeNumberTheorem := by
  apply PrimeNumberTheorem.of_theta
  have ht := tendsto_logPrime_of_tendsto_mangoldt (u := fun _ => (1 : ℝ)) (B := 1)
    (fun _ => by simp) (by simpa only [smul_eq_mul, mul_one, div_eq_inv_mul] using h)
  simpa only [primesThrough, smul_eq_mul, mul_one, div_eq_inv_mul] using ht

/-- Reintroducing the higher prime powers recovers the Mangoldt form of
the prime number theorem from the two prime normalizations. -/
theorem PrimeNumberTheorem.to_psi (h : PrimeNumberTheorem) :
    Tendsto (fun n : ℕ => (∑ m ∈ Finset.range (n + 1),
      ArithmeticFunction.vonMangoldt m) / (n : ℝ)) atTop (𝓝 1) := by
  let ψ (n : ℕ) := (∑ m ∈ Finset.range (n + 1), ArithmeticFunction.vonMangoldt m) / (n : ℝ)
  have hnorm (n : ℕ) : ‖ψ n - primeLogRatio n‖ ≤
      (∑ m ∈ higherPrimePowersThrough n, ArithmeticFunction.vonMangoldt m) / (n : ℝ) := by
    simpa only [ψ, primeLogRatio, primesThrough, smul_eq_mul, mul_one, one_mul, div_eq_inv_mul]
      using norm_sub_mangoldt_logPrime_le (u := fun _ => (1 : ℝ)) (B := 1) (fun _ => by simp) n
  have herror : Tendsto (fun n => ψ n - primeLogRatio n) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) hnorm tendsto_higherPrimePowers_mangoldtMass_div
  have hθ : Tendsto primeLogRatio atTop (𝓝 1) := h.theta
  simpa only [sub_add_cancel, zero_add] using herror.add hθ

end NilBohr
