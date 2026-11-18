import Mathlib

/-! The elementary higher-prime-power error used in the density increment
and in the transfer from Mangoldt sums to prime sums. -/

namespace NilBohr

open Filter
open scoped Topology BigOperators

/-- The prime powers (p^k \le N) with (k\ge 2). -/
def higherPrimePowersThrough (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter (fun n => IsPrimePow n ∧ ¬n.Prime)

/-- A prime base is at most the square root of the cutoff and the exponent
is at most its logarithm to base two. No uniqueness of representations
is needed for this upper bound. -/
theorem card_higherPrimePowersThrough_le (N : ℕ) :
    (higherPrimePowersThrough N).card ≤ (Nat.sqrt N + 1) * (Nat.log 2 N + 1) := by
  let pairs := (Finset.range (Nat.sqrt N + 1)).product (Finset.range (Nat.log 2 N + 1))
  let power : ℕ × ℕ → ℕ := fun a => a.1 ^ a.2
  have h_subset : higherPrimePowersThrough N ⊆ pairs.image power := by
    intro n hn
    obtain ⟨hm, hpow, hprime⟩ := Finset.mem_filter.mp hn
    have hn_le : n ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hm)
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hpow
    have hk₂ : 2 ≤ k := by
      by_contra! hk'
      have hke : k = 1 := by omega
      exact hprime (by simpa [hke] using hp)
    have hpsqrt : p ≤ Nat.sqrt N := Nat.le_sqrt'.mpr
      ((Nat.pow_le_pow_right hp.pos hk₂).trans hn_le)
    have hklog : k ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by decide)
      ((Nat.pow_le_pow_left hp.two_le k).trans hn_le)
    refine Finset.mem_image.mpr ⟨(p,k), ?_, rfl⟩
    simp [pairs, Nat.lt_succ_iff, hpsqrt, hklog]
  exact (Finset.card_le_card h_subset).trans (Finset.card_image_le.trans (by simp [pairs]))

private theorem natLog_two_le_realLog_div (N : ℕ) (hN : 0 < N) :
    (Nat.log 2 N : ℝ) ≤ Real.log (N : ℝ) / Real.log 2 := by
  have hp : (2 : ℝ) ^ (Nat.log 2 N) ≤ (N : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 hN.ne'
  have hlog := Real.log_le_log (by positivity) hp
  rw [Real.log_pow] at hlog
  exact (le_div_iff₀ (Real.log_pos (by norm_num))).mpr hlog

/-- Quantitative mass bound for the contribution of prime powers above
exponent one. The real square root and logarithm make the decay after
division by (N) explicit. -/
theorem higherPrimePowers_mangoldtMass_le {N : ℕ} (hN : 2 ≤ N) :
    (∑ n ∈ higherPrimePowersThrough N, ArithmeticFunction.vonMangoldt n) ≤
      (4 / Real.log 2) * Real.sqrt (N : ℝ) * (Real.log (N : ℝ)) ^ 2 := by
  have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog_ge : Real.log 2 ≤ Real.log (N : ℝ) :=
    Real.log_le_log (by norm_num) hNr
  have hlog_pos := hlog2.trans_le hlog_ge
  have hSqrt : (Nat.sqrt N : ℝ) ≤ Real.sqrt (N : ℝ) := by
    apply (Real.le_sqrt (by positivity) (by positivity)).mpr
    exact_mod_cast Nat.sqrt_le' N
  have hSqrtOne : 1 ≤ Real.sqrt (N : ℝ) := by
    rw [← Real.sqrt_one]
    apply Real.sqrt_le_sqrt
    linarith
  have hlog_pos_N : 0 < N := by omega
  have hcard : ((higherPrimePowersThrough N).card : ℝ) ≤
      ((Nat.sqrt N : ℝ) + 1) * ((Nat.log 2 N : ℝ) + 1) := by
    exact_mod_cast card_higherPrimePowersThrough_le N
  have hLogSize : (Nat.log 2 N : ℝ) + 1 ≤ 2 * (Real.log (N : ℝ) / Real.log 2) := by
    have hquot : 1 ≤ Real.log (N : ℝ) / Real.log 2 :=
      (le_div_iff₀ hlog2).mpr (by simpa using hlog_ge)
    linarith [natLog_two_le_realLog_div N hlog_pos_N]
  calc
    _ ≤ ∑ _n ∈ higherPrimePowersThrough N, Real.log (N : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      obtain ⟨hm, hp, _⟩ := Finset.mem_filter.mp hn
      have hn_le : n ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hm)
      have hn0 : 0 < n := by
        obtain ⟨p,k,hp',_,rfl⟩ := (isPrimePow_nat_iff n).mp hp
        exact Nat.pow_pos hp'.pos
      exact ArithmeticFunction.vonMangoldt_le_log.trans
        (Real.log_le_log (by positivity) (by exact_mod_cast hn_le))
    _ = ((higherPrimePowersThrough N).card : ℝ) * Real.log (N : ℝ) := by simp
    _ ≤ (((Nat.sqrt N : ℝ) + 1) * ((Nat.log 2 N : ℝ) + 1)) * Real.log (N : ℝ) :=
      mul_le_mul_of_nonneg_right hcard hlog_pos.le
    _ ≤ (2 * Real.sqrt (N : ℝ) * (2 * (Real.log (N : ℝ) / Real.log 2))) *
        Real.log (N : ℝ) := by
      refine mul_le_mul_of_nonneg_right (mul_le_mul ?_ hLogSize (by positivity) (by positivity))
        hlog_pos.le
      linarith
    _ = _ := by ring

/-- Higher prime powers contribute (o(N)) to the Mangoldt mass. -/
theorem tendsto_higherPrimePowers_mangoldtMass_div :
    Tendsto (fun N : ℕ => (∑ n ∈ higherPrimePowersThrough N,
      ArithmeticFunction.vonMangoldt n) / (N : ℝ)) atTop (𝓝 0) := by
  have hL : Tendsto (fun N : ℕ => Real.log (N : ℝ) / (N : ℝ) ^ ((1 : ℝ) / 4))
      atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop
  have hL2 : Tendsto (fun N : ℕ => (4 / Real.log 2) *
      (Real.log (N : ℝ) / (N : ℝ) ^ ((1 : ℝ) / 4)) ^ 2) atTop (𝓝 0) := by
    simpa using (hL.pow 2).const_mul (4 / Real.log 2)
  refine squeeze_zero' (Eventually.of_forall fun N => div_nonneg
    (Finset.sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg) (by positivity)) ?_ hL2
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  calc
    _ ≤ ((4 / Real.log 2) * Real.sqrt (N : ℝ) * (Real.log (N : ℝ)) ^ 2) / (N : ℝ) :=
      div_le_div_of_nonneg_right (higherPrimePowers_mangoldtMass_le hN) hN0.le
    _ = _ := by
      let t := (N : ℝ) ^ ((1 : ℝ) / 4)
      have ht0 : 0 < t := Real.rpow_pos_of_pos hN0 _
      have ht2 : t ^ 2 = Real.sqrt (N : ℝ) := by
        dsimp [t]
        rw [← Real.rpow_mul_natCast hN0.le _ 2, Real.sqrt_eq_rpow]
        norm_num
      have ht4 : t ^ 4 = (N : ℝ) := by
        dsimp [t]
        rw [← Real.rpow_mul_natCast hN0.le _ 4]
        norm_num
      change ((4 / Real.log 2) * Real.sqrt (N : ℝ) * Real.log (N : ℝ) ^ 2) / (N : ℝ) =
        4 / Real.log 2 * (Real.log (N : ℝ) / t) ^ 2
      rw [← ht2, ← ht4]
      field_simp [ht0.ne']
      ring


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The Mangoldt sum restricted to nonprimes is supported on higher prime
powers and costs at most their Mangoldt mass times the summand bound. -/
theorem norm_sub_mangoldt_logPrime_le {u : ℕ → E} {B : ℝ}
    (h_bound : ∀ n, ‖u n‖ ≤ B) (N : ℕ) :
    ‖(N : ℝ)⁻¹ • (∑ n ∈ Finset.range (N + 1), ArithmeticFunction.vonMangoldt n • u n) -
      (N : ℝ)⁻¹ • (∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log (p : ℝ) • u p)‖ ≤
      B * ((∑ n ∈ higherPrimePowersThrough N, ArithmeticFunction.vonMangoldt n) / (N : ℝ)) := by
  classical
  let A := Finset.range (N + 1)
  let B' := higherPrimePowersThrough N
  have h_split :
      (∑ n ∈ A, ArithmeticFunction.vonMangoldt n • u n) -
        (∑ p ∈ A.filter Nat.Prime, Real.log (p : ℝ) • u p) =
      ∑ p ∈ B', ArithmeticFunction.vonMangoldt p • u p := by
    unfold B' higherPrimePowersThrough
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hp : n.Prime
    · simp [hp, ArithmeticFunction.vonMangoldt_apply_prime]
    · by_cases hpp : IsPrimePow n
      · simp [hp, hpp]
      · simp [hp, hpp, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp]
  change ‖(N : ℝ)⁻¹ • (∑ n ∈ A, ArithmeticFunction.vonMangoldt n • u n) -
      (N : ℝ)⁻¹ • (∑ p ∈ A.filter Nat.Prime, Real.log (p : ℝ) • u p)‖ ≤ _
  rw [← smul_sub, h_split, norm_smul, Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ (N : ℝ)⁻¹ * (∑ p ∈ B', ArithmeticFunction.vonMangoldt p * B) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply norm_sum_le_of_le
      intro p hp
      rw [norm_smul, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      exact mul_le_mul_of_nonneg_left (h_bound p) ArithmeticFunction.vonMangoldt_nonneg
    _ = _ := by
      rw [← Finset.sum_mul]
      change (N : ℝ)⁻¹ * ((∑ n ∈ B', ArithmeticFunction.vonMangoldt n) * B) = _
      simp only [div_eq_mul_inv]
      ring

/-- Removing higher prime powers from a convergent Mangoldt average
preserves the limit, for an arbitrary bounded sequence. -/
theorem tendsto_logPrime_of_tendsto_mangoldt {u : ℕ → E} {B : ℝ} {L : E}
    (h_bound : ∀ n, ‖u n‖ ≤ B)
    (h : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ • ∑ n ∈ Finset.range (N + 1),
      ArithmeticFunction.vonMangoldt n • u n) atTop (𝓝 L)) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ • ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime,
      Real.log (p : ℝ) • u p) atTop (𝓝 L) := by
  have h_err : Tendsto
      (fun N : ℕ => (N : ℝ)⁻¹ • (∑ n ∈ Finset.range (N + 1), ArithmeticFunction.vonMangoldt n • u n) -
      (N : ℝ)⁻¹ • (∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log (p : ℝ) • u p))
      atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    refine squeeze_zero (fun _ => norm_nonneg _) (norm_sub_mangoldt_logPrime_le h_bound) ?_
    simpa only [mul_zero] using tendsto_higherPrimePowers_mangoldtMass_div.const_mul B
  simpa only [sub_sub_cancel, sub_zero] using h.sub h_err


/-- Reindexing the average of (Lambda(n+1)a(n+1)), (1 le n le N),
changes just one endpoint of the full Mangoldt sum. Its normalized
contribution vanishes for bounded (a). -/
theorem tendsto_mangoldt_of_tendsto_shifted {u : ℕ → E} {B : ℝ} {L : E}
    (h_bound : ∀ n, ‖u n‖ ≤ B)
    (h : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ • ∑ i ∈ Finset.range N,
      ArithmeticFunction.vonMangoldt (i + 2) • u (i + 2)) atTop (𝓝 L)) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ • ∑ n ∈ Finset.range (N + 1),
      ArithmeticFunction.vonMangoldt n • u n) atTop (𝓝 L) := by
  have h_main : Tendsto (fun N : ℕ => Real.log (N : ℝ) / (N : ℝ)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have h_inv : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have h_upper : Tendsto (fun N : ℕ => B * (Real.log (N : ℝ) + Real.log 2) / (N : ℝ))
      atTop (𝓝 0) := by
    convert (h_main.add (h_inv.const_mul (Real.log 2))).const_mul B using 1
    · funext N
      simp only [div_eq_mul_inv]
      ring
    · simp
  have h_endpoint : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ •
      (ArithmeticFunction.vonMangoldt (N + 1) • u (N + 1))) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h_upper
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hp : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 N
    have hlog := Real.log_le_log ((zero_lt_one : (0 : ℝ) < 1).trans_le hp)
      (show ((N + 1 : ℕ) : ℝ) ≤ 2 * (N : ℝ) by push_cast; linarith)
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity)] at hlog
    simp only [norm_smul, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      Real.norm_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))]
    calc
      _ ≤ (N : ℝ)⁻¹ * ((Real.log (N : ℝ) + Real.log 2) * B) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul ?_ (h_bound _) (norm_nonneg _) ?_) (by positivity)
        · exact ArithmeticFunction.vonMangoldt_le_log.trans (by simpa [add_comm] using hlog)
        · exact add_nonneg (Real.log_nonneg hNr) (Real.log_nonneg (by norm_num))
      _ = _ := by simp only [div_eq_mul_inv]; ring
  have h_sub := h.sub h_endpoint
  rw [sub_zero] at h_sub
  apply h_sub.congr
  intro N
  have h_sum (N : ℕ) :
      (∑ n ∈ Finset.range (N + 2), ArithmeticFunction.vonMangoldt n • u n) =
      ∑ i ∈ Finset.range N, ArithmeticFunction.vonMangoldt (i + 2) • u (i + 2) := by
    simpa [Finset.sum_range_succ, add_comm] using
      (Finset.sum_range_add (fun n => ArithmeticFunction.vonMangoldt n • u n) 2 N)
  rw [← smul_sub, ← h_sum N]
  rw [show N + 2 = N + 1 + 1 by omega, Finset.sum_range_succ, add_sub_cancel_right]

end NilBohr
