import Mathlib

/-!
# From summable comparison estimates to pointwise comparison

This module checks the measure-theoretic and finite-sum steps used in the proof
of Proposition 7.1. Its index starts at zero. A summand at manuscript index
(n) is supplied at index (n-1).
-/

namespace NilBohr

open Filter MeasureTheory
open scoped ENNReal Topology BigOperators

variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]

/-- An absolutely summable series of extended (L^1) norms gives pointwise
convergence to zero outside one null set. -/
theorem ae_tendsto_zero_of_tsum_lintegral_enorm_ne_top {μ : Measure X}
    {F : ℕ → X → E} (hF : ∀ n, AEStronglyMeasurable (F n) μ)
    (h_sum : (∑' n, ∫⁻ x, ‖F n x‖ₑ ∂μ) ≠ ∞) :
    ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 0) := by
  have h_meas (n : ℕ) : AEMeasurable (fun x => ‖F n x‖ₑ) μ := (hF n).enorm
  rw [← lintegral_tsum h_meas] at h_sum
  filter_upwards [ae_lt_top' (AEMeasurable.ennreal_tsum h_meas) h_sum] with x hx
  have h_summable : Summable (fun n => ‖F n x‖) :=
    ENNReal.tsum_coe_ne_top_iff_summable_coe.mp hx.ne
  exact tendsto_zero_iff_norm_tendsto_zero.mpr h_summable.tendsto_atTop_zero

/-- The same criterion expressed with the ordinary (L^1) norms of integrable
functions. -/
theorem ae_tendsto_zero_of_summable_integral_norm {μ : Measure X} {F : ℕ → X → E}
    (hF : ∀ n, Integrable (F n) μ)
    (h_sum : Summable (fun n => ∫ x, ‖F n x‖ ∂μ)) :
    ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 0) := by
  apply ae_tendsto_zero_of_tsum_lintegral_enorm_ne_top (fun n => (hF n).1)
  have h_convert (n : ℕ) : (∫⁻ x, ‖F n x‖ₑ ∂μ) = ‖∫ x, ‖F n x‖ ∂μ‖ₑ := by
    dsimp [enorm]
    rw [lintegral_coe_eq_integral _ (hF n).norm, ENNReal.coe_nnreal_eq, coe_nnnorm,
      Real.norm_of_nonneg (integral_nonneg (fun x => norm_nonneg (F n x)))]
    simp only [coe_nnnorm]
  rw [funext h_convert]
  exact ENNReal.tsum_coe_ne_top_iff_summable.mpr (NNReal.summable_coe.mp h_sum.abs)

/-- A nondecreasing cofinal sequence can be used to check convergence even
when adjacent terms coincide. The comparison estimate is needed only on
the half-open gaps of the sequence. -/
theorem tendsto_zero_of_subsequence_gap {F : ℕ → E} {H : ℕ → ℕ} {gap : ℕ → ℝ}
    (h_mono : Monotone H) (h_top : Tendsto H atTop atTop)
    (h_gap : Tendsto gap atTop (𝓝 0))
    (h_close : ∀ j n, H j ≤ n → n < H (j + 1) → ‖F n - F (H j)‖ ≤ gap j)
    (h_subseq : Tendsto (fun j => F (H j)) atTop (𝓝 0)) :
    Tendsto F atTop (𝓝 0) := by
  classical
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨J₁, h₁⟩ := Metric.tendsto_atTop.mp h_subseq (ε / 2) (by positivity)
  obtain ⟨J₂, h₂⟩ := Metric.tendsto_atTop.mp h_gap (ε / 2) (by positivity)
  let J := max J₁ J₂
  refine ⟨H J, ?_⟩
  intro n hn
  have h_ex : ∃ j, n < H j := (h_top.eventually (eventually_gt_atTop n)).exists
  let j := Nat.find h_ex
  have hj : n < H j := Nat.find_spec h_ex
  have h_pos : 0 < j := by
    by_contra! h
    have h_eq : j = 0 := by omega
    exact (not_lt_of_ge (le_trans (h_mono (Nat.zero_le J)) hn)) (h_eq ▸ hj)
  let i := j - 1
  have hi_succ : i + 1 = j := by dsimp [i]; omega
  have hi_lt : n < H (i + 1) := by simpa only [hi_succ] using hj
  have hi_le : H i ≤ n := by
    apply le_of_not_gt
    exact Nat.find_min h_ex (by dsimp [i]; omega)
  have hJi : J ≤ i := by
    by_contra! h
    exact (not_lt_of_ge (le_trans (h_mono (Nat.succ_le_of_lt h)) hn)) hi_lt
  have ha := h₁ i (le_trans (le_max_left J₁ J₂) hJi)
  have hb := h₂ i (le_trans (le_max_right J₁ J₂) hJi)
  rw [dist_zero_right] at ha ⊢
  rw [Real.dist_eq, sub_zero] at hb
  have hc := h_close i n hi_le hi_lt
  calc
    ‖F n‖ = ‖(F n - F (H i)) + F (H i)‖ := by rw [sub_add_cancel]
    _ ≤ ‖F n - F (H i)‖ + ‖F (H i)‖ := norm_add_le _ _
    _ < ε := by linarith [le_abs_self (gap i)]

variable [NormedSpace ℝ E]

/-- The arithmetic average of the first (N) terms of a sequence. -/
noncomputable def prefixAverage (u : ℕ → E) (N : ℕ) : E :=
  (N : ℝ)⁻¹ • ∑ i ∈ Finset.range N, u i

/-- Changing the length of the average entails both deleting the tail and
renormalizing the retained terms. The larger length in the denominator
makes the bound slightly sharper than the bound used in Proposition 7.1. -/
theorem norm_sub_prefixAverage_le {u : ℕ → E} {N M : ℕ} {B : ℝ}
    (hN : 0 < N) (hNM : N ≤ M) (hB : ∀ i < M, ‖u i‖ ≤ B) :
    ‖prefixAverage u M - prefixAverage u N‖ ≤
      2 * ((M - N : ℕ) : ℝ) / (M : ℝ) * B := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hMr : 0 < (M : ℝ) := by exact_mod_cast (hN.trans_le hNM)
  have hNMr : (N : ℝ) ≤ (M : ℝ) := by exact_mod_cast hNM
  let S := ∑ i ∈ Finset.range N, u i
  let R := ∑ i ∈ Finset.range (M - N), u (N + i)
  have hS : ‖S‖ ≤ (N : ℝ) * B := by
    calc
      ‖S‖ ≤ ∑ i ∈ Finset.range N, ‖u i‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ Finset.range N, B :=
        Finset.sum_le_sum fun i hi => hB i ((Finset.mem_range.mp hi).trans_le hNM)
      _ = _ := by simp
  have hR : ‖R‖ ≤ ((M - N : ℕ) : ℝ) * B := by
    calc
      ‖R‖ ≤ ∑ i ∈ Finset.range (M - N), ‖u (N + i)‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ Finset.range (M - N), B := by
        apply Finset.sum_le_sum
        intro i hi
        have := Finset.mem_range.mp hi
        exact hB _ (by omega)
      _ = _ := by simp
  have h_split : (∑ i ∈ Finset.range M, u i) = S + R := by
    simpa [S, R, Nat.add_sub_of_le hNM] using (Finset.sum_range_add u N (M - N))
  have h_inv : (M : ℝ)⁻¹ ≤ (N : ℝ)⁻¹ := inv_anti₀ hNr hNMr
  unfold prefixAverage
  rw [h_split, smul_add, add_sub_right_comm, ← sub_smul]
  calc
    ‖((M : ℝ)⁻¹ - (N : ℝ)⁻¹) • S + (M : ℝ)⁻¹ • R‖ ≤
        ‖((M : ℝ)⁻¹ - (N : ℝ)⁻¹) • S‖ + ‖(M : ℝ)⁻¹ • R‖ := norm_add_le _ _
    _ ≤ |(M : ℝ)⁻¹ - (N : ℝ)⁻¹| * ((N : ℝ) * B) +
        |(M : ℝ)⁻¹| * (((M - N : ℕ) : ℝ) * B) := by
      simp only [norm_smul, Real.norm_eq_abs]
      exact add_le_add
        (mul_le_mul_of_nonneg_left hS (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hR (abs_nonneg _))
    _ = _ := by
      rw [abs_of_nonpos (sub_nonpos.mpr h_inv), abs_of_nonneg (by positivity), Nat.cast_sub hNM]
      field_simp
      ring

/-- From summable (L^1) bounds at sample lengths to almost-everywhere
convergence at every length. The input envelope (B) may grow with the
length. For Proposition 7.1 the envelope is a constant times (log(H+2)). -/
theorem ae_tendsto_zero_prefixAverage_of_summable_subsequence {μ : Measure X}
    {u : ℕ → X → E} {H : ℕ → ℕ} {B : ℕ → ℝ}
    (h_pos : ∀ j, 0 < H j) (h_mono : Monotone H) (h_top : Tendsto H atTop atTop)
    (h_nonneg : ∀ n, 0 ≤ B n) (h_Bmono : Monotone B)
    (h_bound : ∀ᵐ x ∂μ, ∀ n i, i < n → ‖u i x‖ ≤ B n)
    (h_gap : Tendsto (fun j => 2 * ((H (j + 1) - H j : ℕ) : ℝ) /
        (H j : ℝ) * B (H (j + 1))) atTop (𝓝 0))
    (h_int : ∀ j, Integrable (fun x => prefixAverage (fun i => u i x) (H j)) μ)
    (h_sum : Summable (fun j => ∫ x, ‖prefixAverage (fun i => u i x) (H j)‖ ∂μ)) :
    ∀ᵐ x ∂μ, Tendsto (fun n => prefixAverage (fun i => u i x) n) atTop (𝓝 0) := by
  filter_upwards [h_bound, ae_tendsto_zero_of_summable_integral_norm h_int h_sum]
    with x hx h_subseq
  apply tendsto_zero_of_subsequence_gap h_mono h_top h_gap (fun j n h₁ h₂ => ?_) h_subseq
  calc
    ‖prefixAverage (fun i => u i x) n - prefixAverage (fun i => u i x) (H j)‖ ≤
        2 * ((n - H j : ℕ) : ℝ) / (n : ℝ) * B n :=
      norm_sub_prefixAverage_le (h_pos j) h₁ (hx n)
    _ ≤ 2 * ((H (j + 1) - H j : ℕ) : ℝ) / (H j : ℝ) * B (H (j + 1)) := by
      have h_cast : ((n - H j : ℕ) : ℝ) ≤ ((H (j + 1) - H j : ℕ) : ℝ) := by
        exact_mod_cast Nat.sub_le_sub_right h₂.le (H j)
      have h_pos_cast : 0 < (H j : ℝ) := by exact_mod_cast h_pos j
      have h_den : (H j : ℝ) ≤ (n : ℝ) := by exact_mod_cast h₁
      exact mul_le_mul
        (div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left h_cast (by norm_num))
          h_pos_cast h_den)
        (h_Bmono h₂.le) (h_nonneg n) (by positivity)


private noncomputable def sampleRoot (j : ℕ) : ℝ :=
  ((j : ℝ) + 1) ^ ((1 : ℝ) / 3)

/-- The subsequence in Proposition 7.1, with the indices beginning at (j=1). -/
noncomputable def logarithmicSampleLength (j : ℕ) : ℕ :=
  ⌊Real.exp (sampleRoot j)⌋₊

private theorem sampleRoot_one_le (j : ℕ) : 1 ≤ sampleRoot j :=
  Real.one_le_rpow (le_add_of_nonneg_left (Nat.cast_nonneg j)) (by norm_num)

private theorem sampleRoot_mono : Monotone sampleRoot := by
  intro i j hij
  apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
  exact add_le_add_right (by exact_mod_cast hij) 1

private theorem sampleRoot_cube (j : ℕ) : sampleRoot j ^ 3 = (j : ℝ) + 1 := by
  unfold sampleRoot
  rw [← Real.rpow_mul_natCast (by positivity) _ 3]
  norm_num

private theorem sampleRoot_tendsto : Tendsto sampleRoot atTop atTop := by
  exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
    (tendsto_atTop_mono (fun (j : ℕ) => by
      show (j : ℝ) ≤ j + 1
      linarith) tendsto_natCast_atTop_atTop)

private theorem exp_sampleRoot_two_le (j : ℕ) : (2 : ℝ) ≤ Real.exp (sampleRoot j) := by
  have := Real.quadratic_le_exp_of_nonneg ((zero_le_one : (0 : ℝ) ≤ 1).trans (sampleRoot_one_le j))
  nlinarith [sampleRoot_one_le j, sq_nonneg (sampleRoot j)]

private theorem sampleLength_two_le (j : ℕ) : 2 ≤ logarithmicSampleLength j := by
  apply (Nat.le_floor_iff (Real.exp_pos _).le).mpr
  exact exp_sampleRoot_two_le j

private theorem sampleLength_mono : Monotone logarithmicSampleLength :=
  Nat.floor_mono.comp (Real.exp_monotone.comp sampleRoot_mono)

private theorem sampleLength_tendsto : Tendsto logarithmicSampleLength atTop atTop :=
  tendsto_nat_floor_atTop.comp (Real.tendsto_exp_atTop.comp sampleRoot_tendsto)

private theorem half_exp_le_sampleLength (j : ℕ) :
    Real.exp (sampleRoot j) / 2 ≤ (logarithmicSampleLength j : ℝ) := by
  have h_round := Nat.lt_floor_add_one (Real.exp (sampleRoot j))
  have h_two := exp_sampleRoot_two_le j
  change _ ≤ (⌊Real.exp (sampleRoot j)⌋₊ : ℝ)
  linarith

private theorem log_sampleLength_lower (j : ℕ) :
    sampleRoot j / 4 ≤ Real.log (logarithmicSampleLength j) := by
  have hlog := Real.log_le_log (by positivity) (half_exp_le_sampleLength j)
  rw [Real.log_div (Real.exp_pos _).ne' (by norm_num), Real.log_exp] at hlog
  linarith [sampleRoot_one_le j, Real.log_two_lt_d9]

private theorem log_sampleLength_upper (j : ℕ) :
    Real.log ((logarithmicSampleLength j : ℝ) + 2) ≤ sampleRoot j + 2 := by
  have hf : (logarithmicSampleLength j : ℝ) ≤ Real.exp (sampleRoot j) :=
    Nat.floor_le (Real.exp_pos _).le
  have ht := exp_sampleRoot_two_le j
  have hlog := Real.log_le_log
    (show 0 < (logarithmicSampleLength j : ℝ) + 2 by positivity)
    (show (logarithmicSampleLength j : ℝ) + 2 ≤ 3 * Real.exp (sampleRoot j) by linarith)
  rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at hlog
  linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)]

private theorem logarithmicSampleLength_gap_bound (j : ℕ) :
    2 * ((logarithmicSampleLength (j + 1) - logarithmicSampleLength j : ℕ) : ℝ) /
      (logarithmicSampleLength j : ℝ) *
      Real.log ((logarithmicSampleLength (j + 1) : ℝ) + 2) ≤
        64 * (sampleRoot j)⁻¹ := by
  let a := sampleRoot j
  let b := sampleRoot (j + 1)
  let d := b - a
  have ha : 1 ≤ a := sampleRoot_one_le j
  have hb : a ≤ b := sampleRoot_mono (Nat.le_succ j)
  have hd₀ : 0 ≤ d := sub_nonneg.mpr hb
  have ha₀ : 0 < a := zero_lt_one.trans_le ha
  have hcubes : b ^ 3 - a ^ 3 = 1 := by
    dsimp [a, b]
    rw [sampleRoot_cube, sampleRoot_cube, Nat.cast_add, Nat.cast_one]
    ring
  have hd_id : d * (b ^ 2 + b * a + a ^ 2) = 1 := by
    linear_combination hcubes
  have hd_mul : d * a ^ 2 ≤ 1 := by
    rw [← hd_id]
    exact mul_le_mul_of_nonneg_left (by
      have hba : 0 ≤ b * a := mul_nonneg (ha₀.le.trans hb) ha₀.le
      nlinarith [sq_nonneg b]) hd₀
  have hd : d ≤ 1 / a ^ 2 := (le_div_iff₀ (by positivity)).mpr hd_mul
  have hd₁ : d ≤ 1 := hd.trans ((div_le_iff₀ (by positivity)).mpr (by nlinarith))
  have h_exp_sub : Real.exp d - 1 ≤ 2 * d := by
    have h := Real.abs_exp_sub_one_le (show |d| ≤ 1 by rwa [abs_of_nonneg hd₀])
    rw [abs_of_nonneg hd₀] at h
    exact (le_abs_self _).trans h
  have h_exp_diff : Real.exp b - Real.exp a ≤ 2 * d * Real.exp a := by
    calc
      Real.exp b - Real.exp a = (Real.exp d - 1) * Real.exp a := by
        rw [sub_mul, one_mul, ← Real.exp_add]
        simp [d]
      _ ≤ _ := mul_le_mul_of_nonneg_right h_exp_sub (Real.exp_pos _).le
  have h_inv : (Real.exp a)⁻¹ ≤ 2 / a ^ 2 := by
    rw [inv_eq_one_div]
    apply (div_le_div_iff₀ (Real.exp_pos _) (by positivity)).mpr
    nlinarith [Real.quadratic_le_exp_of_nonneg ha₀.le]
  let L := logarithmicSampleLength j
  let U := logarithmicSampleLength (j + 1)
  have hUL : L ≤ U := sampleLength_mono (Nat.le_succ j)
  have hfloor : (U : ℝ) ≤ Real.exp b := Nat.floor_le (Real.exp_pos _).le
  have hround : Real.exp a < (L : ℝ) + 1 := Nat.lt_floor_add_one _
  have hdiff : ((U - L : ℕ) : ℝ) ≤ 2 * d * Real.exp a + 1 := by
    rw [Nat.cast_sub hUL]
    linarith
  have hratio : 2 * ((U - L : ℕ) : ℝ) / (L : ℝ) ≤ 16 / a ^ 2 := by
    calc
      _ ≤ 2 * (2 * d * Real.exp a + 1) / (Real.exp a / 2) := div_le_div₀
        (by positivity) (mul_le_mul_of_nonneg_left hdiff (by norm_num))
        (by positivity) (half_exp_le_sampleLength j)
      _ = 8 * d + 4 * (Real.exp a)⁻¹ := by
        field_simp
        ring
      _ ≤ _ := by
        simp only [div_eq_mul_inv, one_mul] at hd h_inv ⊢
        linarith only [hd, h_inv]
  have hlog : Real.log ((U : ℝ) + 2) ≤ 4 * a := by
    have h := log_sampleLength_upper (j + 1)
    change Real.log ((U : ℝ) + 2) ≤ b + 2 at h
    dsimp [d] at hd₁
    linarith
  calc
    _ ≤ 16 / a ^ 2 * (4 * a) :=
      mul_le_mul hratio hlog (Real.log_nonneg (by linarith [show (0 : ℝ) ≤ (U : ℝ) by positivity]))
        (by positivity)
    _ = _ := by
      field_simp
      ring

/-- Proposition 7.1's passage from logarithmic (L^1) decay and a logarithmic
pointwise envelope for the summands to almost-everywhere convergence.
The exponent 6 is a convenient instance of the manuscript's (A>3). -/
theorem ae_tendsto_zero_prefixAverage_of_log_decay {μ : Measure X}
    {u : ℕ → X → E} {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (h_bound : ∀ᵐ x ∂μ, ∀ n i, i < n → ‖u i x‖ ≤ D * Real.log ((n : ℝ) + 2))
    (h_int : ∀ n, Integrable (fun x => prefixAverage (fun i => u i x) n) μ)
    (h_L1 : ∀ n ≥ 2, (∫ x, ‖prefixAverage (fun i => u i x) n‖ ∂μ)
        ≤ C / (Real.log (n : ℝ)) ^ 6) :
    ∀ᵐ x ∂μ, Tendsto (fun n => prefixAverage (fun i => u i x) n) atTop (𝓝 0) := by
  refine ae_tendsto_zero_prefixAverage_of_summable_subsequence
      (H := logarithmicSampleLength) (B := fun n => D * Real.log ((n : ℝ) + 2))
      (fun j => lt_of_lt_of_le (by decide : 0 < 2) (sampleLength_two_le j))
      sampleLength_mono sampleLength_tendsto (fun n => ?_) (fun i j hij => ?_)
      h_bound ?_ (fun j => h_int (logarithmicSampleLength j)) ?_
  · exact mul_nonneg hD (Real.log_nonneg (by linarith [show (0 : ℝ) ≤ (n : ℝ) by positivity]))
  · exact mul_le_mul_of_nonneg_left
      (Real.log_le_log (by positivity) (add_le_add_right (by exact_mod_cast hij) 2)) hD
  · have h_inv := (tendsto_inv_atTop_zero.comp sampleRoot_tendsto).const_mul (64 * D)
    have h_inv' : Tendsto (fun j => (64 * D) * (sampleRoot j)⁻¹) atTop (𝓝 0) := by
      simpa only [mul_zero] using h_inv
    refine squeeze_zero (fun j => ?_) (fun j => ?_) h_inv'
    · exact mul_nonneg (by positivity)
        (mul_nonneg hD (Real.log_nonneg (by
          linarith [show (0 : ℝ) ≤ (logarithmicSampleLength (j + 1) : ℝ) by positivity])))
    · convert mul_le_mul_of_nonneg_left (logarithmicSampleLength_gap_bound j) hD using 1 <;> ring
  · have hp : Summable (fun j : ℕ => (j : ℝ) ^ (-2 : ℝ)) :=
      Real.summable_nat_rpow.mpr (by norm_num)
    have hp' : Summable (fun j : ℕ => ((j : ℝ) + 1) ^ (-2 : ℝ)) := by
      simpa only [Nat.cast_succ] using (summable_nat_add_iff 1).mpr hp
    refine Summable.of_nonneg_of_le (f := fun j : ℕ => (C * 4 ^ 6) * ((j : ℝ) + 1) ^ (-2 : ℝ))
      (fun _ => integral_nonneg fun _ => norm_nonneg _) (fun j => ?_) (hp'.mul_left _)
    have hu : 0 < sampleRoot j := zero_lt_one.trans_le (sampleRoot_one_le j)
    calc
      _ ≤ C / Real.log (logarithmicSampleLength j) ^ 6 :=
        h_L1 _ (sampleLength_two_le j)
      _ ≤ C / (sampleRoot j / 4) ^ 6 := by
        apply div_le_div_of_nonneg_left hC (by positivity)
        exact pow_le_pow_left₀ (by positivity) (log_sampleLength_lower j) _
      _ = (C * 4 ^ 6) * ((j : ℝ) + 1) ^ (-2 : ℝ) := by
        rw [Real.rpow_neg (by positivity), Real.rpow_two, ← sampleRoot_cube j]
        field_simp [hu.ne']
        ring_nf
        simp

/-- The normalized sum over a finite set. In particular it is zero for an
empty set, while all results dividing by its size require nonemptiness. -/
noncomputable def finsetAverage {ι : Type*} (s : Finset ι) (u : ι → E) : E :=
  (s.card : ℝ)⁻¹ • ∑ i ∈ s, u i

/-- Replacing scalar weights bounded above by one with the constant weight
one costs at most their total deficit times a bound for the summands. -/
theorem norm_sub_finsetAverage_weighted_le {ι : Type*} {s : Finset ι}
    {u : ι → E} {w : ι → ℝ} {B : ℝ}
    (hs : 0 < s.card) (hu : ∀ i ∈ s, ‖u i‖ ≤ B)
    (hw : ∀ i ∈ s, w i ≤ 1) :
    ‖finsetAverage s u - finsetAverage s (fun i => w i • u i)‖ ≤
      B * (1 - (s.card : ℝ)⁻¹ * ∑ i ∈ s, w i) := by
  have hs' : 0 < (s.card : ℝ) := by exact_mod_cast hs
  have hsum :
      ‖∑ i ∈ s, (u i - w i • u i)‖ ≤ ∑ i ∈ s, (1 - w i) * B := by
    apply norm_sum_le_of_le
    intro i hi
    calc
      ‖u i - w i • u i‖ = (1 - w i) * ‖u i‖ := by
        rw [show u i - w i • u i = (1 - w i) • u i by rw [sub_smul, one_smul],
          norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (hw i hi))]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hu i hi) (sub_nonneg.mpr (hw i hi))
  unfold finsetAverage
  rw [← smul_sub, ← Finset.sum_sub_distrib, norm_smul, Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ (s.card : ℝ)⁻¹ * ∑ i ∈ s, (1 - w i) * B :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by
      rw [← Finset.sum_mul, Finset.sum_sub_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      field_simp
      ring

/-- An average whose scalar weights tend to mass one and are at most one
has the same limit as the corresponding unweighted average for bounded
summands. For prime sums the weights are (log p/log N). -/
theorem tendsto_finsetAverage_of_weighted {ι : Type*} {s : ℕ → Finset ι}
    {u : ι → E} {w : ℕ → ι → ℝ} {B : ℝ} {L : E}
    (hs : ∀ᶠ n in atTop, 0 < (s n).card)
    (hu : ∀ i, ‖u i‖ ≤ B) (hw : ∀ᶠ n in atTop, ∀ i ∈ s n, w n i ≤ 1)
    (h_mass : Tendsto (fun n => ((s n).card : ℝ)⁻¹ * ∑ i ∈ s n, w n i) atTop (𝓝 1))
    (h_weighted : Tendsto (fun n => finsetAverage (s n) (fun i => w n i • u i))
      atTop (𝓝 L)) :
    Tendsto (fun n => finsetAverage (s n) u) atTop (𝓝 L) := by
  have h_deficit : Tendsto (fun n => B *
      (1 - ((s n).card : ℝ)⁻¹ * ∑ i ∈ s n, w n i)) atTop (𝓝 0) := by
    have h_one : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    simpa only [sub_self, mul_zero] using (h_one.sub h_mass).const_mul B
  have h_error : Tendsto (fun n => finsetAverage (s n) u -
      finsetAverage (s n) (fun i => w n i • u i)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall (fun n => norm_nonneg _)) ?_ h_deficit
    filter_upwards [hs, hw] with n hn hwn
    exact norm_sub_finsetAverage_weighted_le hn (fun i _ => hu i) hwn
  simpa only [sub_add_cancel, zero_add] using h_error.add h_weighted


/-- Remove logarithmic weights from a bounded sequence over a family of
finite subsets of ([N]). For the primes, the two scalar inputs are the
prime number theorem in its counting and Chebyshev-theta formulations.
This proves the normalization implication directly using nonnegative
weight deficits, with no appeal to an integral summation formula. -/
theorem tendsto_finsetAverage_of_tendsto_logWeighted {s : ℕ → Finset ℕ}
    {u : ℕ → E} {B : ℝ} {L : E} (hu : ∀ i, ‖u i‖ ≤ B)
    (hs : ∀ n i, i ∈ s n → i ≤ n)
    (h_count : Tendsto (fun n => ((s n).card : ℝ) * Real.log (n : ℝ) / n) atTop (𝓝 1))
    (h_logMass : Tendsto (fun n => (∑ i ∈ s n, Real.log (i : ℝ)) / n) atTop (𝓝 1))
    (h_sum : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ s n, Real.log (i : ℝ) • u i)
      atTop (𝓝 L)) :
    Tendsto (fun n => finsetAverage (s n) u) atTop (𝓝 L) := by
  have h_count_ne : ∀ᶠ n in atTop, ((s n).card : ℝ) * Real.log (n : ℝ) / n ≠ 0 :=
    h_count.eventually_ne (by norm_num : (1 : ℝ) ≠ 0)
  refine tendsto_finsetAverage_of_weighted
    (s := s) (w := fun n i => Real.log (i : ℝ) / Real.log (n : ℝ)) ?_ hu ?_ ?_ ?_
  · filter_upwards [h_count_ne] with n hn
    apply Nat.pos_of_ne_zero
    intro hz
    apply hn
    simp [hz]
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn i hi
    have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hn'
    apply (div_le_one hlog).mpr
    by_cases hi₀ : i = 0
    · simpa [hi₀] using hlog.le
    · exact Real.log_le_log (by positivity) (by exact_mod_cast hs n i hi)
  · have h := h_logMass.div h_count (by norm_num : (1 : ℝ) ≠ 0)
    rw [div_self (by norm_num : (1 : ℝ) ≠ 0)] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop (2 : ℕ), h_count_ne] with n hn hne
    have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hn'
    have hc : ((s n).card : ℝ) ≠ 0 := by
      intro hz
      apply hne
      simp [hz]
    rw [← Finset.sum_div]
    field_simp
  · have h := (h_count.inv₀ (by norm_num : (1 : ℝ) ≠ 0)).smul h_sum
    simp only [inv_one, one_smul] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop (2 : ℕ), h_count_ne] with n hn hne
    have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hn'
    have hc : ((s n).card : ℝ) ≠ 0 := by
      intro hz
      apply hne
      simp [hz]
    unfold finsetAverage
    simp_rw [div_eq_mul_inv, mul_comm (Real.log (_ : ℝ)) (Real.log (n : ℝ))⁻¹, mul_smul,
      ← Finset.smul_sum, smul_smul]
    congr 1
    field_simp
    ring

end NilBohr
