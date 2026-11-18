import NilBohr.SeparatingQuadraticLimit

/-! Finite linear phase estimates for the divisor sums in the Cramér sieve. -/

open scoped BigOperators

namespace NilBohr

private theorem sum_nat_Icc_eq_range (N : ℕ) (f : ℕ → ℂ) :
    (∑ n ∈ Finset.Icc 1 N, f n) = ∑ j ∈ Finset.range N, f (j + 1) := by
  have hset : Finset.Icc 1 N = (Finset.range N).image (fun j => j + 1) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨hn, hnN⟩
      exact ⟨n - 1, by omega, by omega⟩
    · rintro ⟨j, hj, rfl⟩
      omega
  rw [hset, Finset.sum_image (fun _ _ _ _ h => Nat.add_right_cancel h)]

/-- The positive multiples of `d` through `N` are the first `N / d`
positive multiples, including the endpoint when `d` divides `N`. -/
theorem sum_multiples_Icc {A : Type*} [AddCommMonoid A] (N d : ℕ) (hd : 0 < d) (f : ℕ → A) :
    (∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n), f n) =
      ∑ j ∈ Finset.range (N / d), f (d * (j + 1)) := by
  have hset : (Finset.Icc 1 N).filter (fun n => d ∣ n) =
      (Finset.range (N / d)).image (fun j => d * (j + 1)) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨⟨hn, hnN⟩, m, rfl⟩
      have hm : 0 < m := by by_contra h; simp [Nat.eq_zero_of_not_pos h] at hn
      have hmN : m ≤ N / d := (Nat.le_div_iff_mul_le hd).2 (by rwa [Nat.mul_comm])
      refine ⟨m - 1, by omega, ?_⟩
      congr 1
      omega
    · rintro ⟨j, hj, rfl⟩
      refine ⟨⟨Nat.mul_pos hd (Nat.succ_pos j), ?_⟩, dvd_mul_right _ _⟩
      rw [Nat.mul_comm]
      exact (Nat.le_div_iff_mul_le hd).1 (by omega)
  rw [hset, Finset.sum_image]
  intro _ _ _ _ h
  exact Nat.add_right_cancel (Nat.eq_of_mul_eq_mul_left hd h)

/-- A finite geometric progression, in the interval and divisor
conventions of the sieve. -/
theorem norm_sum_phase_multiples_mul_torusNorm_le (N d : ℕ) (hd : 0 < d) (α : ℝ) :
    ‖∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n), phase (α * (n : ℝ))‖ *
      torusNorm (α * (d : ℝ)) ≤ 1 := by
  rw [sum_multiples_Icc N d hd]
  let H := N / d
  let F (j : ℕ) := phase (α * (d : ℝ) * (j : ℝ) + α * (d : ℝ))
  have hterm (j : ℕ) : phase (α * ((d * (j + 1) : ℕ) : ℝ)) = F j := by
    dsimp only [F]
    push_cast
    congr 1
    ring
  simp only [hterm]
  change ‖∑ j ∈ Finset.range H, F j‖ * torusNorm (α * (d : ℝ)) ≤ 1
  have h := norm_prefixAverage_linear_mul_torusNorm_le H (α * (d : ℝ)) (α * (d : ℝ))
  by_cases hH : H = 0
  · simp [hH]
  · have hH' : (H : ℝ) ≠ 0 := by exact_mod_cast hH
    have heq : prefixAverage F H = (∑ j ∈ Finset.range H, F j) / (H : ℂ) := by
      simp [prefixAverage, Complex.real_smul, div_eq_inv_mul]
    change ‖prefixAverage F H‖ * ((H : ℝ) * torusNorm (α * (d : ℝ))) ≤ 1 at h
    rw [heq, norm_div, Complex.norm_natCast, ← mul_assoc, div_mul_cancel₀ _ hH'] at h
    exact h

/-- If the common ratio is at least `1 / (2q)` from an integer,
the unnormalized geometric sum is at most `2q`. -/
theorem norm_sum_phase_multiples_le_of_frequency (N d q : ℕ) (hd : 0 < d) (hq : 0 < q)
    (α : ℝ) (hα : (2 * (q : ℝ))⁻¹ ≤ torusNorm (α * (d : ℝ))) :
    ‖∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n), phase (α * (n : ℝ))‖ ≤
      2 * (q : ℝ) := by
  have hq' : 0 < (2 : ℝ) * q := by positivity
  have h := mul_le_mul_of_nonneg_left hα
    (norm_nonneg (∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n), phase (α * (n : ℝ))))
  have hle : ‖∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n), phase (α * (n : ℝ))‖ /
      (2 * (q : ℝ)) ≤ 1 := by
    simpa only [div_eq_mul_inv] using
      h.trans (norm_sum_phase_multiples_mul_torusNorm_le N d hd α)
  have hb := (div_le_iff₀ hq').mp hle
  rwa [one_mul] at hb

private theorem inv_denominator_le_torusNorm_mul_rational {q d : ℕ} (hq : 0 < q)
    {a : ℤ} (ha : a.natAbs.Coprime q) (hqd : ¬ q ∣ d) :
    (q : ℝ)⁻¹ ≤ torusNorm (((a : ℝ) / (q : ℝ)) * (d : ℝ)) := by
  let t := ((a : ℝ) / (q : ℝ)) * (d : ℝ)
  let m := round t
  let k : ℤ := a * (d : ℤ) - (q : ℤ) * m
  have hq' : 0 < (q : ℝ) := Nat.cast_pos.mpr hq
  have hk : k ≠ 0 := by
    intro h0
    have heq : a * (d : ℤ) = (q : ℤ) * m := sub_eq_zero.mp h0
    have hdiv : (q : ℤ) ∣ a * (d : ℤ) := ⟨m, heq⟩
    have hdiv' := Int.natAbs_dvd_natAbs.mpr hdiv
    rw [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast] at hdiv'
    exact hqd (ha.symm.dvd_of_dvd_mul_left hdiv')
  have habs : 1 ≤ |(k : ℝ)| := by
    rw [← Int.cast_abs, ← Int.cast_natAbs]
    exact_mod_cast (Int.natAbs_pos.mpr hk)
  have heq : |(k : ℝ)| = (q : ℝ) * torusNorm t := by
    rw [torusNorm_eq]
    change |(k : ℝ)| = (q : ℝ) * |t - (m : ℝ)|
    rw [← abs_of_nonneg hq'.le, ← abs_mul]
    congr 1
    dsimp only [k, t]
    push_cast
    field_simp
  rw [heq] at habs
  exact (inv_le_iff_one_le_mul₀ hq').mpr (by simpa only [mul_comm] using habs)

/-- A reduced approximation has well-separated common ratios off
the multiples of its denominator, as long as the divisor is at most
half the Dirichlet scale. -/
theorem torusNorm_mul_ge_inv_two_denominator {q d R : ℕ} (hq : 0 < q) (hR : 0 < R)
    (hdR : 2 * d ≤ R) {a : ℤ} (ha : a.natAbs.Coprime q) (hqd : ¬ q ∣ d)
    {α : ℝ} (happrox : |α - (a : ℝ) / (q : ℝ)| ≤ 1 / ((q : ℝ) * (R : ℝ))) :
    (2 * (q : ℝ))⁻¹ ≤ torusNorm (α * (d : ℝ)) := by
  let t := (a : ℝ) / (q : ℝ)
  have hq' : 0 < (q : ℝ) := Nat.cast_pos.mpr hq
  have hR' : 0 < (R : ℝ) := Nat.cast_pos.mpr hR
  have hd' : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
  have hdR' : 2 * (d : ℝ) ≤ (R : ℝ) := by exact_mod_cast hdR
  have hRat : (q : ℝ)⁻¹ ≤ torusNorm (t * (d : ℝ)) :=
    inv_denominator_le_torusNorm_mul_rational hq ha hqd
  have hdist : torusNorm (t * (d : ℝ) - α * (d : ℝ)) ≤ (2 * (q : ℝ))⁻¹ := calc
    _ ≤ |t * (d : ℝ) - α * (d : ℝ)| := torusNorm_le_abs _
    _ = |α - t| * (d : ℝ) := by rw [← sub_mul, abs_mul, abs_of_nonneg hd', abs_sub_comm]
    _ ≤ (1 / ((q : ℝ) * (R : ℝ))) * (d : ℝ) := mul_le_mul_of_nonneg_right happrox hd'
    _ ≤ _ := by
      rw [one_div_mul_eq_div, ← one_div]
      apply (div_le_div_iff₀ (mul_pos hq' hR') (by positivity)).2
      linear_combination mul_le_mul_of_nonneg_right hdR' hq'.le
  have hsum : torusNorm (t * (d : ℝ)) ≤
      torusNorm (t * (d : ℝ) - α * (d : ℝ)) + torusNorm (α * (d : ℝ)) := by
    simpa only [sub_add_cancel] using torusNorm_add_le (t * (d : ℝ) - α * (d : ℝ)) (α * (d : ℝ))
  have heq : (q : ℝ)⁻¹ = 2 * (2 * (q : ℝ))⁻¹ := by field_simp
  linarith only [hRat, hdist, hsum, heq]

private theorem norm_block_endpoints_sub_sum (d : ℕ) {C : ℝ} (hC : 0 ≤ C) (f : ℕ → ℂ)
    (hf : ∀ n m : ℕ, ‖f n - f m‖ ≤ C * |(n : ℝ) - (m : ℝ)|) (m : ℕ) :
    ‖(d : ℂ) * (∑ j ∈ Finset.range m, f (d * (j + 1))) -
      (∑ i ∈ Finset.range (m * d), f (i + 1))‖ ≤ C * (d : ℝ)^2 * (m : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hblock : ‖(d : ℂ) * f (d * (m + 1)) -
        (∑ i ∈ Finset.range d, f (m * d + i + 1))‖ ≤ C * (d : ℝ)^2 := by
      have heq : (d : ℂ) * f (d * (m + 1)) = ∑ _i ∈ Finset.range d, f (d * (m + 1)) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [heq, ← Finset.sum_sub_distrib]
      calc
        _ ≤ ∑ i ∈ Finset.range d, ‖f (d * (m + 1)) - f (m * d + i + 1)‖ :=
          norm_sum_le _ _
        _ ≤ ∑ _i ∈ Finset.range d, C * (d : ℝ) := by
          apply Finset.sum_le_sum
          intro i hi
          have hi' : (i : ℝ) + 1 ≤ (d : ℝ) := by
            exact_mod_cast (Nat.succ_le_of_lt (Finset.mem_range.mp hi))
          apply (hf _ _).trans
          apply mul_le_mul_of_nonneg_left _ hC
          push_cast
          rw [abs_of_nonneg (by nlinarith)]
          nlinarith
        _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    rw [Finset.sum_range_succ, Nat.succ_mul, Finset.sum_range_add, mul_add]
    rw [show (d : ℂ) * (∑ j ∈ Finset.range m, f (d * (j + 1))) +
        (d : ℂ) * f (d * (m + 1)) -
        ((∑ i ∈ Finset.range (m * d), f (i + 1)) +
          ∑ i ∈ Finset.range d, f (m * d + i + 1)) =
        ((d : ℂ) * (∑ j ∈ Finset.range m, f (d * (j + 1))) -
          (∑ i ∈ Finset.range (m * d), f (i + 1))) +
        ((d : ℂ) * f (d * (m + 1)) -
          (∑ i ∈ Finset.range d, f (m * d + i + 1))) by ring]
    exact (norm_add_le _ _).trans ((add_le_add ih hblock).trans_eq (by push_cast; ring))

/-- Comparing one endpoint per block with the mean of that block costs
the Lipschitz constant times the total length. The last partial block
costs at most one. -/
theorem norm_sum_multiples_sub_full_le (N d : ℕ) (hd : 0 < d) {C : ℝ} (hC : 0 ≤ C)
    (f : ℕ → ℂ) (hbound : ∀ n, ‖f n‖ ≤ 1)
    (hLip : ∀ n m : ℕ, ‖f n - f m‖ ≤ C * |(n : ℝ) - (m : ℝ)|) :
    ‖(∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n), f n) -
      (∑ n ∈ Finset.Icc 1 N, f n) / (d : ℂ)‖ ≤ 1 + C * (N : ℝ) := by
  rw [sum_multiples_Icc N d hd, sum_nat_Icc_eq_range]
  let m := N / d
  let r := N % d
  have hN : m * d + r = N := by simpa [m, r, add_comm, Nat.mul_comm] using Nat.mod_add_div N d
  have hmd : (m : ℝ) * (d : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show m * d ≤ N by omega)
  have hrd : (r : ℝ) ≤ (d : ℝ) := by exact_mod_cast (Nat.mod_lt N hd).le
  let A := ∑ j ∈ Finset.range m, f (d * (j + 1))
  let B := ∑ i ∈ Finset.range (m * d), f (i + 1)
  let T := ∑ i ∈ Finset.range r, f (m * d + i + 1)
  have htail : ‖T‖ ≤ (r : ℝ) := by
    change ‖∑ i ∈ Finset.range r, f (m * d + i + 1)‖ ≤ _
    refine (norm_sum_le _ _).trans ?_
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] using
      Finset.sum_le_sum (s := Finset.range r) (fun i _ => hbound (m * d + i + 1))
  have hsplit : (∑ i ∈ Finset.range N, f (i + 1)) = B + T := by
    rw [← hN, Finset.sum_range_add]
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  change ‖A - (∑ i ∈ Finset.range N, f (i + 1)) / (d : ℂ)‖ ≤ _
  rw [hsplit, show A - (B + T) / (d : ℂ) = ((d : ℂ) * A - B - T) / (d : ℂ) by
    field_simp; ring, norm_div, Complex.norm_natCast, div_le_iff₀ (by positivity : 0 < (d : ℝ))]
  have h := (norm_sub_le ((d : ℂ) * A - B) T).trans
    (add_le_add (norm_block_endpoints_sub_sum d hC f hLip m) htail)
  have hmain := mul_le_mul_of_nonneg_left hmd (mul_nonneg hC (Nat.cast_nonneg d))
  exact h.trans (by nlinarith only [hmain, hrd])

/-- The block discrepancy estimate for the real-frequency exponential. -/
theorem exists_norm_sum_phase_multiples_sub_full_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N d : ℕ), 0 < d → ∀ θ : ℝ,
      ‖(∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n), phase (θ * (n : ℝ))) -
        (∑ n ∈ Finset.Icc 1 N, phase (θ * (n : ℝ))) / (d : ℂ)‖ ≤
        1 + C * |θ| * (N : ℝ) := by
  obtain ⟨C, hC, hLip⟩ := phase_lipschitz_exists
  refine ⟨C, hC, fun N d hd θ => ?_⟩
  apply norm_sum_multiples_sub_full_le N d hd (mul_nonneg hC (abs_nonneg θ))
    (fun n => phase (θ * (n : ℝ))) (fun _ => by simp [norm_phase])
  intro n m
  convert hLip (θ * (n : ℝ)) (θ * (m : ℝ)) using 1
  rw [← mul_sub, abs_mul, mul_assoc]

/-- A rational phase with denominator `q` is identically one on
the positive multiples of any `d` divisible by `q`. -/
theorem sum_phase_multiples_sub_rational (N d q : ℕ) (hq : 0 < q) (hqd : q ∣ d)
    (a : ℤ) (α : ℝ) :
    (∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n), phase (α * (n : ℝ))) =
      ∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n),
        phase ((α - (a : ℝ) / (q : ℝ)) * (n : ℝ)) := by
  apply Finset.sum_congr rfl
  intro n hn
  obtain ⟨m, hm⟩ := hqd.trans (Finset.mem_filter.mp hn).2
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have heq : (a : ℝ) / (q : ℝ) * (n : ℝ) = ((a * (m : ℤ) : ℤ) : ℝ) := by
    rw [hm, Nat.cast_mul, Int.cast_mul, Int.cast_natCast]
    field_simp
    ring
  apply phase_eq_of_sub_int
  refine ⟨a * (m : ℤ), ?_⟩
  rw [← heq]
  ring

end NilBohr
