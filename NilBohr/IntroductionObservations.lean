import NilBohr.Arithmetic

/-! Arithmetic examples motivating shifted primes and nonlinear Bohr restrictions. -/

open Filter
open scoped Topology

namespace NilBohr

/-- Positive multiples of four have natural density one quarter. -/
theorem multiplesOfFour_density :
    Tendsto (fun N : ℕ => (((Finset.Ioc 0 N).filter (fun x => 4 ∣ x)).card : ℝ) / N)
      atTop (𝓝 (1 / 4 : ℝ)) := by
  have hmod := tendsto_mod_div_atTop_nhds_zero_nat (m := 4) (by decide)
  have hlim : Tendsto (fun N : ℕ => (1 - (↑(N % 4) : ℝ) / N) / 4) atTop
      (𝓝 (1 / 4 : ℝ)) := by
    simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub hmod |>.div_const 4
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  rw [Nat.Ioc_filter_dvd_card_eq_div]
  have hquot : (↑(N % 4) : ℝ) + 4 * (↑(N / 4) : ℝ) = (N : ℝ) := by
    exact_mod_cast Nat.mod_add_div N 4
  have hsub : (N : ℝ) - ↑(N % 4) = 4 * (↑(N / 4) : ℝ) := by linarith
  field_simp [(Nat.cast_pos.mpr hN : (0 : ℝ) < N).ne']
  rw [hsub]
  ring

/-- No two multiples of four differ by a prime.
Together with `multiplesOfFour_density`, this gives a positive-density
obstruction to using the unshifted primes as recurrence times. -/
theorem not_prime_step_between_multiplesOfFour {x p : ℕ} (hx : 4 ∣ x) (hp : p.Prime) :
    ¬ 4 ∣ x + p := by
  intro h
  have hdiv : 4 ∣ p := (Nat.dvd_add_right hx).mp h
  have heq : p = 4 := ((Nat.dvd_prime hp).mp hdiv).resolve_left (by decide) |>.symm
  subst p
  exact (by decide : ¬ Nat.Prime 4) hp

/-- At tolerance below `1/q`, membership of the rational Bohr interval
is equivalent to divisibility of the signed numerator. -/
theorem torusNorm_fraction_lt_iff_dvd (a q : ℤ) (hq : 0 < q) {ε : ℝ}
    (hε : 0 < ε) (hsmall : ε < 1 / (q : ℝ)) :
    torusNorm ((a : ℝ) / q) < ε ↔ q ∣ a := by
  constructor
  · intro h
    by_contra hd
    exact (not_lt_of_ge (torusNorm_fraction_ge_inv a q hq hd)) (h.trans hsmall)
  · rintro ⟨b, rfl⟩
    have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    have hdiv : ((q * b : ℤ) : ℝ) / q = (b : ℝ) := by
      push_cast
      field_simp
    simpa only [hdiv, torusNorm_eq, round_intCast, sub_self, abs_zero] using hε

/-- The congruence in the introduction is independent of whether `p` is prime. -/
theorem rationalBohr_iff_modEq_one (p q : ℤ) (hq : 0 < q) {ε : ℝ}
    (hε : 0 < ε) (hsmall : ε < 1 / (q : ℝ)) :
    torusNorm (((p : ℝ) - 1) / q) < ε ↔ p ≡ 1 [ZMOD q] := by
  have h := torusNorm_fraction_lt_iff_dvd (p - 1) q hq hε hsmall
  have h' : torusNorm (((p : ℝ) - 1) / q) < ε ↔ 1 ≡ p [ZMOD q] := by
    simpa only [Int.cast_sub, Int.cast_one, ← Int.modEq_iff_dvd] using h
  exact h'.trans ⟨Int.ModEq.symm, Int.ModEq.symm⟩

theorem quadraticColor_difference (α x n : ℝ) :
    α * (x + n)^2 - α * x^2 = 2 * α * x * n + α * n^2 := by
  ring

/-- With frequency `1/3` and `x = n = 2`, the colors of `x` and `x+n`
coincide exactly, but the desired quadratic return norm is `1/3`. -/
theorem quadraticColor_counterexample :
    (((1 / 3 : ℝ) * (2 + 2)^2 : ℝ) : UnitAddCircle) =
        (((1 / 3 : ℝ) * 2^2 : ℝ) : UnitAddCircle) ∧
      torusNorm ((1 / 3 : ℝ) * 2^2) = 1 / 3 := by
  constructor
  · rw [← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
    refine ⟨4, ?_⟩
    norm_num
  · have hround : round (1 / 3 : ℝ) = 0 := round_eq_zero_iff.mpr
      ⟨by norm_num, by norm_num⟩
    rw [show (1 / 3 : ℝ) * 2^2 = 1 / 3 + ((1 : ℤ) : ℝ) by norm_num,
      torusNorm_add_int, torusNorm_eq, hround]
    norm_num

end NilBohr
