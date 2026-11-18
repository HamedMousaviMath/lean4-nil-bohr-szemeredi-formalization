import NilBohr.Selector
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.NumberTheory.ArithmeticFunction

/-! Finite Fourier coefficients of the squarefree coprimality weight. -/

open scoped BigOperators ArithmeticFunction

namespace NilBohr

/-- A product of distinct primes is squarefree. -/
theorem squarefree_prod_primes (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    Squarefree (∏ p ∈ P, p) := by
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
    have hpPrime := hP p (Finset.mem_insert_self p s)
    have hs (l : ℕ) (hl : l ∈ s) : l.Prime := hP l (Finset.mem_insert_of_mem hl)
    rw [Finset.prod_insert hp, Nat.squarefree_mul_iff]
    refine ⟨?_, hpPrime.squarefree, ih hs⟩
    rw [hpPrime.coprime_iff_not_dvd]
    intro hdiv
    obtain ⟨l, hl, hd⟩ := (hpPrime.prime.dvd_finset_prod_iff id).mp hdiv
    exact hp ((Nat.Prime.dvd_iff_eq (hs l hl) hpPrime.ne_one).mp hd ▸ hl)

private theorem phaseExponential_nat_mul (x : ℝ) (n : ℕ) :
    phaseExponential (x * n) = phaseExponential x ^ n := by
  unfold phaseExponential
  push_cast
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

private theorem primitive_phaseExponential_eq_one_iff {q : ℕ} (hq : 0 < q) {a : ℤ}
    (ha : a.natAbs.Coprime q) (n : ℕ) :
    phaseExponential (((a : ℝ) / q) * n) = 1 ↔ q ∣ n := by
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  constructor
  · intro h
    obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp h
    push_cast at hk
    have h' : (a : ℂ) / (q : ℂ) * n = (k : ℂ) := by
      apply mul_left_cancel₀ Complex.two_pi_I_ne_zero
      linear_combination hk
    have hd : (a : ℤ) * (n : ℤ) = k * (q : ℤ) := by
      have he : (a : ℂ) * n = (k : ℂ) * q := by
        apply (div_eq_iff hq').mp
        rw [mul_div_right_comm]
        exact h'
      exact_mod_cast he
    have hdiv : (q : ℤ) ∣ a * (n : ℤ) := ⟨k, by rw [hd, mul_comm]⟩
    have hdiv' := Int.natAbs_dvd_natAbs.mpr hdiv
    rw [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast] at hdiv'
    exact ha.symm.dvd_of_dvd_mul_left hdiv'
  · rintro ⟨k, rfl⟩
    apply Complex.exp_eq_one_iff.mpr
    refine ⟨a * k, ?_⟩
    push_cast
    field_simp
    ring

private theorem sum_multiples_range {H d : ℕ} (hd : 0 < d) (hdH : d ∣ H) (f : ℕ → ℂ) :
    (∑ n ∈ Finset.range H, if d ∣ n then f n else 0) =
      ∑ k ∈ Finset.range (H / d), f (d * k) := by
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun k _ => d * k)
  · intro k hk
    have hk' := Finset.mem_range.mp hk
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, dvd_mul_right _ _⟩
    rw [← Nat.mul_div_cancel' hdH, Nat.mul_lt_mul_left hd]
    exact hk'
  · intro k _ l _ hl
    exact Nat.eq_of_mul_eq_mul_left hd hl
  · intro n hn
    obtain ⟨hr, k, rfl⟩ := Finset.mem_filter.mp hn
    refine ⟨k, Finset.mem_range.mpr ?_, rfl⟩
    have hr' := Finset.mem_range.mp hr
    rwa [← Nat.mul_div_cancel' hdH, Nat.mul_lt_mul_left hd] at hr'
  · intros; rfl

/-- Complete-period rational exponential sum over the multiples of `d`. -/
theorem sum_phaseExponential_dvd_full_period {H q d : ℕ} (hq : 0 < q) (hd : 0 < d)
    (hqH : q ∣ H) (hdH : d ∣ H) {a : ℤ} (ha : a.natAbs.Coprime q) :
    (∑ n ∈ Finset.range H, (if d ∣ n then phaseExponential (((a : ℝ) / q) * n) else 0)) =
      if q ∣ d then (↑(H / d) : ℂ) else 0 := by
  rw [sum_multiples_range hd hdH]
  let z := phaseExponential (((a : ℝ) / q) * d)
  have he (k : ℕ) : phaseExponential (((a : ℝ) / q) * (↑(d * k) : ℝ)) = z ^ k := by
    push_cast
    rw [← mul_assoc, phaseExponential_nat_mul]
  simp_rw [he]
  by_cases hqd : q ∣ d
  · simp [z, (primitive_phaseExponential_eq_one_iff hq ha d).mpr hqd, hqd]
  · rw [if_neg hqd, geom_sum_eq (fun hz => hqd ((primitive_phaseExponential_eq_one_iff hq ha d).mp hz))]
    have hz : z ^ (H / d) = 1 := by
      rw [← he, Nat.mul_div_cancel' hdH]
      exact (primitive_phaseExponential_eq_one_iff hq ha H).mpr hqH
    rw [show phaseExponential (((a : ℝ) / q) * d) = z from rfl, hz]
    simp

/-- The Fourier coefficient over a full period of integer coprimality. -/
noncomputable def coprimeFourierMean (H W : ℕ) (a : ℤ) (q : ℕ) : ℂ :=
  (∑ n ∈ Finset.range H,
      if n.Coprime W then phaseExponential (((a : ℝ) / q) * n) else 0) / (H : ℂ)

private theorem sum_moebius_dvd_indicator (n W : ℕ) (hW : 0 < W) :
    (∑ d ∈ W.divisors, if d ∣ n then (μ d : ℂ) else 0) =
      if n.Coprime W then 1 else 0 := by
  rw [← Finset.sum_filter, show W.divisors.filter (· ∣ n) = (n.gcd W).divisors by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    have hG := (Nat.gcd_pos_of_pos_right n hW).ne'
    simp [hW.ne', hG, and_comm]]
  change (∑ d ∈ (n.gcd W).divisors, (μ : ArithmeticFunction ℂ) d) = _
  rw [← ArithmeticFunction.coe_mul_zeta_apply (f := (μ : ArithmeticFunction ℂ)),
    ArithmeticFunction.coe_moebius_mul_coe_zeta]
  rfl

/-- The divisor formula for the complete coprimality coefficient. -/
theorem coprimeFourierMean_eq_divisor_sum {H W q : ℕ} (hH : 0 < H) (hW : 0 < W)
    (hq : 0 < q) (hWH : W ∣ H) (hqH : q ∣ H) {a : ℤ} (ha : a.natAbs.Coprime q) :
    coprimeFourierMean H W a q =
      ∑ d ∈ W.divisors, if q ∣ d then (μ d : ℂ) / (d : ℂ) else 0 := by
  let e (n : ℕ) := phaseExponential (((a : ℝ) / q) * n)
  have hexpand (n : ℕ) : (if n.Coprime W then e n else 0) =
      ∑ d ∈ W.divisors, (μ d : ℂ) * (if d ∣ n then e n else 0) := by
    calc
      _ = (if n.Coprime W then (1 : ℂ) else 0) * e n := by split_ifs <;> simp
      _ = _ := by
        rw [← sum_moebius_dvd_indicator n W hW, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro d _
        split_ifs <;> simp
  unfold coprimeFourierMean
  change (∑ n ∈ Finset.range H, if n.Coprime W then e n else 0) / (H : ℂ) = _
  simp_rw [hexpand, Finset.sum_comm (s := Finset.range H), ← Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  obtain ⟨hdW, _⟩ := Nat.mem_divisors.mp hd
  have hdH := hdW.trans hWH
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdW hW
  rw [show (∑ n ∈ Finset.range H, if d ∣ n then e n else 0) = _ from
    sum_phaseExponential_dvd_full_period hq hdpos hqH hdH ha]
  split_ifs with hqd
  · rw [Nat.cast_div hdH (by exact_mod_cast hdpos.ne')]
    field_simp [show (d : ℂ) ≠ 0 by exact_mod_cast hdpos.ne',
      show (H : ℂ) ≠ 0 by exact_mod_cast hH.ne']
    ring
  · simp

private theorem sum_moebius_inverse_eq_totient {R : ℕ} (hR : Squarefree R) :
    (∑ r ∈ R.divisors, (μ r : ℂ) / r) = (R.totient : ℂ) / R := by
  let f : ArithmeticFunction ℂ := ⟨fun n => (n : ℂ)⁻¹, by simp⟩
  have hf : f.IsMultiplicative := by
    constructor
    · simp [f]
    · intro m n _
      change ((m * n : ℕ) : ℂ)⁻¹ = (m : ℂ)⁻¹ * (n : ℂ)⁻¹
      rw [Nat.cast_mul, mul_inv]
  have h := hf.prodPrimeFactors_one_sub_of_squarefree f hR
  change (∏ p ∈ R.primeFactors, (1 - (p : ℂ)⁻¹)) =
    (∑ d ∈ R.divisors, (μ d : ℂ) * (d : ℂ)⁻¹) at h
  simp_rw [div_eq_mul_inv] at ⊢
  rw [← h]
  have hprod := congrArg (fun x : ℚ => (x : ℂ)) (Nat.totient_eq_mul_prod_factors R)
  simp only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_prod, Rat.cast_inv, Rat.cast_sub,
    Rat.cast_one] at hprod
  rw [hprod]
  field_simp [show (R : ℂ) ≠ 0 by exact_mod_cast hR.ne_zero]

private theorem sum_moebius_divisors_multiple {q R : ℕ} (hq : 0 < q) (hR : 0 < R)
    (hcop : q.Coprime R) :
    (∑ d ∈ (q * R).divisors, if q ∣ d then (μ d : ℂ) / d else 0) =
      ((μ q : ℂ) / q) * ∑ r ∈ R.divisors, (μ r : ℂ) / r := by
  rw [← Finset.sum_filter, Finset.mul_sum]
  symm
  apply Finset.sum_bij (fun r _ => q * r)
  · intro r hr
    refine Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr
      ⟨mul_dvd_mul_left _ (Nat.dvd_of_mem_divisors hr), (Nat.mul_pos hq hR).ne'⟩,
      dvd_mul_right _ _⟩
  · intro r _ s _ hrs
    exact Nat.eq_of_mul_eq_mul_left hq hrs
  · intro d hd
    obtain ⟨hd', r, rfl⟩ := Finset.mem_filter.mp hd
    have hdiv : r ∣ R := Nat.dvd_of_mul_dvd_mul_left hq (Nat.dvd_of_mem_divisors hd')
    exact ⟨r, Nat.mem_divisors.mpr ⟨hdiv, hR.ne'⟩, rfl⟩
  · intro r hr
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
      (hcop.coprime_dvd_right (Nat.dvd_of_mem_divisors hr)), Int.cast_mul, Nat.cast_mul, div_mul_div_comm]

/-- The normalized complete coprimality coefficient at a primitive rational
frequency is zero unless the denominator divides the squarefree sieve modulus.
Otherwise it is the Möbius value divided by the totient of the denominator. -/
theorem normalized_coprimeFourierMean_eq {H W q : ℕ} (hH : 0 < H) (hW : Squarefree W)
    (hq : 0 < q) (hWH : W ∣ H) (hqH : q ∣ H) {a : ℤ} (ha : a.natAbs.Coprime q) :
    (W : ℂ) / (W.totient : ℂ) * coprimeFourierMean H W a q =
      if q ∣ W then (μ q : ℂ) / (q.totient : ℂ) else 0 := by
  rw [coprimeFourierMean_eq_divisor_sum hH hW.ne_zero.bot_lt hq hWH hqH ha]
  by_cases hqW : q ∣ W
  · rw [if_pos hqW]
    obtain ⟨R, rfl⟩ := hqW
    obtain ⟨hcop, _, hR⟩ := Nat.squarefree_mul_iff.mp hW
    rw [sum_moebius_divisors_multiple hq hR.ne_zero.bot_lt hcop,
      sum_moebius_inverse_eq_totient hR, Nat.totient_mul hcop, Nat.cast_mul, Nat.cast_mul]
    have hφq : (q.totient : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hq).ne'
    have hφR : (R.totient : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hR.ne_zero.bot_lt).ne'
    field_simp [hφq, hφR, show (q : ℂ) ≠ 0 by exact_mod_cast hq.ne',
      show (R : ℂ) ≠ 0 by exact_mod_cast hR.ne_zero]
    ring
  · rw [if_neg hqW, Finset.sum_eq_zero, mul_zero]
    intro d hd
    exact if_neg (fun hqd => hqW (hqd.trans (Nat.dvd_of_mem_divisors hd)))

private theorem squarefree_le_twice_totient_sq {q : ℕ} (hq : Squarefree q) :
    q ≤ 2 * q.totient ^ 2 := by
  have hqTot : q.totient = ∏ p ∈ q.primeFactors, (p - 1) := by
    rw [Nat.totient_eq_div_primeFactors_mul, Nat.prod_primeFactors_of_squarefree hq,
      Nat.div_self (Nat.pos_of_ne_zero hq.ne_zero), one_mul]
  have hprime (p : ℕ) (hp : p ∈ q.primeFactors) (hp2 : p ≠ 2) :
      p ≤ (p - 1)^2 := by
    have hp' := (Nat.prime_of_mem_primeFactors hp).two_le
    have hthree : 3 ≤ p := by omega
    rw [pow_two]
    exact (show p ≤ 2 * (p - 1) by omega).trans
      (Nat.mul_le_mul_right (p - 1) (show 2 ≤ p - 1 by omega))
  rw [hqTot, ← Finset.prod_pow]
  conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hq]
  by_cases htwo : 2 ∈ q.primeFactors
  · rw [← Finset.mul_prod_erase _ (fun p => p) htwo,
      ← Finset.mul_prod_erase _ (fun p => (p - 1)^2) htwo]
    norm_num
    apply Finset.prod_le_prod'
    intro p hp
    exact hprime p (Finset.mem_erase.mp hp).2 (Finset.mem_erase.mp hp).1
  · have hle : (∏ p ∈ q.primeFactors, p) ≤ ∏ p ∈ q.primeFactors, (p - 1)^2 := by
      apply Finset.prod_le_prod'
      intro p hp
      exact hprime p hp (by rintro rfl; exact htwo hp)
    exact hle.trans (by omega)

/-- A bound uniform in the squarefree modulus and in the choice of full
period. It tends to zero as the primitive denominator tends to infinity. -/
theorem norm_normalized_coprimeFourierMean_le {H W q : ℕ} (hH : 0 < H) (hW : Squarefree W)
    (hq : 0 < q) (hWH : W ∣ H) (hqH : q ∣ H) {a : ℤ} (ha : a.natAbs.Coprime q) :
    ‖(W : ℂ) / (W.totient : ℂ) * coprimeFourierMean H W a q‖ ≤ Real.sqrt (2 / (q : ℝ)) := by
  rw [normalized_coprimeFourierMean_eq hH hW hq hWH hqH ha]
  by_cases hqW : q ∣ W
  · rw [if_pos hqW, norm_div]
    have hqSquarefree := hW.squarefree_of_dvd hqW
    have hμ : ‖(μ q : ℂ)‖ = 1 := by
      rw [Complex.norm_intCast, ← Int.cast_abs, ArithmeticFunction.abs_moebius_eq_one_of_squarefree
        hqSquarefree, Int.cast_one]
    rw [hμ, Complex.norm_natCast]
    have hφ : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
    have hq' : 0 < (q : ℝ) := by exact_mod_cast hq
    apply Real.le_sqrt_of_sq_le
    have h : (q : ℝ) ≤ 2 * (q.totient : ℝ)^2 := by
      exact_mod_cast squarefree_le_twice_totient_sq hqSquarefree
    rw [div_pow, one_pow, div_le_div_iff₀ (by positivity) hq']
    simpa only [one_mul] using h
  · rw [if_neg hqW, norm_zero]
    exact Real.sqrt_nonneg _

end NilBohr
