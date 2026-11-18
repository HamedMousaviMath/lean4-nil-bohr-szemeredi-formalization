import NilBohr.DensityParameters

/-! The exact Chebyshev identity for the initial modulus in the density iteration. -/

open scoped BigOperators

namespace NilBohr

private theorem primePower_dvd_iff_exists_dvd {p k : ℕ} (hp : p.Prime) (hk : 0 < k)
    (s : Finset ℕ) (hs : ∀ n ∈ s, n ≠ 0) :
    p ^ k ∣ s.lcm id ↔ ∃ n ∈ s, p ^ k ∣ n := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hpow : 1 < p ^ k := one_lt_pow₀ hp.one_lt hk.ne'
    simp [Nat.dvd_one, ne_of_gt hpow]
  | @insert n s hn ih =>
    have hn₀ : n ≠ 0 := hs n (Finset.mem_insert_self n s)
    have hs₀ : ∀ m ∈ s, m ≠ 0 := fun m hm => hs m (Finset.mem_insert_of_mem hm)
    have hL : s.lcm id ≠ 0 := by
      rw [ne_eq, Finset.lcm_eq_zero_iff]
      rintro ⟨m, hm, rfl⟩
      exact hs₀ 0 hm rfl
    have hpow : p ^ k ∣ Nat.lcm n (s.lcm id) ↔ p ^ k ∣ n ∨ p ^ k ∣ s.lcm id := by
      rw [hp.pow_dvd_iff_le_factorization (Nat.lcm_ne_zero hn₀ hL),
        Nat.factorization_lcm hn₀ hL, Finsupp.sup_apply, le_sup_iff,
        hp.pow_dvd_iff_le_factorization hn₀, hp.pow_dvd_iff_le_factorization hL]
    rw [Finset.lcm_insert]
    change p ^ k ∣ Nat.lcm n (s.lcm id) ↔ _
    rw [hpow, ih hs₀]
    simp [Finset.mem_insert, or_and_right, exists_or]

/-- Exactly the prime powers up to the cutoff contribute to the Mangoldt
divisor sum of the initial least common multiple. -/
theorem log_initialModulus_eq_mangoldt_sum (w : ℕ) :
    Real.log (initialModulus w : ℝ) =
      ∑ m ∈ Finset.range (w + 1), ArithmeticFunction.vonMangoldt m := by
  classical
  have hL : initialModulus w ≠ 0 := (initialModulus_pos w).ne'
  have hPrimePowers : (initialModulus w).divisors.filter IsPrimePow =
      (Finset.range (w + 1)).filter IsPrimePow := by
    ext m
    rw [Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨hm, hpp⟩
      refine ⟨Finset.mem_range.mpr ?_, hpp⟩
      obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff m).mp hpp
      have hdvd := (Nat.mem_divisors.mp hm).1
      obtain ⟨n, hn, hdiv⟩ :=
        (primePower_dvd_iff_exists_dvd hp hk (Finset.Icc 1 w)
          (fun n hn => ((Nat.zero_lt_succ 0).trans_le (Finset.mem_Icc.mp hn).1).ne')).mp hdvd
      obtain ⟨hpos, hle⟩ := Finset.mem_Icc.mp hn
      exact Nat.lt_succ_of_le ((Nat.le_of_dvd hpos hdiv).trans hle)
    · rintro ⟨hm, hpp⟩
      refine ⟨Nat.mem_divisors.mpr ⟨?_, hL⟩, hpp⟩
      have hmpos : 0 < m := by
        obtain ⟨p, k, hp, _, rfl⟩ := (isPrimePow_nat_iff m).mp hpp
        exact pow_pos hp.pos _
      exact Finset.dvd_lcm (f := id)
        (Finset.mem_Icc.mpr ⟨hmpos, Nat.le_of_lt_succ (Finset.mem_range.mp hm)⟩)
  have hSum (s : Finset ℕ) :
      ∑ m ∈ s.filter IsPrimePow, ArithmeticFunction.vonMangoldt m =
        ∑ m ∈ s, ArithmeticFunction.vonMangoldt m := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro m hm hs
    exact ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr (fun h => hs (Finset.mem_filter.mpr ⟨hm, h⟩))
  rw [← ArithmeticFunction.vonMangoldt_sum, ← hSum (initialModulus w).divisors,
    hPrimePowers, hSum]

end NilBohr
