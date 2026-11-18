import NilBohr.GowersComparison
import NilBohr.Sieve
import Mathlib.Algebra.BigOperators.Associated

/-! The Cramér weight on a reduced progression and its sieve normalization. -/

open scoped BigOperators

namespace NilBohr

/-- The part of the primorial that still imposes sieve conditions in the
residue class one modulo q. -/
def cramerSieveModulus (Q q : ℕ) : ℕ :=
  ∏ p ∈ (primesThrough Q).filter (fun p => ¬p ∣ q), p

theorem primeFactors_cramerModulus {Q : ℕ} (hQ : 2 ≤ Q) :
    (cramerModulus Q).primeFactors = primesThrough Q := by
  have hpos : 0 < ∏ p ∈ primesThrough Q, p :=
    Finset.prod_pos fun p hp => (Finset.mem_filter.mp hp).2.pos
  have hpos' : 0 < cramerModulus Q := by unfold cramerModulus; positivity
  ext p
  rw [Nat.mem_primeFactors_of_ne_zero hpos'.ne']
  constructor
  · rintro ⟨hp, hdiv⟩
    rw [cramerModulus] at hdiv
    rcases (hp.dvd_mul.mp hdiv) with h8 | hprod
    · have h2 : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2^3 from h8)
      have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2
      subst p
      simp [primesThrough, Nat.prime_two, Nat.lt_succ_iff, hQ]
    · obtain ⟨a, ha, hd⟩ := hp.prime.dvd_finset_prod_iff id |>.mp hprod
      have hap := (Finset.mem_filter.mp ha).2
      have heq := (Nat.Prime.dvd_iff_eq hap hp.ne_one).mp hd
      exact heq ▸ ha
  · intro hp
    exact ⟨(Finset.mem_filter.mp hp).2,
      dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem id hp) 8⟩

/-- The exact Euler product of the model normalization. -/
theorem cramerModulus_div_totient {Q : ℕ} (hQ : 2 ≤ Q) :
    (cramerModulus Q : ℝ) / (cramerModulus Q).totient =
      ∏ p ∈ primesThrough Q, (1-(p : ℝ)⁻¹)⁻¹ := by
  let W := cramerModulus Q
  have hW : (0 : ℝ) < W := by
    exact_mod_cast (show 0 < W from
      Nat.mul_pos (by decide) (Finset.prod_pos fun p hp => (Finset.mem_filter.mp hp).2.pos))
  have hEuler : (W.totient : ℝ) = (W : ℝ) * ∏ p ∈ W.primeFactors, (1-(p : ℝ)⁻¹) := by
    have h := congrArg (fun x : ℚ => (x : ℝ)) (Nat.totient_eq_mul_prod_factors W)
    push_cast at h
    exact h
  change (W : ℝ) / W.totient = _
  rw [hEuler, div_mul_eq_div_div, div_self hW.ne', one_div, Finset.prod_inv_distrib,
    show W.primeFactors = _ from primeFactors_cramerModulus hQ]

/-- Coprimality with the full model modulus on a residue-one progression is
equivalent to the sieve condition on primes not dividing q. -/
theorem coprime_cramerModulus_iff {Q q m : ℕ} (hQ : 2 ≤ Q) (hmq : m.Coprime q) :
    m.Coprime (cramerModulus Q) ↔ m.Coprime (cramerSieveModulus Q q) := by
  have h2 : 2 ∈ primesThrough Q := by
    simp [primesThrough, Nat.prime_two, Nat.lt_succ_iff, hQ]
  have hfull : m.Coprime (cramerModulus Q) ↔
      ∀ p ∈ primesThrough Q, m.Coprime p := by
    rw [cramerModulus, Nat.coprime_mul_iff_right, Nat.coprime_prod_right_iff]
    refine and_iff_right_of_imp ?_
    intro h
    have hm2 := h 2 h2
    simpa using hm2.pow_right 3
  rw [hfull, cramerSieveModulus, Nat.coprime_prod_right_iff]
  constructor
  · intro h p hp
    exact h p (Finset.mem_filter.mp hp).1
  · intro h p hp
    by_cases hd : p ∣ q
    · exact hmq.coprime_dvd_right hd
    · exact h p (Finset.mem_filter.mpr ⟨hp, hd⟩)

theorem cramerWeight_eq_sieveIndicator {Q q : ℕ} (hQ : 2 ≤ Q) (m : ℤ)
    (hmq : m.toNat.Coprime q) :
    cramerWeight Q m =
      ((∏ p ∈ primesThrough Q, (1-(p : ℝ)⁻¹)⁻¹ : ℝ) : ℂ) *
        (coprimeSieveIndicator (cramerSieveModulus Q q) m.toNat : ℂ) := by
  have hCoprime := coprime_cramerModulus_iff hQ hmq
  by_cases h : m.toNat.Coprime (cramerSieveModulus Q q)
  · simp only [cramerWeight, if_pos (hCoprime.mpr h), cramerModulus_div_totient hQ,
      coprimeSieveIndicator, if_pos h, Complex.ofReal_one, mul_one]
  · simp only [cramerWeight, if_neg (fun hFull => h (hCoprime.mp hFull)),
      coprimeSieveIndicator, if_neg h, Complex.ofReal_zero, mul_zero]

end NilBohr
