import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Complex.Norm
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace NilBohr

/-- The divisor sum attached to finite sieve coefficients. In the manuscript,
`hits l m` means that the divisor `l` divides the prime variable `m`. -/
def sieveDivisorSum {L X : Type*} (divisors : Finset L)
    (hits : L → X → Prop) [DecidableRel hits] (coeff : L → ℝ) (x : X) : ℝ :=
  ∑ l ∈ divisors, if hits l x then coeff l else 0

/-- The finite weighted midpoint estimate in the Cramér term of Proposition 6.2.
The real bracketing coefficients enter explicitly. The local discrepancy compares
each filtered sample count with its model. The conclusion holds for every complex
test of modulus at most one. -/
theorem sieveMidpoint_bound {L X : Type*} (divisors : Finset L) (samples : Finset X)
    (hits : L → X → Prop) [DecidableRel hits]
    (lower upper : L → ℝ) (sifted : X → ℝ) (test : X → ℂ)
    (expected : L → ℝ) (error : ℝ)
    (hLower : ∀ l ∈ divisors, |lower l| ≤ 1)
    (hUpper : ∀ l ∈ divisors, |upper l| ≤ 1)
    (hBracket : ∀ x ∈ samples,
      sieveDivisorSum divisors hits lower x ≤ sifted x ∧
      sifted x ≤ sieveDivisorSum divisors hits upper x)
    (hTest : ∀ x ∈ samples, ‖test x‖ ≤ 1)
    (hDiscrepancy : ∀ l ∈ divisors,
      |((samples.filter (hits l)).card : ℝ) - expected l| ≤ error) :
    ‖∑ x ∈ samples, (sifted x : ℂ) * test x‖ ≤
      (∑ l ∈ divisors, ‖∑ x ∈ samples.filter (hits l), test x‖) +
      (∑ l ∈ divisors, (upper l - lower l) * expected l) / 2 +
      (divisors.card : ℝ) * error := by
  let mid : L → ℝ := fun l => (lower l + upper l) / 2
  let lowerSum := sieveDivisorSum divisors hits lower
  let upperSum := sieveDivisorSum divisors hits upper
  let midSum := sieveDivisorSum divisors hits mid
  have hMidSum (x : X) : midSum x = (lowerSum x + upperSum x) / 2 := by
    simp only [midSum, lowerSum, upperSum, sieveDivisorSum, mid]
    rw [← Finset.sum_add_distrib, div_eq_mul_inv, Finset.sum_mul]
    simp_rw [div_eq_mul_inv]
    apply Finset.sum_congr rfl
    intro l hl
    split_ifs <;> simp
  have hMid (l : L) (hl : l ∈ divisors) : |mid l| ≤ 1 := by
    dsimp [mid]
    have h := (abs_add_le (lower l) (upper l)).trans (add_le_add (hLower l hl) (hUpper l hl))
    rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith
  have hPoint (x : X) (hx : x ∈ samples) :
      |sifted x - midSum x| ≤ (upperSum x - lowerSum x) / 2 := by
    obtain ⟨hl, hu⟩ := hBracket x hx
    rw [hMidSum, abs_le]
    constructor <;> linarith
  have hWeight (x : X) (hx : x ∈ samples) :
      ‖(sifted x : ℂ) * test x - (midSum x : ℂ) * test x‖ ≤
        (upperSum x - lowerSum x) / 2 := by
    rw [← sub_mul, ← Complex.ofReal_sub, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_of_le_one_right (abs_nonneg _) (hTest x hx)).trans (hPoint x hx)
  have hMidpointEstimate :
      ‖∑ x ∈ samples, ((midSum x : ℝ) : ℂ) * test x‖ ≤
        ∑ l ∈ divisors, ‖∑ x ∈ samples.filter (hits l), test x‖ := by
    have hRearrange :
        (∑ x ∈ samples, ((midSum x : ℝ) : ℂ) * test x) =
          ∑ l ∈ divisors, ((mid l : ℝ) : ℂ) * (∑ x ∈ samples.filter (hits l), test x) := by
      calc
        _ = ∑ x ∈ samples, ∑ l ∈ divisors, if hits l x then (mid l : ℂ) * test x else 0 := by
          apply Finset.sum_congr rfl
          intro x hx
          simp only [midSum, sieveDivisorSum]
          rw [Complex.ofReal_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro l hl
          split_ifs <;> simp
        _ = _ := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro l hl
          rw [Finset.mul_sum, Finset.sum_filter]
    rw [hRearrange]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
    intro l hl
    rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (hMid l hl)
  have hGapRearrange :
      (∑ x ∈ samples, (upperSum x - lowerSum x) / 2) =
        (∑ l ∈ divisors, (upper l - lower l) * ((samples.filter (hits l)).card : ℝ)) / 2 := by
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul]
    have hGapFormula (x : X) :
        upperSum x - lowerSum x = ∑ l ∈ divisors, if hits l x then upper l - lower l else 0 := by
      simp only [upperSum, lowerSum, sieveDivisorSum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro l hl
      split_ifs <;> simp
    simp_rw [hGapFormula]
    rw [Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro l hl
    rw [← Finset.sum_filter]
    simp [mul_comm, sub_mul]
  have hGapEstimate :
      (∑ x ∈ samples, (upperSum x - lowerSum x) / 2) ≤
        (∑ l ∈ divisors, (upper l - lower l) * expected l) / 2 +
        (divisors.card : ℝ) * error := by
    rw [hGapRearrange]
    have hSum :
        (∑ l ∈ divisors, (upper l - lower l) * ((samples.filter (hits l)).card : ℝ)) ≤
        (∑ l ∈ divisors, (upper l - lower l) * expected l) +
        (divisors.card : ℝ) * (2 * error) := by
      rw [← nsmul_eq_mul, ← Finset.sum_const, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro l hl
      have hClose := hDiscrepancy l hl
      have hCoeff : |upper l - lower l| ≤ 2 := by
        calc
          |upper l - lower l| ≤ |upper l| + |lower l| := by
            simpa only [sub_zero, zero_sub, abs_neg] using (abs_sub_le (upper l) 0 (lower l))
          _ ≤ 2 := by linarith [hUpper l hl, hLower l hl]
      have hProduct :
          (upper l - lower l) * (((samples.filter (hits l)).card : ℝ) - expected l) ≤
          2 * error := by
        refine (le_abs_self _).trans ?_
        rw [abs_mul]
        exact mul_le_mul hCoeff hClose (abs_nonneg _) (by norm_num)
      linarith only [hProduct]
    nlinarith only [hSum]
  have hDifference :
      ‖∑ x ∈ samples, ((sifted x : ℂ) * test x - (midSum x : ℂ) * test x)‖ ≤
        ∑ x ∈ samples, (upperSum x - lowerSum x) / 2 :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum hWeight)
  have hSplit :
      (∑ x ∈ samples, (sifted x : ℂ) * test x) =
        (∑ x ∈ samples, (midSum x : ℂ) * test x) +
          ∑ x ∈ samples, ((sifted x : ℂ) * test x - (midSum x : ℂ) * test x) := by
    rw [Finset.sum_sub_distrib]
    abel
  rw [hSplit]
  linarith only [norm_add_le
    (∑ x ∈ samples, (midSum x : ℂ) * test x)
    (∑ x ∈ samples, ((sifted x : ℂ) * test x - (midSum x : ℂ) * test x)),
    hMidpointEstimate, hDifference, hGapEstimate]


/-- For a step invertible modulo a divisor, divisibility of the affine
parameter is a single residue class of its index. -/
theorem exists_modEq_of_dvd_affine (offset step divisor : ℕ)
    (hDivisor : 0 < divisor) (hCoprime : step.Coprime divisor) :
    ∃ residue : ℕ, ∀ t : ℕ, divisor ∣ offset + step * t ↔ t ≡ residue [MOD divisor] := by
  haveI : NeZero divisor := ⟨hDivisor.ne'⟩
  let unit := ZMod.unitOfCoprime step hCoprime
  let residue : ZMod divisor := (↑unit⁻¹ : ZMod divisor) * -(offset : ZMod divisor)
  refine ⟨residue.val, fun t => ?_⟩
  rw [← ZMod.natCast_zmod_eq_zero_iff_dvd, Nat.cast_add, Nat.cast_mul,
    ← ZMod.coe_unitOfCoprime step hCoprime,
    ← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val]
  change (offset : ZMod divisor) + (unit : ZMod divisor) * (t : ZMod divisor) = 0 ↔
    (t : ZMod divisor) = residue
  constructor
  · intro h
    have hNeg : (unit : ZMod divisor) * (t : ZMod divisor) = -(offset : ZMod divisor) :=
      eq_neg_of_add_eq_zero_right h
    calc
      (t : ZMod divisor) = (↑unit⁻¹ : ZMod divisor) * ((unit : ZMod divisor) * t) := by
        simp [← mul_assoc]
      _ = residue := by rw [hNeg]
  · intro h
    rw [h]
    simp [residue, ← mul_assoc]

/-- The local divisor count discrepancy in the Cramér term, at most one
for a consecutive segment of an arithmetic progression of coprime step. -/
theorem abs_card_dvd_affine_sub_le_one (offset step divisor H : ℕ)
    (hDivisor : 0 < divisor) (hCoprime : step.Coprime divisor) :
    |(((Finset.range H).filter (fun t => divisor ∣ offset + step * t)).card : ℝ)
      - (H : ℝ) / divisor| ≤ 1 := by
  obtain ⟨residue, hResidue⟩ := exists_modEq_of_dvd_affine offset step divisor hDivisor hCoprime
  simp_rw [hResidue]
  rw [← Nat.count_eq_card_filter_range, Nat.count_modEq_card _ hDivisor]
  have hDivisorReal : (0 : ℝ) < divisor := by exact_mod_cast hDivisor
  have hDecomp : (H : ℝ) / divisor = ((H / divisor : ℕ) : ℝ) +
      (↑(H % divisor) : ℝ) / divisor := by
    have h := Nat.div_add_mod H divisor
    have hReal : (H : ℝ) = (divisor : ℝ) * ((H / divisor : ℕ) : ℝ) + (↑(H % divisor) : ℝ) := by
      exact_mod_cast h.symm
    calc
      _ = ((divisor : ℝ) * (↑(H / divisor) : ℝ) + (↑(H % divisor) : ℝ)) / divisor :=
        congrArg (fun z : ℝ => z / (divisor : ℝ)) hReal
      _ = _ := by
        rw [add_div, mul_comm (divisor : ℝ), mul_div_cancel_right₀ _ hDivisorReal.ne']
  have hRemainderNonneg : 0 ≤ (↑(H % divisor) : ℝ) / divisor :=
    div_nonneg (Nat.cast_nonneg _) hDivisorReal.le
  have hRemainderLe : (↑(H % divisor) : ℝ) / divisor ≤ 1 := by
    apply (div_le_iff₀ hDivisorReal).2
    rw [one_mul]
    exact_mod_cast (Nat.mod_lt H hDivisor).le
  rw [hDecomp]
  split_ifs <;> push_cast <;> rw [abs_le] <;> constructor <;> linarith


/-- The coprimality selector in the Cramér model, before its Euler product
normalization. The sieving product omits primes dividing the progression step. -/
def coprimeSieveIndicator (W n : ℕ) : ℝ :=
  if n.Coprime W then 1 else 0

/-- The midpoint estimate, normalized by the length of the progression.
The divisibility count and its error are proved above. The lower and upper
coefficient bounds are the only sieve-theoretic premises. -/
theorem cramerSieve_average_bound (W offset step H : ℕ) (divisors : Finset ℕ)
    (hW : 0 < W) (hH : 0 < H) (hStep : step.Coprime W)
    (hDivisors : ∀ l ∈ divisors, l ∣ W)
    (lower upper : ℕ → ℝ) (test : ℕ → ℂ)
    (hLower : ∀ l ∈ divisors, |lower l| ≤ 1)
    (hUpper : ∀ l ∈ divisors, |upper l| ≤ 1)
    (hBracket : ∀ t ∈ Finset.range H,
      sieveDivisorSum divisors (fun l t => l ∣ offset + step * t) lower t ≤
        coprimeSieveIndicator W (offset + step * t) ∧
      coprimeSieveIndicator W (offset + step * t) ≤
        sieveDivisorSum divisors (fun l t => l ∣ offset + step * t) upper t)
    (hTest : ∀ t ∈ Finset.range H, ‖test t‖ ≤ 1) :
    ‖(∑ t ∈ Finset.range H, (coprimeSieveIndicator W (offset + step * t) : ℂ) * test t) /
        (H : ℂ)‖ ≤
      (∑ l ∈ divisors,
        ‖∑ t ∈ (Finset.range H).filter (fun t => l ∣ offset + step * t), test t‖) / (H : ℝ) +
      (∑ l ∈ divisors, (upper l - lower l) / (l : ℝ)) / 2 +
      (divisors.card : ℝ) / (H : ℝ) := by
  have hMidpoint := sieveMidpoint_bound divisors (Finset.range H)
    (fun l t => l ∣ offset + step * t) lower upper
    (fun t => coprimeSieveIndicator W (offset + step * t)) test
    (fun l => (H : ℝ) / l) 1 hLower hUpper hBracket hTest
    (fun l hl => abs_card_dvd_affine_sub_le_one offset step l H
      (Nat.pos_of_dvd_of_pos (hDivisors l hl) hW) (hStep.coprime_dvd_right (hDivisors l hl)))
  have hHReal : 0 < (H : ℝ) := by exact_mod_cast hH
  have hFactor :
      (∑ l ∈ divisors, (upper l - lower l) * ((H : ℝ) / l)) =
        (∑ l ∈ divisors, (upper l - lower l) / (l : ℝ)) * (H : ℝ) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l hl
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  rw [Complex.norm_div, Complex.norm_natCast]
  refine (div_le_div_of_nonneg_right hMidpoint hHReal.le).trans_eq ?_
  rw [hFactor, mul_one, add_div, add_div]
  congr 2
  field_simp
  ring


/-- Exact reciprocal sum over the exceptional divisors that are multiples
of the approximating denominator. -/
theorem sum_inv_multiples_eq_harmonic (D r : ℕ) (hr : 0 < r) :
    (∑ l ∈ (Finset.Icc 1 D).filter (fun l => r ∣ l), (l : ℝ)⁻¹) =
      (harmonic (D / r) : ℝ) / r := by
  let multiply : ℕ ↪ ℕ := ⟨fun l => l * r, fun {_ _} h => Nat.mul_right_cancel hr h⟩
  have hMultiples : (Finset.Icc 1 D).filter (fun l => r ∣ l) =
      (Finset.Icc 1 (D / r)).map multiply := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_map, Function.Embedding.coeFn_mk,
      multiply]
    constructor
    · rintro ⟨⟨hl, hUpper⟩, ⟨m, rfl⟩⟩
      have hm : 1 ≤ m := by
        cases m with
        | zero => simp at hl
        | succ m => omega
      exact ⟨m, ⟨hm, (Nat.le_div_iff_mul_le hr).2 (by simpa [Nat.mul_comm] using hUpper)⟩,
        Nat.mul_comm m r⟩
    · rintro ⟨m, ⟨hm, hUpper⟩, rfl⟩
      exact ⟨⟨Nat.mul_pos hm hr, (Nat.le_div_iff_mul_le hr).1 hUpper⟩,
        ⟨m, Nat.mul_comm m r⟩⟩
  rw [hMultiples, Finset.sum_map, harmonic_eq_sum_Icc]
  push_cast
  simp only [multiply, Function.Embedding.coeFn_mk, Nat.cast_mul, mul_inv_rev, div_eq_mul_inv,
    Finset.sum_mul, Finset.mul_sum, mul_comm]

/-- A logarithmic bound for the reciprocal sum over multiples of the
approximating prime, including the case where the cutoff is smaller
than that prime. -/
theorem sum_inv_multiples_le (D r : ℕ) (hr : 0 < r) :
    (∑ l ∈ (Finset.Icc 1 D).filter (fun l => r ∣ l), (l : ℝ)⁻¹) ≤
      (1 + Real.log ((max D 1 : ℕ) : ℝ)) / r := by
  rw [sum_inv_multiples_eq_harmonic D r hr]
  have hrReal : (0 : ℝ) < r := by exact_mod_cast hr
  apply div_le_div_of_nonneg_right _ hrReal.le
  by_cases hZero : D / r = 0
  · rw [hZero, harmonic_zero, Rat.cast_zero]
    have hLog : 0 ≤ Real.log ((max D 1 : ℕ) : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast (le_max_right D 1)
    linarith
  · have hPos : 0 < (↑(D / r) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hZero
    have hle : (↑(D / r) : ℝ) ≤ ((max D 1 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.div_le_self D r).trans (le_max_left D 1)
    exact (harmonic_le_one_add_log _).trans (add_le_add_left (Real.log_le_log hPos hle) 1)


/-- The Cramér term after bounding divisor correlations. The hypothesis on
the good divisors is a normalized cancellation bound on each subprogression.
The exceptional divisors use only boundedness of the test. The error from
the sieve weights is half of their reciprocal-weighted gap. -/
theorem cramerSieve_correlation_bound (W offset step H D r : ℕ) (divisors : Finset ℕ)
    (hW : 0 < W) (hH : 0 < H) (hr : 0 < r) (hStep : step.Coprime W)
    (hDivisors : ∀ l ∈ divisors, l ∣ W ∧ l ≤ D)
    (lower upper : ℕ → ℝ) (test : ℕ → ℂ) (ε gap : ℝ) (hε : 0 ≤ ε)
    (hLower : ∀ l ∈ divisors, |lower l| ≤ 1)
    (hUpper : ∀ l ∈ divisors, |upper l| ≤ 1)
    (hBracket : ∀ t ∈ Finset.range H,
      sieveDivisorSum divisors (fun l t => l ∣ offset + step * t) lower t ≤
        coprimeSieveIndicator W (offset + step * t) ∧
      coprimeSieveIndicator W (offset + step * t) ≤
        sieveDivisorSum divisors (fun l t => l ∣ offset + step * t) upper t)
    (hTest : ∀ t ∈ Finset.range H, ‖test t‖ ≤ 1)
    (hGap : (∑ l ∈ divisors, (upper l - lower l) / (l : ℝ)) ≤ gap)
    (hGood : ∀ l ∈ divisors, ¬r ∣ l →
      ‖∑ t ∈ (Finset.range H).filter (fun t => l ∣ offset + step * t), test t‖ ≤
        ε * (((Finset.range H).filter (fun t => l ∣ offset + step * t)).card : ℝ)) :
    ‖(∑ t ∈ Finset.range H, (coprimeSieveIndicator W (offset + step * t) : ℂ) * test t) /
        (H : ℂ)‖ ≤
      ε * (1 + Real.log ((max D 1 : ℕ) : ℝ)) +
      (1 + Real.log ((max D 1 : ℕ) : ℝ)) / r +
      gap / 2 + (2 + ε) * ((divisors.card : ℝ) / (H : ℝ)) := by
  let localPart (l : ℕ) := (Finset.range H).filter (fun t => l ∣ offset + step * t)
  let correlation (l : ℕ) : ℝ := ‖∑ t ∈ localPart l, test t‖
  let bad (l : ℕ) : ℝ := if r ∣ l then 1 else 0
  let reciprocal (l : ℕ) := (l : ℝ)⁻¹
  have hHReal : (0 : ℝ) < H := by exact_mod_cast hH
  have hLoc (l : ℕ) (hl : l ∈ divisors) :
      ((localPart l).card : ℝ) ≤ (H : ℝ) * reciprocal l + 1 := by
    have h := abs_card_dvd_affine_sub_le_one offset step l H
      (Nat.pos_of_dvd_of_pos (hDivisors l hl).1 hW)
      (hStep.coprime_dvd_right (hDivisors l hl).1)
    have h' := le_of_abs_le h
    dsimp [localPart, reciprocal]
    rw [← div_eq_mul_inv]
    linarith only [h']
  have hLocalBound (l : ℕ) (hl : l ∈ divisors) :
      correlation l ≤ (ε + bad l) * ((localPart l).card : ℝ) := by
    by_cases hBad : r ∣ l
    · have hTrivial : correlation l ≤ ((localPart l).card : ℝ) := by
        refine (norm_sum_le _ _).trans ?_
        simpa using Finset.sum_le_sum (s := localPart l)
          (g := fun _ => (1 : ℝ)) (fun t ht => hTest t (Finset.mem_filter.mp ht).1)
      simp only [bad, if_pos hBad]
      exact hTrivial.trans (le_mul_of_one_le_left (Nat.cast_nonneg _) (by linarith))
    · simpa [correlation, localPart, bad, hBad] using hGood l hl hBad
  have hPoint (l : ℕ) (hl : l ∈ divisors) :
      correlation l ≤
        ε * ((H : ℝ) * reciprocal l) + bad l * ((H : ℝ) * reciprocal l) + (ε + 1) := by
    have hBadNonneg : 0 ≤ bad l := by by_cases h : r ∣ l <;> simp [bad, h]
    have hBadLe : bad l ≤ 1 := by by_cases h : r ∣ l <;> simp [bad, h]
    have h := (hLocalBound l hl).trans
      (mul_le_mul_of_nonneg_left (hLoc l hl) (add_nonneg hε hBadNonneg))
    linarith only [h, hBadLe]
  have hSubset : divisors ⊆ Finset.Icc 1 D := by
    intro l hl
    exact Finset.mem_Icc.2 ⟨Nat.pos_of_dvd_of_pos (hDivisors l hl).1 hW, (hDivisors l hl).2⟩
  have hLog : (∑ l ∈ divisors, reciprocal l) ≤ 1 + Real.log ((max D 1 : ℕ) : ℝ) := by
    have h := Finset.sum_le_sum_of_subset_of_nonneg hSubset
      (f := reciprocal) (by intro l hl _; exact inv_nonneg.mpr (Nat.cast_nonneg l))
    refine h.trans ?_
    calc
      _ = (harmonic D : ℝ) := by
        rw [harmonic_eq_sum_Icc]
        push_cast
        rfl
      _ ≤ 1 + Real.log (D : ℝ) := harmonic_le_one_add_log D
      _ ≤ _ := by
        by_cases hD : D = 0
        · simp [hD]
        · exact add_le_add_left (Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hD)
            (by exact_mod_cast le_max_left D 1)) 1
  have hBadSum : (∑ l ∈ divisors, bad l * reciprocal l) ≤
      (1 + Real.log ((max D 1 : ℕ) : ℝ)) / r := by
    have hSubset' : divisors.filter (fun l => r ∣ l) ⊆
        (Finset.Icc 1 D).filter (fun l => r ∣ l) := Finset.filter_subset_filter _ hSubset
    have hRewrite : (∑ l ∈ divisors, bad l * reciprocal l) =
        ∑ l ∈ divisors.filter (fun l => r ∣ l), reciprocal l := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro l hl
      by_cases h : r ∣ l <;> simp [bad, h]
    rw [hRewrite]
    exact (Finset.sum_le_sum_of_subset_of_nonneg hSubset'
      (f := reciprocal) (by intro l hl _; exact inv_nonneg.mpr (Nat.cast_nonneg l))).trans
      (sum_inv_multiples_le D r hr)
  have hCorrelations : (∑ l ∈ divisors, correlation l) / (H : ℝ) ≤
      ε * (1 + Real.log ((max D 1 : ℕ) : ℝ)) +
      (1 + Real.log ((max D 1 : ℕ) : ℝ)) / r +
      (ε + 1) * ((divisors.card : ℝ) / (H : ℝ)) := by
    have h := Finset.sum_le_sum hPoint
    have hRewrite :
        (∑ l ∈ divisors,
          (ε * ((H : ℝ) * reciprocal l) + bad l * ((H : ℝ) * reciprocal l) + (ε + 1))) =
          ε * ((H : ℝ) * ∑ l ∈ divisors, reciprocal l) +
          (H : ℝ) * (∑ l ∈ divisors, bad l * reciprocal l) +
          (divisors.card : ℝ) * (ε + 1) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      congr 2
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      ring
      all_goals ring
    rw [hRewrite] at h
    apply (div_le_iff₀ hHReal).2
    have hFirst := mul_le_mul_of_nonneg_left hLog (mul_nonneg hε hHReal.le)
    have hSecond := mul_le_mul_of_nonneg_left hBadSum hHReal.le
    have hCancel : (((divisors.card : ℝ) / (H : ℝ)) * (H : ℝ)) = (divisors.card : ℝ) :=
      div_mul_cancel₀ _ hHReal.ne'
    nlinarith only [h, hFirst, hSecond, congrArg (fun z : ℝ => (ε + 1) * z) hCancel]
  have hMidpoint := cramerSieve_average_bound W offset step H divisors hW hH hStep
    (fun l hl => (hDivisors l hl).1) lower upper test hLower hUpper hBracket hTest
  change _ ≤ ((∑ l ∈ divisors, correlation l) / (H : ℝ)) +
    (∑ l ∈ divisors, (upper l - lower l) / (l : ℝ)) / 2 +
    (divisors.card : ℝ) / (H : ℝ) at hMidpoint
  linarith only [hMidpoint, hGap, hCorrelations]

end NilBohr
