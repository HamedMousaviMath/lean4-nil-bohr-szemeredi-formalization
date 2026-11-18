import NilBohr.CramerSieveWeight

/-! Dimension-one sieve inputs and their uniform specialization to the
cutoff and level of Proposition 6.2. -/

open Filter
open scoped BigOperators Topology

namespace NilBohr

/-- The divisors that can occur in the upper and lower weights at level D. -/
def sieveWeightDivisors (W D : ℕ) : Finset ℕ :=
  (Finset.Icc 1 D).filter (fun l => l ∣ W)

theorem mem_sieveWeightDivisors {W D l : ℕ} (hl : l ∈ sieveWeightDivisors W D) :
    l ∣ W ∧ l ≤ D :=
  ⟨(Finset.mem_filter.mp hl).2, (Finset.mem_Icc.mp (Finset.mem_filter.mp hl).1).2⟩

theorem card_sieveWeightDivisors_le (W D : ℕ) : (sieveWeightDivisors W D).card ≤ D := by
  unfold sieveWeightDivisors
  exact (Finset.card_filter_le _ _).trans (by simp [Nat.card_Icc])

/-- Pointwise bracketing on positive integers and the absolute error in the
expected divisor sum. The sum is restricted to the permitted support. -/
structure SieveBracketingWeights (W D : ℕ) (ε : ℝ) (lower upper : ℕ → ℝ) : Prop where
  lowerBound : ∀ l ∈ sieveWeightDivisors W D, |lower l| ≤ 1
  upperBound : ∀ l ∈ sieveWeightDivisors W D, |upper l| ≤ 1
  bracket : ∀ n : ℕ, 0 < n →
    sieveDivisorSum (sieveWeightDivisors W D) (fun l n => l ∣ n) lower n ≤
      coprimeSieveIndicator W n ∧
    coprimeSieveIndicator W n ≤
      sieveDivisorSum (sieveWeightDivisors W D) (fun l n => l ∣ n) upper n
  absoluteGap : |∑ l ∈ sieveWeightDivisors W D, (upper l - lower l) / (l : ℝ)| ≤ ε

theorem SieveBracketingWeights.gap {W D : ℕ} {ε : ℝ} {lower upper : ℕ → ℝ}
    (h : SieveBracketingWeights W D ε lower upper) :
    (∑ l ∈ sieveWeightDivisors W D, (upper l - lower l) / (l : ℝ)) ≤ ε :=
  (le_abs_self _).trans h.absoluteGap

/-- Euler product over the portion of a finite prime set lying in (u,v]. -/
noncomputable def primeIntervalEulerProduct (P : Finset ℕ) (u v : ℝ) : ℝ := by
  classical
  exact ∏ p ∈ P.filter (fun p : ℕ => u < (p : ℝ) ∧ (p : ℝ) ≤ v),
    (1 - ((p : ℕ) : ℝ)⁻¹)⁻¹

/-- The uniform interval consequence of Mertens' prime product estimate
(Koukoulopoulos, Theorem 3.4(c)). This is the dimension-one bound used
in the sieve axiom, with endpoints (u,v]. -/
def MertensIntervalProductBound : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ u v : ℝ, 3 / 2 ≤ u → u ≤ v →
    primeIntervalEulerProduct (primesThrough ⌊v⌋₊) u v ≤
      (1 + C / Real.log u) * (Real.log v / Real.log u)

/-- Dimension-one product hypothesis for the finite set of sieving primes. -/
def SieveDimensionOne (P : Finset ℕ) (C : ℝ) : Prop :=
  ∀ u v : ℝ, 3 / 2 ≤ u → u ≤ v →
    primeIntervalEulerProduct P u v ≤
      (1 + C / Real.log u) * (Real.log v / Real.log u)

/-- Dimension one and local densities 1/p in Koukoulopoulos, Theorem 19.1.
Only the difference of the two sieve main terms is retained. The
constant accounts for both relative errors in the source statement.
A valid interval product bound for all v in particular gives the
source condition up to the largest sieving prime. -/
def FundamentalSieveLemma : Prop :=
  ∀ C : ℝ, 1 ≤ C →
    ∃ (C₁ U₀ : ℝ) (D₀ : ℕ), 0 < C₁ ∧ 1 ≤ U₀ ∧ 2 ≤ D₀ ∧
      ∀ (P : Finset ℕ) (Q D : ℕ), P.Nonempty → P ⊆ primesThrough Q →
        2 ≤ Q → D₀ ≤ D → SieveDimensionOne P C →
        let U := Real.log (D : ℝ) / Real.log (Q : ℝ)
        U₀ ≤ U →
        ∃ lower upper : ℕ → ℝ,
          SieveBracketingWeights (∏ p ∈ P, p) D
            (C₁ * U ^ (-(U / 2)) * ∏ p ∈ P, (1 - (p : ℝ)⁻¹)) lower upper

private theorem primeEulerFactor_pos {p : ℕ} (hp : p.Prime) : 0 < 1 - (p : ℝ)⁻¹ := by
  have hp₂ : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  exact sub_pos.mpr (inv_lt_one_of_one_lt₀ (by linarith))

private theorem primeEulerFactor_le_one (p : ℕ) : 1 - (p : ℝ)⁻¹ ≤ 1 :=
  sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg _))

private theorem sieveDimensionOne_of_mertens {C : ℝ}
    (hM : ∀ u v : ℝ, 3 / 2 ≤ u → u ≤ v →
      primeIntervalEulerProduct (primesThrough ⌊v⌋₊) u v ≤
        (1 + C / Real.log u) * (Real.log v / Real.log u))
    {Q : ℕ} {P : Finset ℕ} (hP : P ⊆ primesThrough Q) :
    SieveDimensionOne P C := by
  classical
  intro u v hu huv
  have hv : 0 ≤ v := by linarith
  have hsubset : P.filter (fun p : ℕ => u < (p : ℝ) ∧ (p : ℝ) ≤ v) ⊆
      (primesThrough ⌊v⌋₊).filter (fun p : ℕ => u < (p : ℝ) ∧ (p : ℝ) ≤ v) := by
    intro p hp
    obtain ⟨hpP, hpRange⟩ := Finset.mem_filter.mp hp
    have hpPrime := (Finset.mem_filter.mp (hP hpP)).2
    have hpFloor := (Nat.le_floor_iff hv).mpr hpRange.2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hpFloor), hpPrime⟩, hpRange⟩
  calc
    primeIntervalEulerProduct P u v ≤ primeIntervalEulerProduct (primesThrough ⌊v⌋₊) u v := by
      let s := P.filter (fun p : ℕ => u < (p : ℝ) ∧ (p : ℝ) ≤ v)
      let t := (primesThrough ⌊v⌋₊).filter (fun p : ℕ => u < (p : ℝ) ∧ (p : ℝ) ≤ v)
      let f := fun p : ℕ => (1 - (p : ℝ)⁻¹)⁻¹
      change (∏ p ∈ s, f p) ≤ ∏ p ∈ t, f p
      have hfilter : t.filter (fun p => p ∈ s) = s := by
        ext p
        simp only [Finset.mem_filter]
        exact ⟨And.right, fun hp => ⟨hsubset hp, hp⟩⟩
      rw [← hfilter, Finset.prod_filter]
      apply Finset.prod_le_prod
      · intro p hp
        have hpPrime := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
        split_ifs
        · exact inv_nonneg.mpr (primeEulerFactor_pos hpPrime).le
        · exact zero_le_one
      · intro p hp
        have hpPrime := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
        split_ifs
        · exact le_rfl
        · exact (one_le_inv₀ (primeEulerFactor_pos hpPrime)).mpr (primeEulerFactor_le_one p)
    _ ≤ _ := hM u v hu huv

/-- Euler normalization for the Cramér weight, deduced using the single
fixed lower endpoint 3/2 in the interval form of Mertens' bound. -/
theorem MertensIntervalProductBound.eulerProduct_le_log (hM : MertensIntervalProductBound) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, 2 ≤ Q →
      (∏ p ∈ primesThrough Q, (1 - (p : ℝ)⁻¹)⁻¹) ≤ C * Real.log (Q : ℝ) := by
  classical
  obtain ⟨C, hC, hBound⟩ := hM
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hLog : 0 < Real.log (3 / 2 : ℝ) := Real.log_pos (by norm_num)
  refine ⟨(1 + C / Real.log (3 / 2 : ℝ)) / Real.log (3 / 2 : ℝ), by positivity, ?_⟩
  intro Q hQ
  have hQr : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hFilter : (primesThrough Q).filter
      (fun p : ℕ => (3 / 2 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Q) = primesThrough Q := by
    apply Finset.filter_eq_self.mpr
    intro p hp
    obtain ⟨hpQ, hpPrime⟩ := Finset.mem_filter.mp hp
    have hpTwo : (2 : ℝ) ≤ p := by exact_mod_cast hpPrime.two_le
    have hpQ' : p ≤ Q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hpQ)
    exact ⟨by linarith, by exact_mod_cast hpQ'⟩
  have hEq : primeIntervalEulerProduct (primesThrough ⌊(Q : ℝ)⌋₊) (3 / 2) Q =
      ∏ p ∈ primesThrough Q, (1 - (p : ℝ)⁻¹)⁻¹ := by
    rw [Nat.floor_natCast, primeIntervalEulerProduct, hFilter]
  have h := hBound (3 / 2) Q (by norm_num) (by linarith)
  rw [hEq] at h
  exact h.trans_eq (by ring)

/-- Logarithmic scale separation between the subexponential cutoff and
the floored polynomial sieve level. -/
private theorem eventually_sieve_level_ratio {c₀ : ℝ} (hc₀ : 0 ≤ c₀) (D₀ : ℕ) :
    ∀ᶠ X : ℕ in atTop,
      let Q := cramerCutoff c₀ X
      let D := ⌊(X : ℝ) ^ (1 / 20000 : ℝ)⌋₊
      2 ≤ Q ∧ D₀ ≤ D ∧
        (Real.log (X : ℝ)) ^ (1 - c₀) / 80000 ≤
          Real.log (D : ℝ) / Real.log (Q : ℝ) := by
  have hT : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hD : Tendsto (fun X : ℕ => (X : ℝ) ^ (1 / 20000 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : 0 < (1 / 20000 : ℝ))).comp tendsto_natCast_atTop_atTop
  filter_upwards [hT.eventually_ge_atTop 1, hT.eventually_ge_atTop (40000 * Real.log 2),
    eventually_ge_atTop (1 : ℕ), hD.eventually_ge_atTop (max 2 (D₀ : ℝ))]
      with X hX hXbig hX₁ hVbig
  let t := Real.log (X : ℝ)
  let Q := cramerCutoff c₀ X
  let V := (X : ℝ) ^ (1 / 20000 : ℝ)
  let D := ⌊V⌋₊
  have ht : 0 < t := zero_lt_one.trans_le hX
  have hXpos : 0 < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hVtwo : 2 ≤ V := (le_max_left _ _).trans hVbig
  have hVpos : 0 < V := by linarith
  obtain ⟨hQpos, hQlo, hQhi⟩ := cramerCutoff_log_bounds hc₀ hX
  have hlogQ : 0 < Real.log (Q : ℝ) := (Real.rpow_pos_of_pos ht _).trans_le hQlo
  have hQgt : (1 : ℝ) < Q := by
    by_contra! h
    exact (not_le_of_gt hlogQ) (Real.log_nonpos hQpos.le h)
  have hQtwo : 2 ≤ Q := by
    have hQone : 1 < Q := by exact_mod_cast hQgt
    omega
  have hD₀ : D₀ ≤ D :=
    (Nat.le_floor_iff hVpos.le).mpr ((le_max_right _ _).trans hVbig)
  have hVhalf : V / 2 ≤ (D : ℝ) := by
    have h := Nat.lt_floor_add_one V
    change V < (D : ℝ) + 1 at h
    linarith
  have hlogD : t / 40000 ≤ Real.log (D : ℝ) := by
    have h := Real.log_le_log (by positivity : 0 < V / 2) hVhalf
    rw [Real.log_div hVpos.ne' (by norm_num : (2 : ℝ) ≠ 0)] at h
    change Real.log ((X : ℝ) ^ (1 / 20000 : ℝ)) - Real.log 2 ≤ _ at h
    rw [Real.log_rpow hXpos] at h
    change 40000 * Real.log 2 ≤ t at hXbig
    linarith
  refine ⟨hQtwo, hD₀, (le_div_iff₀ hlogQ).mpr ?_⟩
  calc
    t ^ (1 - c₀) / 80000 * Real.log (Q : ℝ) ≤
        t ^ (1 - c₀) / 80000 * (2 * t ^ c₀) :=
      mul_le_mul_of_nonneg_left hQhi (by positivity)
    _ = t / 40000 := by
      rw [show t ^ (1 - c₀) / 80000 * (2 * t ^ c₀) =
        (t ^ (1 - c₀) * t ^ c₀) / 40000 by ring, ← Real.rpow_add ht]
      rw [show 1 - c₀ + c₀ = 1 by ring, Real.rpow_one]
    _ ≤ _ := hlogD

/-- At the level floor(X^(1/20000)) the absolute sieve gap saves any
prescribed power of log X, uniformly over the omitted primes. -/
theorem eventually_cramerSieve_coefficients (hM : MertensIntervalProductBound)
    (hS : FundamentalSieveLemma) {c₀ A : ℝ} (hc₀ : 0 < c₀) (hc₁ : c₀ < 1) (hA : 0 < A) :
    ∀ᶠ X : ℕ in atTop, ∀ q : ℕ,
      ∃ lower upper : ℕ → ℝ,
        SieveBracketingWeights (cramerSieveModulus (cramerCutoff c₀ X) q)
          ⌊(X : ℝ) ^ (1 / 20000 : ℝ)⌋₊ ((Real.log (X : ℝ)) ^ (-A)) lower upper := by
  classical
  obtain ⟨C, hC, hM⟩ := hM
  obtain ⟨C₁, U₀, D₀, hC₁, hU₀, hD₀, hS⟩ := hS C hC
  have hB : 0 < 1 - c₀ := sub_pos.mpr hc₁
  have hT : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hPow := (tendsto_rpow_atTop hB).comp hT
  have hSmall := (isLittleO_log_rpow_atTop hB).bound
    (show 0 < 1 / (160000 * A) by positivity)
  filter_upwards [eventually_sieve_level_ratio hc₀.le D₀, hT.eventually_ge_atTop 1,
    hPow.eventually_ge_atTop (80000 * max U₀ (Real.exp 2)),
    hPow.eventually_ge_atTop (160000 * Real.log C₁), hT.eventually hSmall]
    with X hScales hX hUbig hCbig hSmall
  intro q
  let t := Real.log (X : ℝ)
  let Q := cramerCutoff c₀ X
  let D := ⌊(X : ℝ) ^ (1 / 20000 : ℝ)⌋₊
  let P := (primesThrough Q).filter (fun p => ¬p ∣ q)
  let U := Real.log (D : ℝ) / Real.log (Q : ℝ)
  obtain ⟨hQ, hD, hU⟩ := hScales
  have hP : P ⊆ primesThrough Q := Finset.filter_subset _ _
  have hW : cramerSieveModulus Q q = ∏ p ∈ P, p := rfl
  have ht : 0 < t := zero_lt_one.trans_le hX
  have hGapNonneg : 0 ≤ t ^ (-A) := Real.rpow_nonneg ht.le _
  have hD₂ : 2 ≤ D := hD₀.trans hD
  by_cases hPempty : P = ∅
  · rw [show cramerSieveModulus (cramerCutoff c₀ X) q = 1 by
      rw [hW, hPempty, Finset.prod_empty]]
    have hDiv : sieveWeightDivisors 1 D = {1} := by
      ext l
      simp only [sieveWeightDivisors, Finset.mem_filter, Finset.mem_Icc, Nat.dvd_one,
        Finset.mem_singleton]
      refine ⟨And.right, ?_⟩
      rintro rfl
      exact ⟨⟨le_rfl, by omega⟩, rfl⟩
    refine ⟨fun _ => 1, fun _ => 1, ?_⟩
    constructor
    · simp
    · simp
    · intro n _
      change sieveDivisorSum (sieveWeightDivisors 1 D) (fun l m => l ∣ m) (fun _ => 1) n ≤
        coprimeSieveIndicator 1 n ∧ coprimeSieveIndicator 1 n ≤
          sieveDivisorSum (sieveWeightDivisors 1 D) (fun l m => l ∣ m) (fun _ => 1) n
      have hSum : sieveDivisorSum ({1} : Finset ℕ) (fun l m => l ∣ m) (fun _ => 1) n = 1 := by
        rw [sieveDivisorSum, Finset.sum_singleton, if_pos (one_dvd n)]
      rw [hDiv, hSum]
      simp [coprimeSieveIndicator]
    · simpa [hDiv] using hGapNonneg
  have hPne := Finset.nonempty_iff_ne_empty.mpr hPempty
  change t ^ (1 - c₀) / 80000 ≤ U at hU
  have hUlarge : max U₀ (Real.exp 2) ≤ U :=
    ((le_div_iff₀ (by norm_num : (0 : ℝ) < 80000)).mpr (by simpa [mul_comm] using hUbig)).trans hU
  have hUpos : 0 < U := (Real.exp_pos _).trans_le ((le_max_right _ _).trans hUlarge)
  obtain ⟨lower, upper, hWeights⟩ :=
    hS P Q D hPne hP hQ hD (sieveDimensionOne_of_mertens hM hP)
      ((le_max_left _ _).trans hUlarge)
  refine ⟨lower, upper, ?_⟩
  change SieveBracketingWeights (cramerSieveModulus Q q) D (t ^ (-A)) lower upper
  rw [hW]
  refine ⟨hWeights.lowerBound, hWeights.upperBound, hWeights.bracket, hWeights.absoluteGap.trans ?_⟩
  have hEuler :
      (∏ p ∈ P, (1 - (p : ℝ)⁻¹)) ≤ 1 :=
    Finset.prod_le_one
      (fun p hp => (primeEulerFactor_pos (Finset.mem_filter.mp (hP hp)).2).le)
      (fun p _ => primeEulerFactor_le_one p)
  have hUrate : U ^ (-(U / 2)) ≤ Real.exp (-U) := by
    have hlog := (Real.le_log_iff_exp_le hUpos).mpr ((le_max_right _ _).trans hUlarge)
    rw [Real.rpow_def_of_pos hUpos, Real.exp_le_exp]
    have hmul := mul_le_mul_of_nonneg_right hlog (show 0 ≤ U / 2 by positivity)
    nlinarith only [hmul]
  have hAsymp : Real.log C₁ + A * Real.log t ≤ U := by
    have hSmall' : Real.log t ≤ 1 / (160000 * A) * t ^ (1 - c₀) := by
      simpa [t, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hX),
        abs_of_nonneg (Real.rpow_nonneg ht.le _)] using hSmall
    have hAlog := mul_le_mul_of_nonneg_left hSmall' hA.le
    have hExact : A * (1 / (160000 * A) * t ^ (1 - c₀)) = t ^ (1 - c₀) / 160000 := by
      field_simp [hA.ne']
      ring
    rw [hExact] at hAlog
    change 160000 * Real.log C₁ ≤ t ^ (1 - c₀) at hCbig
    linarith
  calc
    C₁ * U ^ (-(U / 2)) * (∏ p ∈ P, (1 - (p : ℝ)⁻¹)) ≤ C₁ * U ^ (-(U / 2)) :=
      mul_le_of_le_one_right (by positivity) hEuler
    _ ≤ C₁ * Real.exp (-U) := mul_le_mul_of_nonneg_left hUrate hC₁.le
    _ = Real.exp (Real.log C₁ + -U) := by rw [Real.exp_add, Real.exp_log hC₁]
    _ ≤ t ^ (-A) := by
      rw [Real.rpow_def_of_pos ht, Real.exp_le_exp]
      nlinarith only [hAsymp]

end NilBohr
