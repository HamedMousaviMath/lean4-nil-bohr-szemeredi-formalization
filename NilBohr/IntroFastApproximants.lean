import NilBohr.BetaDensity

/-! The fast prime-denominator family used in the introductory obstruction. -/

open Filter Set
open scoped Topology

namespace NilBohr

private theorem exists_fast_prime (j r : ℕ) :
    ∃ p : ℕ, p.Prime ∧ 2*r ≤ p ∧
      2*Real.exp ((r : ℝ)^j) < (p : ℝ) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max (2*(r : ℝ)) (2*Real.exp ((r : ℝ)^j)))
  obtain ⟨p, hnp, hp⟩ := Nat.exists_infinite_primes n
  have hnp' : (n : ℝ) ≤ p := by exact_mod_cast hnp
  have hrp : 2*(r : ℝ) ≤ p := ((le_max_left _ _).trans_lt hn).le.trans hnp'
  exact ⟨p, hp, by exact_mod_cast hrp, ((le_max_right _ _).trans_lt hn).trans_le hnp'⟩

private noncomputable def fastDenominator : ℕ → ℕ
  | 0 => 3
  | j+1 => Classical.choose (exists_fast_prime j (fastDenominator j))

private theorem fastDenominator_step (j : ℕ) :
    (fastDenominator (j+1)).Prime ∧ 2*fastDenominator j ≤ fastDenominator (j+1) ∧
      2*Real.exp ((fastDenominator j : ℝ)^j) < (fastDenominator (j+1) : ℝ) :=
  Classical.choose_spec (exists_fast_prime j (fastDenominator j))

private noncomputable def fastNumerator (r : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | j+1 => ⌊((fastNumerator r j : ℝ)/(r j : ℝ)) * (r (j+1) : ℝ)⌋₊ + 1

private theorem fast_round_up (u : ℝ) (hu : 0 ≤ u) (r : ℕ) (hr : 0 < r) :
    u < (⌊u*(r : ℝ)⌋₊ + 1 : ℕ)/(r : ℝ) ∧
      (⌊u*(r : ℝ)⌋₊ + 1 : ℕ)/(r : ℝ) ≤ u+1/(r : ℝ) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  push_cast
  constructor
  · exact (lt_div_iff₀ hr').mpr (Nat.lt_floor_add_one _)
  · apply (div_le_iff₀ hr').mpr
    rw [add_mul, div_mul_cancel₀ _ hr'.ne']
    exact add_le_add_right (Nat.floor_le (mul_nonneg hu hr'.le)) 1

private theorem fast_tail (q : ℕ → ℝ) (r : ℕ → ℕ)
    (hr : ∀ j, 0 < r j) (hrgrowth : ∀ j, 2*r j ≤ r (j+1))
    (hq : Monotone q) (hqstep : ∀ j, q (j+1) ≤ q j+1/(r (j+1) : ℝ)) :
    ∀ j k, q k ≤ q j+1/(r j : ℝ) := by
  have hanti : Antitone (fun j => q j+1/(r j : ℝ)) := by
    apply antitone_nat_of_succ_le
    intro j
    have hpos : (0 : ℝ) < r j := by exact_mod_cast hr j
    have hpos' : (0 : ℝ) < r (j+1) := by exact_mod_cast hr (j+1)
    have hle : 2*(r j : ℝ) ≤ r (j+1) := by exact_mod_cast hrgrowth j
    have hinv : 2/(r (j+1) : ℝ) ≤ 1/(r j : ℝ) := by
      rw [div_le_div_iff₀ hpos' hpos, one_mul]
      exact hle
    rw [show (2 : ℝ) = 1+1 by norm_num, add_div] at hinv
    linarith only [hqstep j, hinv]
  intro j k
  rcases le_total k j with h | h
  · exact (hq h).trans (le_add_of_nonneg_right (by positivity))
  · exact (le_add_of_nonneg_right (show 0 ≤ 1/(r k : ℝ) by positivity)).trans (hanti h)

/-- There is a strictly increasing sequence of rational approximants with
strictly increasing prime denominators and error smaller than
(exp(-r_j^j)) at every index. -/
theorem exists_fast_prime_approximants :
    ∃ (β : ℝ) (a r : ℕ → ℕ), 0 < β ∧ β < 1 ∧ Irrational β ∧ StrictMono r ∧
      StrictMono (fun j => (a j : ℝ)/(r j : ℝ)) ∧
      Tendsto (fun j => (a j : ℝ)/(r j : ℝ)) atTop (𝓝 β) ∧
      ∀ j, (r j).Prime ∧ 0 < a j ∧ a j < r j ∧
        0 < β - (a j : ℝ)/(r j : ℝ) ∧
        β - (a j : ℝ)/(r j : ℝ) < Real.exp (-((r j : ℝ)^j)) := by
  let r := fastDenominator
  let a := fastNumerator r
  let q : ℕ → ℝ := fun j => (a j : ℝ)/(r j : ℝ)
  have hprime (j : ℕ) : (r j).Prime := by
    cases j with
    | zero => exact Nat.prime_three
    | succ j => exact (fastDenominator_step j).1
  have hr : ∀ j, 0 < r j := fun j => (hprime j).pos
  have hgrowth (j : ℕ) : 2*r j ≤ r (j+1) := (fastDenominator_step j).2.1
  have hindex (j : ℕ) : j+3 ≤ r j := by
    induction j with
    | zero => exact le_rfl
    | succ j ih =>
        have hg := hgrowth j
        omega
  have hrMono : StrictMono r :=
    strictMono_nat_of_lt_succ fun j => by have := hr j; have := hgrowth j; omega
  have hqstep (j : ℕ) :
      q j < q (j+1) ∧ q (j+1) ≤ q j+1/(r (j+1) : ℝ) :=
    fast_round_up (q j) (by dsimp [q]; positivity) _ (hr (j+1))
  have hqMono : StrictMono q := strictMono_nat_of_lt_succ fun j => (hqstep j).1
  have htail := fast_tail q r hr hgrowth hqMono.monotone (fun j => (hqstep j).2)
  let β := sSup (range q)
  have hbounded : BddAbove (range q) := ⟨q 0+1/(r 0 : ℝ), by
    rintro _ ⟨k,rfl⟩
    exact htail 0 k⟩
  have hβlow (j : ℕ) : q j < β :=
    (hqstep j).1.trans_le (le_csSup hbounded (mem_range_self (j+1)))
  have hβup (j : ℕ) : β ≤ q j+1/(r j : ℝ) := by
    apply csSup_le (range_nonempty q)
    rintro _ ⟨k,rfl⟩
    exact htail j k
  have hq0 : q 0 = 1/3 := by norm_num [q,a,r,fastNumerator,fastDenominator]
  have hβ0 : 0 < β := (by rw [hq0]; norm_num : 0 < q 0).trans (hβlow 0)
  have hβ1 : β < 1 := by
    have h := hβup 0
    rw [hq0] at h
    change β ≤ 1/3+1/(3 : ℝ) at h
    linarith only [h]
  have hErrBound (j : ℕ) : β-q j ≤ 2/(r (j+1) : ℝ) := by
    have h := hβup (j+1)
    have h' := (hqstep j).2
    rw [show (2 : ℝ) = 1+1 by norm_num, add_div]
    linarith only [h,h']
  have hErrSmall (j : ℕ) : β-q j < Real.exp (-((r j : ℝ)^j)) := by
    refine (hErrBound j).trans_lt ?_
    have hp : (0 : ℝ) < r (j+1) := by exact_mod_cast hr (j+1)
    rw [Real.exp_neg, div_lt_iff₀ hp, inv_mul_eq_div,
      lt_div_iff₀ (Real.exp_pos _)]
    exact (fastDenominator_step j).2.2
  have hanum (j : ℕ) : 0 < a j ∧ a j < r j := by
    have hqpos : 0 < q j := by
      exact (by rw [hq0]; norm_num : 0 < q 0).trans_le (hqMono.monotone (Nat.zero_le j))
    have hqsmall : q j < 1 := (hβlow j).trans hβ1
    have hrj : (0 : ℝ) < r j := by exact_mod_cast hr j
    have hapos : (0 : ℝ) < a j := (div_pos_iff.mp hqpos).resolve_right (by aesop) |>.1
    have halt : (a j : ℝ) < r j := by
      simpa only [one_mul] using (div_lt_iff₀ hrj).mp hqsmall
    exact ⟨by exact_mod_cast hapos, by exact_mod_cast halt⟩
  have hLiouville : Liouville β := by
    intro n
    let j := n+2
    have hr' : (0 : ℝ) < r j := by exact_mod_cast hr j
    have hn : (n : ℝ) ≤ r j := by
      have hn₀ : n ≤ j+3 := by dsimp [j]; omega
      exact_mod_cast hn₀.trans (hindex j)
    have hs : (n : ℝ)*Real.log (r j : ℝ) ≤ (r j : ℝ)^j := by
      calc
        _ ≤ (n : ℝ)*(r j : ℝ) := mul_le_mul_of_nonneg_left
          ((Real.log_le_sub_one_of_pos hr').trans (sub_le_self _ zero_le_one)) (by positivity)
        _ ≤ (r j : ℝ)^2 := by rw [pow_two]; exact mul_le_mul_of_nonneg_right hn hr'.le
        _ ≤ _ := pow_le_pow_right₀ (by exact_mod_cast hr j) (by dsimp [j]; omega)
    have hp : Real.exp (-((r j : ℝ)^j)) ≤ 1/(r j : ℝ)^n := by
      rw [one_div, ← Real.exp_log (pow_pos hr' n), ← Real.exp_neg,
        Real.exp_le_exp, Real.log_pow, neg_le_neg_iff]
      exact hs
    refine ⟨(a j : ℤ), (r j : ℤ), by exact_mod_cast (hprime j).one_lt,
      ?_, ?_⟩
    · simpa only [Int.cast_natCast] using (ne_of_gt (hβlow j))
    · simp only [Int.cast_natCast]
      change |β-q j| < 1/(r j : ℝ)^n
      rw [abs_of_pos (sub_pos.mpr (hβlow j))]
      exact (hErrSmall j).trans_le hp
  refine ⟨β,a,r,hβ0,hβ1,hLiouville.irrational,hrMono,hqMono,?_,?_⟩
  · exact tendsto_admissible_approximants β 2 a r hrMono
      (fun j => ⟨sub_pos.mpr (hβlow j), hErrBound j⟩)
  · intro j
    exact ⟨hprime j,(hanum j).1,(hanum j).2,sub_pos.mpr (hβlow j),hErrSmall j⟩

end NilBohr
