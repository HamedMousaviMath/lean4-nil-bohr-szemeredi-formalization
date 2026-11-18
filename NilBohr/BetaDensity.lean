import NilBohr.Definitions

/-! Prime-denominator construction of the dense class of admissible Liouville numbers. -/

open Filter Set

namespace NilBohr

private theorem eventually_power_lt_doubleExpSqrtLog (D : ℕ) :
    ∀ᶠ R : ℝ in atTop, R ^ D < Real.exp (Real.exp (Real.sqrt (Real.log R))) := by
  have hs : Tendsto (fun R : ℝ => Real.sqrt (Real.log R)) atTop atTop := by
    simpa only [Real.sqrt_eq_rpow, Function.comp_apply] using
      (tendsto_rpow_atTop (show 0 < (1 / 2 : ℝ) by norm_num)).comp Real.tendsto_log_atTop
  have hD : 0 < (D : ℝ) + 1 := by positivity
  have he : ∀ᶠ t : ℝ in atTop, ((D : ℝ) + 1) * t ^ 2 ≤ Real.exp t := by
    filter_upwards [(isLittleO_rpow_exp_atTop (2 : ℝ)).bound (one_div_pos.mpr hD)]
      with t ht
    simp only [Real.rpow_two, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t),
      abs_of_pos (Real.exp_pos t), one_div_mul_eq_div] at ht
    exact mul_comm (t ^ 2) ((D : ℝ) + 1) ▸ (le_div_iff₀ hD).mp ht
  filter_upwards [eventually_gt_atTop (1 : ℝ), hs.eventually he] with R hR hpow
  have hR' : 0 < R := by linarith
  have hlog : 0 < Real.log R := Real.log_pos hR
  have hsq := Real.sq_sqrt hlog.le
  apply (Real.log_lt_log_iff (pow_pos hR' _) (Real.exp_pos _)).1
  rw [Real.log_pow, Real.log_exp]
  rw [hsq] at hpow
  linarith

private theorem exists_prime_above_denominatorScale (r : ℕ) :
    ∃ p : ℕ, p.Prime ∧ denominatorScale r < (p : ℝ) ∧
      (p : ℝ) ≤ 4 * denominatorScale r := by
  have hscale : 1 ≤ denominatorScale r := by
    unfold denominatorScale
    exact Real.one_le_exp (Real.exp_pos _).le
  let R := ⌈denominatorScale r⌉₊
  have hR : 0 < R := by
    have h := (show (1 : ℝ) ≤ denominatorScale r from hscale).trans
      (Nat.le_ceil (denominatorScale r))
    exact_mod_cast h
  obtain ⟨p, hp, hlow, hhigh⟩ := Nat.exists_prime_lt_and_le_two_mul R hR.ne'
  have hR₂ : (R : ℝ) < denominatorScale r + 1 :=
    Nat.ceil_lt_add_one (zero_le_one.trans hscale)
  refine ⟨p, hp, (Nat.le_ceil _).trans_lt (by exact_mod_cast hlow), ?_⟩
  have hbound : (p : ℝ) ≤ 2 * (R : ℝ) := by exact_mod_cast hhigh
  linarith

private noncomputable def primeDenominatorSequence (seed : ℕ) : ℕ → ℕ
  | 0 => seed
  | j + 1 => Classical.choose (exists_prime_above_denominatorScale (primeDenominatorSequence seed j))

private theorem primeDenominatorSequence_step (seed j : ℕ) :
    (primeDenominatorSequence seed (j + 1)).Prime ∧
      denominatorScale (primeDenominatorSequence seed j) <
        (primeDenominatorSequence seed (j + 1) : ℝ) ∧
      (primeDenominatorSequence seed (j + 1) : ℝ) ≤
        4 * denominatorScale (primeDenominatorSequence seed j) :=
  Classical.choose_spec (exists_prime_above_denominatorScale _)

private noncomputable def roundedNumerator (r : ℕ → ℕ) (u : ℝ) : ℕ → ℕ
  | 0 => ⌊u * (r 0 : ℝ)⌋₊ + 1
  | j + 1 => ⌊((roundedNumerator r u j : ℝ) / (r j : ℝ)) * (r (j + 1) : ℝ)⌋₊ + 1

private theorem upwardRounding_interval (u : ℝ) (hu : 0 ≤ u) (p : ℕ) (hp : 0 < p) :
    u < (⌊u * (p : ℝ)⌋₊ + 1 : ℕ) / (p : ℝ) ∧
      (⌊u * (p : ℝ)⌋₊ + 1 : ℕ) / (p : ℝ) ≤ u + 1 / (p : ℝ) := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  push_cast
  constructor
  · exact (lt_div_iff₀ hp').2 (Nat.lt_floor_add_one _)
  · apply (div_le_iff₀ hp').2
    rw [add_mul, div_mul_cancel₀ _ hp'.ne']
    exact add_le_add_right (Nat.floor_le (mul_nonneg hu hp'.le)) 1

private theorem tail_bound_of_doubling (q : ℕ → ℝ) (r : ℕ → ℕ)
    (hr : ∀ j, 0 < r j) (hgrowth : ∀ j, 2 * r j ≤ r (j + 1))
    (hq : Monotone q) (hstep : ∀ j, q (j + 1) ≤ q j + 1 / (r (j + 1) : ℝ)) :
    ∀ j k, q k ≤ q j + 1 / (r j : ℝ) := by
  have hanti : Antitone (fun j => q j + 1 / (r j : ℝ)) := by
    apply antitone_nat_of_succ_le
    intro j
    have hpos : (0 : ℝ) < r j := by exact_mod_cast hr j
    have hpos' : (0 : ℝ) < r (j + 1) := by exact_mod_cast hr (j + 1)
    have hle : 2 * (r j : ℝ) ≤ r (j + 1) := by exact_mod_cast hgrowth j
    have hinv : 2 / (r (j + 1) : ℝ) ≤ 1 / (r j : ℝ) := by
      rw [div_le_div_iff₀ hpos' hpos, one_mul]
      exact hle
    rw [show (2 : ℝ) = 1 + 1 by norm_num, add_div] at hinv
    linarith [hstep j, hinv]
  intro j k
  rcases le_total k j with h | h
  · exact (hq h).trans (le_add_of_nonneg_right (by positivity))
  · exact (le_add_of_nonneg_right (show 0 ≤ 1 / (r k : ℝ) by positivity)).trans (hanti h)

set_option maxHeartbeats 1000000 in
/-- The prescribed prime-denominator approximation condition is dense in
the unit interval. The upper and lower growth constants and the positive
one-sided approximation error are witnessed by the construction. -/
theorem exists_admissibleBeta_between {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hv : v ≤ 1) :
    ∃ β : ℝ, u < β ∧ β < v ∧ AdmissibleBeta β := by
  obtain ⟨R, hR⟩ := eventually_atTop.1 (eventually_power_lt_doubleExpSqrtLog 2)
  obtain ⟨s, hs⟩ := exists_nat_gt (max R (2 / (v - u)))
  obtain ⟨seed, hseed, hseedPrime⟩ := Nat.exists_infinite_primes s
  have hseedR : R ≤ (seed : ℝ) := by
    exact (le_max_left _ _).trans (hs.le.trans (by exact_mod_cast hseed))
  have hseedSize : 2 / (v - u) < (seed : ℝ) := by
    exact (le_max_right _ _).trans_lt (hs.trans_le (by exact_mod_cast hseed))
  let r := primeDenominatorSequence seed
  have hstep (j : ℕ) := primeDenominatorSequence_step seed j
  have hprime (j : ℕ) : (r j).Prime := by
    cases j with
    | zero => exact hseedPrime
    | succ j => exact (hstep j).1
  have hgrowthR (j : ℕ) : R ≤ (r j : ℝ) ∧ 2 * r j ≤ r (j + 1) := by
    induction j with
    | zero =>
        refine ⟨hseedR, ?_⟩
        have h₂ : (2 : ℝ) ≤ r 0 := by exact_mod_cast (hprime 0).two_le
        have hlt := (hR (r 0 : ℝ) hseedR).trans (hstep 0).2.1
        exact_mod_cast (show 2 * (r 0 : ℝ) ≤ r 1 by nlinarith)
    | succ j ih =>
        have hR' : R ≤ (r (j + 1) : ℝ) :=
          ih.1.trans (by
            have h : (2 : ℝ) * (r j : ℝ) ≤ r (j + 1) := by exact_mod_cast ih.2
            linarith [(show 0 ≤ (r j : ℝ) by positivity)])
        refine ⟨hR', ?_⟩
        have h₂ : (2 : ℝ) ≤ r (j + 1) := by exact_mod_cast (hprime (j + 1)).two_le
        have hlt := (hR (r (j + 1) : ℝ) hR').trans (hstep (j + 1)).2.1
        exact_mod_cast (show 2 * (r (j + 1) : ℝ) ≤ r (j + 2) by nlinarith)
  have hr : ∀ j, 0 < r j := fun j => (hprime j).pos
  have hgrowth : ∀ j, 2 * r j ≤ r (j + 1) := fun j => (hgrowthR j).2
  have hrMono : StrictMono r := strictMono_nat_of_lt_succ fun j => by
    have h := hgrowth j
    have hj := hr j
    omega
  let a := roundedNumerator r u
  let q (j : ℕ) := (a j : ℝ) / (r j : ℝ)
  have hfirst : u < q 0 ∧ q 0 ≤ u + 1 / (r 0 : ℝ) :=
    upwardRounding_interval u hu (r 0) (hr 0)
  have hqstep (j : ℕ) : q j < q (j + 1) ∧
      q (j + 1) ≤ q j + 1 / (r (j + 1) : ℝ) :=
    upwardRounding_interval (q j) (by dsimp [q]; positivity) _ (hr (j + 1))
  have hqMono : StrictMono q := strictMono_nat_of_lt_succ fun j => (hqstep j).1
  have htail := tail_bound_of_doubling q r hr hgrowth hqMono.monotone (fun j => (hqstep j).2)
  let β := sSup (range q)
  have hbounded : BddAbove (range q) := ⟨q 0 + 1 / (r 0 : ℝ), by
    rintro _ ⟨k, rfl⟩; exact htail 0 k⟩
  have hβlow (j : ℕ) : q j < β :=
    (hqstep j).1.trans_le (le_csSup hbounded (mem_range_self (j + 1)))
  have hβup (j : ℕ) : β ≤ q j + 1 / (r j : ℝ) := by
    apply csSup_le (range_nonempty q)
    rintro _ ⟨k, rfl⟩
    exact htail j k
  have hβu : u < β := hfirst.1.trans (hβlow 0)
  have hβv : β < v := by
    have hr₀ : (0 : ℝ) < r 0 := by exact_mod_cast hr 0
    have hlarge : 2 / (v - u) < (r 0 : ℝ) := hseedSize
    have hsmall : 2 / (r 0 : ℝ) < v - u := by
      apply (div_lt_iff₀ hr₀).2
      rw [mul_comm]
      exact (div_lt_iff₀ (sub_pos.mpr huv)).1 hlarge
    rw [show (2 : ℝ) = 1 + 1 by norm_num, add_div] at hsmall
    linarith [hβup 0, hfirst.2]
  have hanum (j : ℕ) : 0 < a j ∧ a j < r j := by
    have hqpos : 0 < q j := hu.trans_lt (hfirst.1.trans_le (hqMono.monotone (Nat.zero_le j)))
    have hqsmall : q j < 1 := (hβlow j).trans (hβv.trans_le hv)
    have hrj : (0 : ℝ) < r j := by exact_mod_cast hr j
    have hapos : (0 : ℝ) < a j := by
      dsimp [q] at hqpos
      exact (div_pos_iff.mp hqpos).resolve_right (by aesop) |>.1
    have halt : (a j : ℝ) < r j := by
      simpa only [one_mul] using (div_lt_iff₀ hrj).1 hqsmall
    exact ⟨by exact_mod_cast hapos, by exact_mod_cast halt⟩
  refine ⟨β, hβu, hβv, hu.trans_lt hβu, hβv.trans_le hv, a, r, hrMono,
    hqMono, fun j => ⟨hprime j, (hanum j).1, (hanum j).2⟩,
    1, 4, 2, by norm_num, by norm_num, by norm_num, ?_⟩
  intro j
  have hupper := hβup (j + 1)
  have hqbound := (hqstep j).2
  have hsmall : β - q j ≤ 2 / (r (j + 1) : ℝ) := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, add_div]
    linarith
  exact ⟨by simpa only [one_mul] using (hstep j).2.1.le, (hstep j).2.2,
    sub_pos.mpr (hβlow j), hsmall⟩

/-- The one-sided error bound and the increasing denominators imply the
literal limit of the rational approximants used in the manuscript. -/
theorem tendsto_admissible_approximants (β D : ℝ) (a r : ℕ → ℕ)
    (hr : StrictMono r) (h : ∀ j, 0 < β - (a j : ℝ) / (r j : ℝ) ∧
      β - (a j : ℝ) / (r j : ℝ) ≤ D / (r (j + 1) : ℝ)) :
    Tendsto (fun j => (a j : ℝ) / (r j : ℝ)) atTop (nhds β) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  have hr' : StrictMono (fun j : ℕ => r (j + 1)) := hr.comp (by
    intro i j hij
    dsimp only
    omega)
  have hlim : Tendsto (fun j : ℕ => (r (j + 1) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hr'.tendsto_atTop
  obtain ⟨N, hN⟩ := eventually_atTop.1 <| hlim.eventually
    (eventually_gt_atTop (D / ε))
  refine ⟨N, fun j hj => ?_⟩
  have hpos : (0 : ℝ) < r (j + 1) := by
    exact_mod_cast (Nat.zero_le (r j)).trans_lt (hr (Nat.lt_succ_self j))
  rw [Real.dist_eq, abs_sub_comm, abs_of_pos (h j).1]
  apply (h j).2.trans_lt (div_lt_iff₀ hpos |>.2 ?_)
  have hl := (div_lt_iff₀ hε).1 (hN j hj)
  simpa only [mul_comm ε] using hl

/-- Every admissible choice is Liouville in the standard Mathlib sense. -/
theorem AdmissibleBeta.liouville {β : ℝ} (hβ : AdmissibleBeta β) : Liouville β := by
  obtain ⟨_, _, a, r, hr, _, hp, c, C, D, hc, _, hD, happ⟩ := hβ
  intro n
  have hrLim : Tendsto (fun j : ℕ => (r j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hr.tendsto_atTop
  have hEventually : ∀ᶠ j : ℕ in atTop,
      (r j : ℝ) ^ (n + 1) < denominatorScale (r j) ∧ D / c ≤ (r j : ℝ) := by
    exact (hrLim.eventually (eventually_power_lt_doubleExpSqrtLog (n + 1))).and
      (hrLim.eventually (eventually_ge_atTop (D / c)))
  obtain ⟨j, hj⟩ := hEventually.exists
  obtain ⟨hlo, _, hpos, hle⟩ := happ j
  have hR : (0 : ℝ) < r j := by exact_mod_cast (hp j).1.pos
  have hR' : (0 : ℝ) < r (j + 1) := by exact_mod_cast (hp (j + 1)).1.pos
  have hR2 : 1 < r j := (hp j).1.one_lt
  have hD' : D ≤ (r j : ℝ) * c := (div_le_iff₀ hc).1 hj.2
  have hs : D * (r j : ℝ) ^ n < (r (j + 1) : ℝ) := by
    calc
      _ ≤ ((r j : ℝ) * c) * (r j : ℝ) ^ n := by gcongr
      _ = c * (r j : ℝ) ^ (n + 1) := by rw [pow_succ]; ring
      _ < c * denominatorScale (r j) := mul_lt_mul_of_pos_left hj.1 hc
      _ ≤ _ := hlo
  have herror : |β - (a j : ℝ) / (r j : ℝ)| < 1 / (r j : ℝ) ^ n := by
    rw [abs_of_pos hpos]
    apply hle.trans_lt
    rw [div_lt_div_iff₀ hR' (pow_pos hR n), one_mul]
    exact hs
  refine ⟨(a j : ℤ), (r j : ℤ), by exact_mod_cast hR2, ?_, ?_⟩
  · simpa only [Int.cast_natCast] using (ne_of_gt (sub_pos.mp hpos))
  · simpa only [Int.cast_natCast] using herror

end NilBohr
