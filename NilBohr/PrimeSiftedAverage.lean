import NilBohr.CramerSieveWeight
import NilBohr.LocalPhases

/-! Reindexing and normalizations for the Cramér part of the prime phase estimate. -/

open Filter
open scoped Topology BigOperators

namespace NilBohr

/-- A positive one-based integer progression also has a zero-based
nonnegative affine parametrization. -/
theorem positiveProgression_eq_natImage {P : Finset ℤ} {H s : ℕ} {a : ℤ}
    (hH : 0 < H) (hP : ∀ m ∈ P, 1 ≤ m)
    (hAP : P = (positiveInterval H).image (fun t => a+(s : ℤ)*t)) :
    let offset := (a+(s : ℤ)).toNat
    0 < offset ∧ P = (Finset.range H).image (fun j => ((offset+s*j : ℕ) : ℤ)) := by
  let offset := (a+(s : ℤ)).toNat
  have hFirst : (1 : ℤ) ∈ positiveInterval H :=
    Finset.mem_Icc.mpr ⟨le_rfl, by exact_mod_cast hH⟩
  have hOffset : 1 ≤ a+(s : ℤ) := by
    have hmem : a+(s : ℤ)*(1 : ℤ) ∈ P := by rw [hAP]; exact Finset.mem_image_of_mem _ hFirst
    simpa only [mul_one] using hP _ hmem
  have hCast : (offset : ℤ) = a+(s : ℤ) :=
    Int.toNat_of_nonneg (by omega)
  have hoff : 0 < offset := by omega
  refine ⟨hoff, ?_⟩
  rw [hAP]
  ext m
  simp only [Finset.mem_image, Finset.mem_range, Finset.mem_Icc, positiveInterval]
  constructor
  · rintro ⟨t, ⟨ht₁, ht₂⟩, rfl⟩
    let j := (t-1).toNat
    have hj : (j : ℤ)+1 = t := by dsimp [j]; omega
    refine ⟨j, by omega, ?_⟩
    push_cast
    rw [hCast, ← hj]
    ring
  · rintro ⟨j, hj, rfl⟩
    refine ⟨(j : ℤ)+1, ⟨by omega, by omega⟩, ?_⟩
    push_cast
    rw [hCast]
    ring

/-- All values in the image of the shifted-prime change of variables
are coprime to the original modulus on a positive parameter interval. -/
theorem primeProgression_value_coprime {P : Finset ℤ} {q : ℕ}
    (hP : ∀ y ∈ P, 0 ≤ y) {m : ℤ} (hm : m ∈ P.image (fun y => (q : ℤ)*y+1)) :
    m.toNat.Coprime q := by
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hm
  have hycast : (y.toNat : ℤ) = y := Int.toNat_of_nonneg (hP y hy)
  have hre : ((q : ℤ)*y+1).toNat = q*y.toNat+1 := by
    rw [← Int.toNat_natCast (q*y.toNat+1)]
    push_cast
    rw [hycast]
  rw [hre, add_comm, Nat.coprime_add_mul_left_left]
  exact Nat.coprime_one_left _

/-- Every prime in the reduced sieve product is coprime to the original
step, including all powers of the original modulus. -/
theorem primeStep_coprime_cramerSieveModulus (Q q b : ℕ) :
    (q^b).Coprime (cramerSieveModulus Q q) := by
  rw [cramerSieveModulus, Nat.coprime_prod_right_iff]
  intro p hp
  obtain ⟨hp, hn⟩ := Finset.mem_filter.mp hp
  have hprime := (Finset.mem_filter.mp hp).2
  exact ((hprime.coprime_iff_not_dvd.mpr hn).symm).pow_left _

theorem cramerSieveModulus_pos (Q q : ℕ) : 0 < cramerSieveModulus Q q :=
  Finset.prod_pos fun _ hp => (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.pos

private theorem norm_phaseSum_le_of_phaseAverage (P : Finset ℤ) (g : ℤ → ℂ) (p : Polynomial ℝ)
    {ε : ℝ} (hg : ‖phaseAverage P g p‖ ≤ ε) :
    ‖∑ m ∈ P, g m*phase (-p.eval (m : ℝ))‖ ≤ ε * (P.card : ℝ) := by
  by_cases h : P.card = 0
  · simp [Finset.card_eq_zero.mp h]
  have hp : (0 : ℝ) < P.card := by exact_mod_cast Nat.pos_of_ne_zero h
  rw [phaseAverage, norm_div, Complex.norm_natCast] at hg
  exact (div_le_iff₀ hp).mp hg

set_option maxHeartbeats 800000 in
/-- Finite Cramér estimate on the reduced shifted-prime progression. The
good-divisor premise is an estimate on each divisor progression with its own
normalization. The conclusion uses the original progression normalization. -/
theorem norm_cramerPhaseAverage_le_of_sieve
    (Q q s offset H W D r : ℕ) (hQ : 2 ≤ Q) (hs : 0 < s) (hoffset : 0 < offset)
    (hH : 0 < H) (hW : W = cramerSieveModulus Q q) (hr : 0 < r)
    (hStep : s.Coprime W) (divisors : Finset ℕ)
    (hDivisors : ∀ l ∈ divisors, l ∣ W ∧ l ≤ D)
    (lower upper : ℕ → ℝ) (g : ℤ → ℂ) (p : Polynomial ℝ)
    {R ε gap : ℝ} (hR : 0 < R) (hε : 0 ≤ ε)
    (hLower : ∀ l ∈ divisors, |lower l| ≤ 1)
    (hUpper : ∀ l ∈ divisors, |upper l| ≤ 1)
    (hBracket : ∀ n : ℕ, 0 < n →
      sieveDivisorSum divisors (fun l k => l ∣ k) lower n ≤ coprimeSieveIndicator W n ∧
      coprimeSieveIndicator W n ≤ sieveDivisorSum divisors (fun l k => l ∣ k) upper n)
    (hGap : (∑ l ∈ divisors, (upper l-lower l)/(l : ℝ)) ≤ gap)
    {P : Finset ℤ} (hP : P = (Finset.range H).image (fun j => ((offset+s*j : ℕ) : ℤ)))
    (hReduced : ∀ m ∈ P, m.toNat.Coprime q)
    (hg : ∀ m ∈ P, ‖g m‖ ≤ R)
    (hGood : ∀ l ∈ divisors, ¬r ∣ l →
      ‖phaseAverage (P.filter (fun m => (l : ℤ) ∣ m)) g p‖ ≤ R*ε) :
    ‖phaseAverage P (fun m => cramerWeight Q m * g m) p‖ ≤
      (∏ l ∈ primesThrough Q, (1-(l : ℝ)⁻¹)⁻¹) * R *
      (ε * (1 + Real.log ((max D 1 : ℕ) : ℝ)) +
        (1 + Real.log ((max D 1 : ℕ) : ℝ)) / r + gap/2 +
        (2+ε)*((divisors.card : ℝ)/(H : ℝ))) := by
  classical
  let f : ℕ → ℤ := fun j => ((offset+s*j : ℕ) : ℤ)
  let w : ℝ := ∏ l ∈ primesThrough Q, (1-(l : ℝ)⁻¹)⁻¹
  let t : ℕ → ℂ := fun j => g (f j) * phase (-p.eval (f j : ℝ)) / (R : ℂ)
  have hR' : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  have hf : Function.Injective f := by
    intro i j hij
    simp only [f, Int.natCast_inj] at hij
    exact Nat.eq_of_mul_eq_mul_left hs (Nat.add_left_cancel hij)
  have hPi (j : ℕ) (hj : j ∈ Finset.range H) : f j ∈ P :=
    hP ▸ Finset.mem_image_of_mem f hj
  have hCard : P.card = H := by rw [hP, Finset.card_image_of_injective _ hf, Finset.card_range]
  have hPos (j : ℕ) : 0 < offset+s*j := by positivity
  have hw : 0 ≤ w := by dsimp [w]; rw [← cramerModulus_div_totient hQ]; positivity
  have hTest (j : ℕ) (hj : j ∈ Finset.range H) : ‖t j‖ ≤ 1 := by
    change ‖g (f j) * phase (-p.eval (f j : ℝ)) / (R : ℂ)‖ ≤ 1
    rw [norm_div, norm_mul, norm_phase, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hR.le, div_le_iff₀ hR, one_mul]
    exact hg _ (hPi j hj)
  have hFiltered (l : ℕ) :
      P.filter (fun m => (l : ℤ) ∣ m) =
        ((Finset.range H).filter (fun j => l ∣ offset+s*j)).image f := by
    rw [hP, Finset.filter_image]
    simp only [f, Int.natCast_dvd_natCast]
  have hGood' (l : ℕ) (hl : l ∈ divisors) (hrl : ¬r ∣ l) :
      ‖∑ j ∈ (Finset.range H).filter (fun j => l ∣ offset+s*j), t j‖ ≤
        ε * (((Finset.range H).filter (fun j => l ∣ offset+s*j)).card : ℝ) := by
    have h := norm_phaseSum_le_of_phaseAverage _ g p (hGood l hl hrl)
    rw [hFiltered, Finset.card_image_of_injective _ hf,
      Finset.sum_image (fun _ _ _ _ hij => hf hij)] at h
    simp only [t, ← Finset.sum_div, norm_div, Complex.norm_real, Real.norm_of_nonneg hR.le]
    apply (div_le_iff₀ hR).mpr
    convert h using 1
    ring
  have hSieve := cramerSieve_correlation_bound W offset s H D r divisors
    (hW.symm ▸ cramerSieveModulus_pos Q q) hH hr hStep hDivisors lower upper t ε gap hε
    hLower hUpper (fun j _ => hBracket _ (hPos j)) hTest hGap hGood'
  have hValue (j : ℕ) (hj : j ∈ Finset.range H) :
      cramerWeight Q (f j) = (w : ℂ)*(coprimeSieveIndicator W (offset+s*j) : ℂ) := by
    rw [cramerWeight_eq_sieveIndicator hQ _ (hReduced _ (hPi j hj)), hW]
    simp only [f, Int.toNat_natCast, w]
  have hReindex : phaseAverage P (fun m => cramerWeight Q m * g m) p =
      ((w : ℂ)*(R : ℂ)) *
        ((∑ j ∈ Finset.range H, (coprimeSieveIndicator W (offset+s*j) : ℂ)*t j)/(H : ℂ)) := by
    rw [phaseAverage, hCard, hP, Finset.sum_image (fun _ _ _ _ hij => hf hij), ← mul_div_assoc,
      Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [hValue j hj]
    dsimp [t]
    field_simp
    ring
  rw [hReindex, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg hw, Real.norm_of_nonneg hR.le]
  exact mul_le_mul_of_nonneg_left hSieve (mul_nonneg hw hR.le)

/-- The quantitative errors in the finite sieve bound give one additional
inverse logarithm before the Euler product is put back. -/
theorem eventually_siftedPhase_error {A : ℝ} (hA : 0 < A) :
    ∀ᶠ X : ℕ in atTop,
      1 ≤ Real.log (X : ℝ) ∧ ∀ (D H r S : ℕ),
      (D : ℝ) ≤ (X : ℝ)^(1/20000 : ℝ) →
      (X : ℝ)^(1/2 : ℝ) ≤ H → Real.log (X : ℝ) ^ (A+2) ≤ r → S ≤ D →
      let t := Real.log (X : ℝ)
      let ε := 2*t^(-(A+2))
      ε*(1+Real.log ((max D 1 : ℕ) : ℝ)) +
      (1+Real.log ((max D 1 : ℕ) : ℝ))/(r : ℝ) +
      t^(-(A+1))/2 + (2+ε)*((S : ℝ)/(H : ℝ)) ≤ 11*t^(-(A+1)) := by
  let a : ℝ := 1/20000
  let b : ℝ := 1/2
  have hab : 0 < b-a := by norm_num [a,b]
  have hLogN : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall := (isLittleO_log_rpow_rpow_atTop (A+1) hab).bound
    (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [hLogN.eventually_ge_atTop 1,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hsmall,
    eventually_ge_atTop (1 : ℕ)] with X hlog hsmall hX
  refine ⟨hlog, ?_⟩
  intro D H r S hD hH hr hS
  let t := Real.log (X : ℝ)
  let ε := 2*t^(-(A+2))
  have ht : 0 < t := zero_lt_one.trans_le hlog
  have hX' : (0 : ℝ) < X := by exact_mod_cast zero_lt_one.trans_le hX
  have hX₁ : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hDmax : ((max D 1 : ℕ) : ℝ) ≤ (X : ℝ)^a := by
    rw [Nat.cast_max, Nat.cast_one]
    exact max_le hD (Real.one_le_rpow hX₁ (by norm_num [a]))
  have hLogD : 1+Real.log ((max D 1 : ℕ) : ℝ) ≤ 2*t := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < (max D 1 : ℕ)) hDmax
    rw [Real.log_rpow hX'] at h
    change Real.log ((max D 1 : ℕ) : ℝ) ≤ (1/20000:ℝ) * Real.log (X : ℝ) at h
    change 1+Real.log ((max D 1 : ℕ) : ℝ) ≤ 2*Real.log (X : ℝ)
    linarith only [h, hlog]
  have hMagnitude : t^(A+1) ≤ (X : ℝ)^(b-a) := by
    change ‖t^(A+1)‖ ≤ 1*‖(X : ℝ)^(b-a)‖ at hsmall
    rwa [Real.norm_of_nonneg (Real.rpow_nonneg ht.le (A+1)),
      Real.norm_of_nonneg (Real.rpow_nonneg hX'.le (b-a)), one_mul] at hsmall
  have hRatio : (S : ℝ)/(H : ℝ) ≤ t^(-(A+1)) := by
    have hS' : (S : ℝ) ≤ (X : ℝ)^a := (by exact_mod_cast hS : (S : ℝ) ≤ D).trans hD
    have hXpow : 0 < (X : ℝ)^b := Real.rpow_pos_of_pos hX' _
    calc
      _ ≤ (X : ℝ)^a / (X : ℝ)^b := by
        exact div_le_div₀ (Real.rpow_nonneg hX'.le _) hS' hXpow hH
      _ = (X : ℝ)^(a-b) := (Real.rpow_sub hX' _ _).symm
      _ ≤ _ := by
        rw [show a-b = -(b-a) by ring, Real.rpow_neg hX'.le, Real.rpow_neg ht.le]
        exact inv_anti₀ (Real.rpow_pos_of_pos ht _) hMagnitude
  have he : t * t^(-(A+2)) = t^(-(A+1)) := by
    calc
      _ = t^(1 : ℝ) * t^(-(A+2)) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add ht, show 1 + (-(A+2)) = -(A+1) by ring]
  have hFirst : ε*(1+Real.log ((max D 1 : ℕ) : ℝ)) ≤ 4*t^(-(A+1)) := by
    calc
      _ ≤ ε*(2*t) := mul_le_mul_of_nonneg_left hLogD (by dsimp [ε]; positivity)
      _ = _ := by dsimp [ε]; rw [← he]; ring
  have hSecond : (1+Real.log ((max D 1 : ℕ) : ℝ))/(r : ℝ) ≤ 2*t^(-(A+1)) := by
    calc
      _ ≤ (2*t)/t^(A+2) := div_le_div₀ (by positivity) hLogD (Real.rpow_pos_of_pos ht _) hr
      _ = _ := by rw [div_eq_mul_inv, ← Real.rpow_neg ht.le, ← he]; ring
  have hε : ε ≤ 2 := by
    have hp := Real.rpow_le_one_of_one_le_of_nonpos hlog (by linarith : -(A+2) ≤ 0)
    dsimp [ε]
    linarith only [hp]
  have hLast : (2+ε)*((S : ℝ)/(H : ℝ)) ≤ 4*t^(-(A+1)) :=
    mul_le_mul (by linarith only [hε]) hRatio (by positivity) (by norm_num)
  have hHalf : t^(-(A+1))/2 ≤ t^(-(A+1)) := by linarith [Real.rpow_nonneg ht.le (-(A+1))]
  change ε*(1+Real.log ((max D 1 : ℕ) : ℝ)) +
    (1+Real.log ((max D 1 : ℕ) : ℝ))/(r : ℝ) +
      t^(-(A+1))/2 + (2+ε)*((S : ℝ)/(H : ℝ)) ≤ 11*t^(-(A+1))
  linarith only [hFirst,hSecond,hHalf,hLast, Real.rpow_nonneg ht.le (-(A+1))]

end NilBohr
