import NilBohr.AmbientPrimeMean
import NilBohr.BohrPeriodic
import NilBohr.CramerModelMean
import NilBohr.GowersDilation
import NilBohr.GowersOrderComparison
import NilBohr.PrimeProgressions
import NilBohr.PrimeSiftedAverage
import NilBohr.SieveLiterature

/-! The fixed-modulus prime number theorem from the ambient prime model
and the dimension-one sieve inputs. -/

namespace NilBohr

open Filter
open scoped BigOperators Topology

private theorem residue_succ_iff {q : ℕ} (hq : 0 < q) (a n : ℕ) :
    n + 1 ≡ a [MOD q] ↔ n ≡ a + q - 1 [MOD q] := by
  have hshift : (a + q - 1) + 1 = a + q := Nat.sub_add_cancel (by omega)
  have ha : a + q ≡ a [MOD q] := by
    simp [Nat.ModEq, Nat.add_mod]
  constructor
  · intro h
    apply Nat.ModEq.add_right_cancel' 1
    rw [hshift]
    exact h.trans ha.symm
  · intro h
    exact ((h.add_right 1).trans (hshift ▸ ha))

private theorem localProgression_eq_image_range_succ (N a : ℕ) {q : ℕ} (hq : 0 < q) :
    localProgression 1 (N : ℤ) (a : ℤ) q =
      ((Finset.range N).filter (fun t => t ≡ a + q - 1 [MOD q])).image
        (fun t : ℕ => (t : ℤ) + 1) := by
  ext x
  simp only [localProgression, Finset.mem_filter, Finset.mem_Icc, Finset.mem_image,
    Finset.mem_range]
  constructor
  · rintro ⟨⟨hx₀, hx₁⟩, hx⟩
    let t := (x - 1).toNat
    have ht : (t : ℤ) + 1 = x := by dsimp [t]; omega
    refine ⟨t, ⟨by omega, (residue_succ_iff hq a t).mp ?_⟩, ht⟩
    apply Int.natCast_modEq_iff.mp
    rwa [Nat.cast_add, Nat.cast_one, ht]
  · rintro ⟨t, ⟨ht, hres⟩, rfl⟩
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    simpa only [Nat.cast_add, Nat.cast_one] using
      (Int.natCast_modEq_iff.mpr ((residue_succ_iff hq a t).mpr hres))

private theorem abs_card_fixedResidue_sub_le_one (N a : ℕ) {q : ℕ} (hq : 0 < q) :
    |((localProgression 1 (N : ℤ) (a : ℤ) q).card : ℝ) - (N : ℝ) / q| ≤ 1 := by
  rw [localProgression_eq_image_range_succ N a hq, Finset.card_image_of_injective _
    (fun i j e => by omega), ← Nat.count_eq_card_filter_range, Nat.count_modEq_card _ hq]
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hN : (N : ℝ) = (q : ℝ) * (↑(N / q) : ℝ) + (↑(N % q) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod N q).symm
  have hdivide : (N : ℝ) / q = (↑(N / q) : ℝ) + (↑(N % q) : ℝ) / q := by
    conv_lhs => rw [hN, add_div, mul_comm, mul_div_cancel_right₀ _ hq'.ne']
  have hrem₀ : 0 ≤ (↑(N % q) : ℝ) / q := by positivity
  have hrem₁ : (↑(N % q) : ℝ) / q ≤ 1 :=
    (div_le_one hq').mpr (by exact_mod_cast (Nat.mod_lt N hq).le)
  rw [hdivide]
  split_ifs <;> push_cast <;> rw [abs_le] <;> constructor <;> linarith

private theorem tendsto_fixedResidue_card_div (a : ℕ) {q : ℕ} (hq : 0 < q) :
    Tendsto (fun N : ℕ => ((localProgression 1 (N : ℤ) (a : ℤ) q).card : ℝ) / N)
      atTop (𝓝 ((q : ℝ)⁻¹)) := by
  have hNorm : Tendsto (fun N : ℕ =>
      ((localProgression 1 (N : ℤ) (a : ℤ) q).card : ℝ) / N - (q : ℝ)⁻¹) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_
      (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have hq' : (0 : ℝ) < q := by exact_mod_cast hq
    change |((localProgression 1 (N : ℤ) (a : ℤ) q).card : ℝ) / N - (q : ℝ)⁻¹| ≤ (N : ℝ)⁻¹
    rw [show ((q : ℝ)⁻¹) = (N / (q : ℝ)) / N by field_simp,
      ← sub_div, abs_div, abs_of_pos hN', ← one_div]
    exact div_le_div_of_nonneg_right (abs_card_fixedResidue_sub_le_one N a hq) hN'.le
  simpa only [sub_add_cancel, zero_add] using
    hNorm.add (tendsto_const_nhds (x := (q : ℝ)⁻¹))

private theorem coprime_of_mem_fixedResidue {N a q : ℕ} (ha : Nat.Coprime a q)
    {x : ℤ} (hx : x ∈ localProgression 1 (N : ℤ) (a : ℤ) q) : x.toNat.Coprime q := by
  obtain ⟨hxI, hxmod⟩ := Finset.mem_filter.mp hx
  have hx₀ : 0 ≤ x := by have := (Finset.mem_Icc.mp hxI).1; omega
  have hmod : x.toNat ≡ a [MOD q] := Int.natCast_modEq_iff.mp (by rwa [Int.toNat_of_nonneg hx₀])
  change x.toNat.gcd q = 1
  rw [Nat.gcd_comm, Nat.gcd_rec, hmod, ← Nat.gcd_rec, Nat.gcd_comm]
  exact ha

private theorem cramerSieve_excludedEulerProduct {Q q : ℕ} (hq : 0 < q) (hQ : q ≤ Q) :
    (∏ p ∈ (primesThrough Q).filter (fun p => p ∣ q), (1 - (p : ℝ)⁻¹)⁻¹) =
      (q : ℝ) / (q.totient : ℝ) := by
  have hFactors : q.primeFactors = (primesThrough Q).filter (fun p => p ∣ q) := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_primeFactors_of_ne_zero hq.ne']
    constructor
    · rintro ⟨hp, hdvd⟩
      exact ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le ((Nat.le_of_dvd hq hdvd).trans hQ)), hp⟩, hdvd⟩
    · rintro ⟨hp, hdvd⟩
      exact ⟨(Finset.mem_filter.mp hp).2, hdvd⟩
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hEuler : (q.totient : ℝ) = (q : ℝ) *
      ∏ p ∈ q.primeFactors, (1 - (p : ℝ)⁻¹) := by
    have h := congrArg (fun x : ℚ => (x : ℝ)) (Nat.totient_eq_mul_prod_factors q)
    push_cast at h
    exact h
  rw [hEuler, hFactors, div_mul_eq_div_div, div_self hqR.ne', one_div, Finset.prod_inv_distrib]

private theorem norm_cramerResidue_average_sub_le {Q N D q a : ℕ} {ε : ℝ}
    {lower upper : ℕ → ℝ} (hQ : 2 ≤ Q) (hqQ : q ≤ Q) (hq : 0 < q) (hqN : q ≤ N)
    (ha : a.Coprime q) (hε : 0 ≤ ε)
    (hWeights : SieveBracketingWeights (cramerSieveModulus Q q) D ε lower upper) :
    let P := localProgression 1 (N : ℤ) (a : ℤ) q
    ‖(∑ n ∈ P, cramerWeight Q n) / (N : ℂ) -
      (((q : ℝ) / q.totient : ℝ) : ℂ) * ((P.card : ℂ) / (N : ℂ))‖ ≤
      (∏ p ∈ primesThrough Q, (1 - (p : ℝ)⁻¹)⁻¹) * (ε + (D : ℝ) / (N : ℝ)) := by
  let P := localProgression 1 (N : ℤ) (a : ℤ) q
  have hPsubset : P ⊆ positiveInterval N := fun _ hx => (Finset.mem_filter.mp hx).1
  have hPne : P.Nonempty := localProgression_nonempty_of_step_le_card hq
    (show q ≤ (positiveInterval N).card by simpa only [card_positiveInterval] using hqN)
  let H := P.card
  have hH : 0 < H := Finset.card_pos.mpr hPne
  have hN : 0 < N := hq.trans_le hqN
  obtain ⟨a₀, _, hAP⟩ := localProgression_as_affine hq hPne
  obtain ⟨hOffset, hP⟩ := positiveProgression_eq_natImage hH
    (fun n hn => (Finset.mem_Icc.mp (hPsubset hn)).1) hAP
  let offset := (a₀ + (q : ℤ)).toNat
  change 0 < offset at hOffset
  let f (t : ℕ) := ((offset + q * t : ℕ) : ℤ)
  change P = (Finset.range H).image f at hP
  have hInj : Function.Injective f := by
    intro i j hij
    simp only [f, Int.natCast_inj] at hij
    exact Nat.eq_of_mul_eq_mul_left hq (Nat.add_left_cancel hij)
  have hf₀ : f 0 = (offset : ℤ) := by simp [f]
  have hOffMem : f 0 ∈ P := by
    rw [hP]
    exact Finset.mem_image_of_mem _ (Finset.mem_range.mpr hH)
  have hCoprime : offset.Coprime q := by
    simpa only [hf₀, Int.toNat_natCast] using coprime_of_mem_fixedResidue ha hOffMem
  have hb := norm_cramerWeight_progressionMean_sub_eulerProduct_le hQ hH hOffset hCoprime hWeights
  rw [cramerSieve_excludedEulerProduct hq hqQ] at hb
  change ‖(∑ t ∈ Finset.range H, cramerWeight Q (f t)) / (H : ℂ) -
    (((q : ℝ) / q.totient : ℝ) : ℂ)‖ ≤ _ at hb
  rw [← Finset.sum_image (fun _ _ _ _ hij => hInj hij), ← hP] at hb
  let W : ℝ := ∏ p ∈ primesThrough Q, (1 - (p : ℝ)⁻¹)⁻¹
  have hW : 0 ≤ W := by dsimp only [W]; rw [← cramerModulus_div_totient hQ]; positivity
  have hH₁ : (H : ℂ) ≠ 0 := by exact_mod_cast hH.ne'
  have hN₁ : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hH₂ : (0 : ℝ) < H := by exact_mod_cast hH
  have hN₂ : (0 : ℝ) < N := by exact_mod_cast hN
  have hSize : (H : ℝ) / N ≤ 1 := (div_le_one hN₂).mpr (by
    exact_mod_cast (Finset.card_le_card hPsubset).trans (card_positiveInterval N).le)
  change ‖(∑ n ∈ P, cramerWeight Q n) / (N : ℂ) -
    (((q : ℝ) / q.totient : ℝ) : ℂ) * ((H : ℂ) / (N : ℂ))‖ ≤ W * _
  rw [show (∑ n ∈ P, cramerWeight Q n) / (N : ℂ) -
      (((q : ℝ) / q.totient : ℝ) : ℂ) * ((H : ℂ) / (N : ℂ)) =
      ((H : ℂ) / (N : ℂ)) * ((∑ n ∈ P, cramerWeight Q n) / (H : ℂ) -
        (((q : ℝ) / q.totient : ℝ) : ℂ)) by
          rw [mul_sub, mul_comm ((H : ℂ) / (N : ℂ))
            (((q : ℝ) / q.totient : ℝ) : ℂ)]
          congr 1
          field_simp [hH₁, hN₁]
          ring,
    norm_mul, norm_div, Complex.norm_natCast, Complex.norm_natCast]
  calc
    _ ≤ ((H : ℝ) / N) * (W * (ε + (D : ℝ) / H)) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = W * (((H : ℝ) / N) * ε + (D : ℝ) / N) := by
      field_simp [hH₂.ne', hN₂.ne']
      ring
    _ ≤ W * (ε + (D : ℝ) / N) := mul_le_mul_of_nonneg_left
        (add_le_add_right (mul_le_of_le_one_left hε hSize) _) hW

private theorem tendsto_cramerResidue_mean {c₀ : ℝ} (hc₀ : 0 < c₀) (hc₁ : c₀ < 1)
    (hMertens : MertensIntervalProductBound) (hSieve : FundamentalSieveLemma)
    (q a : ℕ) (hq : 0 < q) (ha : a.Coprime q) :
    Tendsto (fun N : ℕ => (∑ n ∈ localProgression 1 (N : ℤ) (a : ℤ) q,
      cramerWeight (cramerCutoff c₀ N) n) / (N : ℂ)) atTop (𝓝 (((q.totient : ℝ)⁻¹ : ℝ) : ℂ)) := by
  let Q (N : ℕ) := cramerCutoff c₀ N
  let P (N : ℕ) := localProgression 1 (N : ℤ) (a : ℤ) q
  let H (N : ℕ) := (P N).card
  let m (N : ℕ) := (∑ n ∈ P N, cramerWeight (Q N) n) / (N : ℂ)
  let c := (((q : ℝ) / q.totient : ℝ) : ℂ)
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpow := (tendsto_rpow_atTop hc₀).comp hlog
  obtain ⟨C, hC, hEuler⟩ := hMertens.eulerProduct_le_log
  have hError : Tendsto (fun N : ℕ => m N - c * ((H N : ℂ) / (N : ℂ))) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_
      (by simpa only [mul_zero] using tendsto_cramerSieveLogError.const_mul (2 * C))
    filter_upwards [eventually_cramerSieve_coefficients hMertens hSieve hc₀ hc₁ (A := 2) (by norm_num),
      hlog.eventually_ge_atTop 1, hpow.eventually_ge_atTop (Real.log (max 2 q : ℕ)),
      eventually_ge_atTop q] with N hWeights hLog hPow hN
    let D := ⌊(N : ℝ) ^ (1 / 20000 : ℝ)⌋₊
    let ε := Real.log (N : ℝ) ^ (-2 : ℝ)
    have h₁ : 0 < (max 2 q : ℕ) := lt_of_lt_of_le (by decide) (le_max_left _ _)
    obtain ⟨hQpos, hQlog, hQhi⟩ := cramerCutoff_log_bounds hc₀.le hLog
    have hQge : max 2 q ≤ Q N := by
      exact_mod_cast (Real.log_le_log_iff (by exact_mod_cast h₁) hQpos).mp (hPow.trans hQlog)
    have hQ₂ := (le_max_left 2 q).trans hQge
    have hqQ := (le_max_right 2 q).trans hQge
    obtain ⟨lower, upper, hW⟩ := hWeights q
    have hε : 0 ≤ ε := by positivity
    have hnorm := norm_cramerResidue_average_sub_le hQ₂ hqQ hq hN ha hε hW
    change ‖m N - c * ((H N : ℂ) / (N : ℂ))‖ ≤ _ at hnorm
    have hLogQ : Real.log (Q N : ℝ) ≤ 2 * Real.log (N : ℝ) := hQhi.trans
      (mul_le_mul_of_nonneg_left (by simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hLog hc₁.le) (by norm_num))
    calc
      _ ≤ (C * Real.log (Q N : ℝ)) * (ε + (D : ℝ) / (N : ℝ)) := hnorm.trans
        (mul_le_mul_of_nonneg_right (hEuler (Q N) hQ₂) (by positivity))
      _ ≤ (C * (2 * Real.log (N : ℝ))) * (ε + (D : ℝ) / (N : ℝ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLogQ hC.le) (by positivity)
      _ = _ := by dsimp only [D, ε]; ring
  have hCard : Tendsto (fun N : ℕ => (H N : ℂ) / (N : ℂ))
      atTop (𝓝 (((q : ℝ)⁻¹ : ℝ) : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofReal_div, Complex.ofReal_natCast, H, P] using
      (Complex.continuous_ofReal.tendsto ((q : ℝ)⁻¹)).comp (tendsto_fixedResidue_card_div a hq)
  have hCenter : c * (((q : ℝ)⁻¹ : ℝ) : ℂ) = (((q.totient : ℝ)⁻¹ : ℝ) : ℂ) := by
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    rw [← Complex.ofReal_mul]
    congr 1
    dsimp only [c]
    rw [div_mul_eq_mul_div, mul_inv_cancel₀ hqR, one_div]
  have hMain := hCard.const_mul c
  rw [hCenter] at hMain
  simpa only [sub_add_cancel, zero_add] using hError.add hMain

private theorem tendsto_mangoldtResidue_sub_cramer_mean {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hc₁ : c₀ < 1 / 11) (hBanks : BanksRealZeroBound) (hAmbient : KMTTAmbientPrimeModel c₀)
    (q a : ℕ) (hq : 0 < q) :
    Tendsto (fun N : ℕ => (∑ n ∈ localProgression 1 (N : ℤ) (a : ℤ) q,
      (mangoldtWeight n - cramerWeight (cramerCutoff c₀ N) n)) / (N : ℂ)) atTop (𝓝 0) := by
  obtain ⟨A, hA, hModel⟩ := ambient_cramer_log_saving_of_kmtt hc₀ hc₁ hBanks hAmbient
    (S := 2) (by decide) (A := 1) (by norm_num)
  obtain ⟨C, hC, hMean⟩ := normalizedGowers_meanBound_of_adjacent
    normalizedGowersAdjacentMonotonicity 2 (by decide)
  have hlim : Tendsto (fun N : ℕ => C * (A * (Real.log (N : ℝ)) ^ (-1 : ℝ))) atTop (𝓝 0) := by
    have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    simpa only [Real.rpow_neg_one, mul_zero] using ((tendsto_inv_atTop_zero.comp hlog).const_mul A).const_mul C
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ hlim
  filter_upwards [hModel, eventually_gt_atTop (0 : ℕ)] with N hMN hN
  let f (n : ℤ) := mangoldtWeight n - cramerWeight (cramerCutoff c₀ N) n
  let g (n : ℤ) := if (q : ℤ) ∣ n - (a : ℤ) then f n else 0
  have hNZ : (1 : ℤ) ≤ N := by exact_mod_cast hN
  have hs : (∑ n ∈ localProgression 1 (N : ℤ) (a : ℤ) q, f n) =
      ∑ n ∈ positiveInterval N, g n := by
    simp only [localProgression, Finset.sum_filter, positiveInterval, g]
    exact Finset.sum_congr rfl (fun n _ =>
      if_congr (Int.modEq_comm.trans Int.modEq_iff_dvd) rfl rfl)
  rw [hs]
  exact (hMean N hN g).trans (mul_le_mul_of_nonneg_left
    ((normalizedGowers_residue_restriction 1 (N : ℤ) 2 (by decide) hNZ q hq (a : ℤ) f).trans hMN)
    hC.le)

private theorem mangoldtResidue_mean_eq_nat_sum (N q a : ℕ) :
    (∑ n ∈ localProgression 1 (N : ℤ) (a : ℤ) q, mangoldtWeight n) / (N : ℂ) =
      (N : ℝ)⁻¹ • ∑ n ∈ Finset.range (N + 1), ArithmeticFunction.vonMangoldt n •
        primePredicateWeight (fun p => p ≡ a [MOD q]) n := by
  rw [← mangoldtMean_eq_nat_sum]
  congr 1
  simp only [localProgression, Finset.sum_filter, positiveInterval]
  apply Finset.sum_congr rfl
  intro n hn
  have hn' : 0 ≤ n := by have := (Finset.mem_Icc.mp hn).1; omega
  have hres : n.toNat ≡ a [MOD q] ↔ n ≡ (a : ℤ) [ZMOD (q : ℤ)] := by
    rw [← Int.natCast_modEq_iff, Int.toNat_of_nonneg hn']
  by_cases h : n ≡ (a : ℤ) [ZMOD (q : ℤ)] <;> simp [primePredicateWeight, hres, h]

/-- The fixed-modulus prime counting asymptotic in every reduced residue
class, from the ambient prime model and the sieve. The ordinary PNT supplied
here is used for the removal of logarithmic prime weights. -/
theorem primeNumberTheoremInProgressions_of_prime_model {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hc₁ : c₀ < 1 / 11) (hBanks : BanksRealZeroBound) (hAmbient : KMTTAmbientPrimeModel c₀)
    (hMertens : MertensIntervalProductBound) (hSieve : FundamentalSieveLemma)
    (hPNT : PrimeNumberTheorem) : PrimeNumberTheoremInProgressions := by
  intro q a hq ha
  let s (p : ℕ) : Prop := p ≡ a [MOD q]
  let d : ℝ := (q.totient : ℝ)⁻¹
  have hM := tendsto_mangoldtResidue_sub_cramer_mean hc₀ hc₁ hBanks hAmbient q a hq
  have hC := tendsto_cramerResidue_mean hc₀ (by linarith) hMertens hSieve q a hq ha
  have hlim := hM.add hC
  simp only [Finset.sum_sub_distrib, sub_div, sub_add_cancel, zero_add,
    mangoldtResidue_mean_eq_nat_sum] at hlim
  have hP : Tendsto (primeAverage (primePredicateWeight s)) atTop (𝓝 (d : ℂ)) :=
    tendsto_primeAverage_of_tendsto_mangoldt hPNT (B := 1)
      (fun n => by by_cases h : s n <;> simp [primePredicateWeight, h])
      (by simpa only [s, d] using hlim)
  have hAvg (N : ℕ) : primeAverage (primePredicateWeight s) N = (predicatePrimeDensity s N : ℂ) := by
    rw [predicatePrimeDensity_eq_weighted_one]
    simp [weightedPrimeAverage]
  have hd := (Complex.continuous_re.tendsto (d : ℂ)).comp (hP.congr hAvg)
  have hd' : Tendsto (predicatePrimeDensity s) atTop (𝓝 d) := by
    simpa only [Function.comp_def, Complex.ofReal_re] using hd
  have hD := hd'.mul hPNT.count
  simp only [mul_one] at hD
  refine hD.congr' ?_
  filter_upwards [hPNT.count.eventually_ne (by norm_num : (1 : ℝ) ≠ 0)] with N hN
  have hc : ((primesThrough N).card : ℝ) ≠ 0 := fun hz => hN (by simp [hz])
  simp only [predicatePrimeDensity, s]
  have hN₀ : (N : ℝ) ≠ 0 := fun hz => hN (by simp [hz])
  field_simp [hc, hN₀]
  ring

/-- The fixed-modulus prime number theorem from the same model and sieve
inputs as the ordinary prime number theorem. -/
theorem primeNumberTheoremInProgressions_of_kmtt_and_sieve {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hc₁ : c₀ < 1 / 11) (hBanks : BanksRealZeroBound) (hAmbient : KMTTAmbientPrimeModel c₀)
    (hMertens : MertensIntervalProductBound) (hSieve : FundamentalSieveLemma) :
    PrimeNumberTheoremInProgressions :=
  primeNumberTheoremInProgressions_of_prime_model hc₀ hc₁ hBanks hAmbient hMertens hSieve
    (primeNumberTheorem_of_cramer_mean hc₀ hc₁ hBanks hAmbient
      (tendsto_cramerWeight_mean hc₀ (by linarith) hMertens hSieve))

end NilBohr
