import NilBohr.DensityParameters

/-! The small-modulus comparison at the end of Appendix A. -/

open Filter
open scoped Topology

namespace NilBohr

/-- A modulus reached within the density-increment horizon is bounded by
a fixed inverse power of the initial density. The factorial estimate for
`initialModulus` suffices here, with a larger fixed exponent. -/
theorem log_iteration_modulus_le_density_power {η δ b K E : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hb : 1 ≤ b)
    (hK : 0 < K) (hE : 0 ≤ E) {i q : ℕ} (hi : i ≤ densityIterationSteps η δ)
    (hq : Real.log (q : ℝ) ≤
      b ^ i * Real.log (initialModulus ⌈K * δ ^ (-E)⌉₊ : ℝ)) :
    Real.log (q : ℝ) ≤ b * (K + 1)^2 *
      δ ^ (-(Real.log b / Real.log (1 + η) + 2 * E)) := by
  let w := ⌈K * δ ^ (-E)⌉₊
  have hwpos : (0 : ℝ) < w :=
    (mul_pos hK (Real.rpow_pos_of_pos hδ _)).trans_le (Nat.le_ceil _)
  have hlogw : Real.log (w : ℝ) ≤ w := by
    linarith [Real.log_le_sub_one_of_pos hwpos]
  have hlogMod : Real.log (initialModulus w : ℝ) ≤ (w : ℝ)^2 :=
    (log_initialModulus_le w).trans (by
      simpa only [pow_two] using mul_le_mul_of_nonneg_left hlogw hwpos.le)
  have hδE : 1 ≤ δ ^ (-E) := by
    simpa using Real.rpow_le_rpow_of_exponent_ge hδ hδ₁ (show -E ≤ 0 by linarith)
  have hceil : (w : ℝ) < K * δ ^ (-E) + 1 :=
    Nat.ceil_lt_add_one (mul_nonneg hK.le (Real.rpow_nonneg hδ.le _))
  have hw : (w : ℝ) ≤ (K + 1) * δ ^ (-E) := by
    rw [add_mul, one_mul]
    linarith
  have hsq := pow_le_pow_left₀ hwpos.le hw 2
  rw [mul_pow, ← Real.rpow_natCast (δ ^ (-E)), ← Real.rpow_mul hδ.le] at hsq
  norm_num only [Nat.cast_ofNat] at hsq
  have hpow := modulus_growth_to_density_power hη hδ hδ₁ hb hi
  calc
    _ ≤ b ^ i * (w : ℝ)^2 :=
      hq.trans (mul_le_mul_of_nonneg_left hlogMod (pow_nonneg (by linarith) i))
    _ ≤ (b * δ ^ (-(Real.log b / Real.log (1 + η)))) *
          ((K + 1)^2 * δ ^ (-E * 2)) :=
      mul_le_mul hpow hsq (sq_nonneg _) (by positivity)
    _ = _ := by
      rw [show -(Real.log b / Real.log (1 + η) + 2 * E) =
        -(Real.log b / Real.log (1 + η)) + (-E * 2) by ring, Real.rpow_add hδ]
      ring

/-- At initial density at least `(log log N)^(-c)`, the logarithm of the
stage modulus is uniformly `o(log log n)` over all stages whose length
and modulus satisfy the estimates from the density iteration. -/
theorem eventually_log_modulus_le_logLog_at_doubleLog_density {C D c : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hcD : c * D < 1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (δ : ℝ) (n q : ℕ),
      Real.log (Real.log (N : ℝ)) ^ (-c) ≤ δ →
      Real.log (N : ℝ) ^ (3 / 4 : ℝ) ≤ Real.log (n : ℝ) →
      Real.log (q : ℝ) ≤ C * δ ^ (-D) →
      0 < Real.log (Real.log (n : ℝ)) ∧
        Real.log (q : ℝ) / Real.log (Real.log (n : ℝ)) ≤ ε := by
  have hNlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hNloglog : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hNlog
  have hpower := (tendsto_rpow_atTop (sub_pos.mpr hcD)).comp hNloglog
  filter_upwards [hNlog.eventually (eventually_ge_atTop (1 : ℝ)),
    hNloglog.eventually (eventually_ge_atTop (1 : ℝ)),
    hpower.eventually (eventually_ge_atTop (C / (ε * (3 / 4))))]
    with N hLog hLogLog hPower δ n q hδ hn hq
  let t := Real.log (Real.log (N : ℝ))
  have ht : 0 < t := zero_lt_one.trans_le hLogLog
  have hLog' : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hLog
  have hlen := Real.log_le_log (Real.rpow_pos_of_pos hLog' (3 / 4 : ℝ)) hn
  rw [Real.log_rpow hLog'] at hlen
  change (3 / 4 : ℝ) * t ≤ Real.log (Real.log (n : ℝ)) at hlen
  have hlenpos : 0 < Real.log (Real.log (n : ℝ)) :=
    (mul_pos (by norm_num) ht).trans_le hlen
  refine ⟨hlenpos, (div_le_iff₀ hlenpos).mpr ?_⟩
  have hδPower := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos ht (-c)) hδ
    (neg_nonpos.mpr hD)
  rw [← Real.rpow_mul ht.le, neg_mul_neg] at hδPower
  have hcoef := (div_le_iff₀ (mul_pos hε (by norm_num : 0 < (3 / 4 : ℝ)))).mp hPower
  calc
    Real.log (q : ℝ) ≤ C * δ ^ (-D) := hq
    _ ≤ C * t ^ (c * D) := mul_le_mul_of_nonneg_left hδPower hC
    _ ≤ (t ^ (1 - c * D) * (ε * (3 / 4))) * t ^ (c * D) :=
      mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg ht.le _)
    _ = ε * ((3 / 4) * t) := by
      rw [mul_comm (t ^ (1 - c * D)), mul_assoc, ← Real.rpow_add ht,
        sub_add_cancel, Real.rpow_one, mul_assoc]
    _ ≤ ε * Real.log (Real.log (n : ℝ)) := mul_le_mul_of_nonneg_left hlen hε.le

/-- Any fixed modulus power is absorbed by a correspondingly larger
logarithmic phase saving, uniformly over all the same stages. -/
theorem eventually_small_modulus_absorbed_by_logarithmic_saving {C D c K A a : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hcD : c * D < 1) (hK : 0 ≤ K) (haA : a < A) :
    ∀ᶠ N : ℕ in atTop, ∀ (δ : ℝ) (n q : ℕ),
      Real.log (Real.log (N : ℝ)) ^ (-c) ≤ δ →
      Real.log (N : ℝ) ^ (3 / 4 : ℝ) ≤ Real.log (n : ℝ) →
      Real.log (q : ℝ) ≤ C * δ ^ (-D) → 0 < q →
      (q : ℝ) ^ K ≤ Real.log (n : ℝ) ^ (A - a) ∧
        (q : ℝ) ^ K * Real.log (n : ℝ) ^ (-A) ≤ Real.log (n : ℝ) ^ (-a) := by
  let ε := (A - a) / (K + 1)
  have hε : 0 < ε := div_pos (sub_pos.mpr haA) (by linarith)
  have hεK : K * ε ≤ A - a := by
    have h₁ : (K + 1) * ε = A - a := by
      dsimp only [ε]
      field_simp
    linarith
  have hNlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_log_modulus_le_logLog_at_doubleLog_density hC hD hcD hε,
    hNlog.eventually (eventually_ge_atTop (1 : ℝ))] with N hN hLog δ n q hδ hn hq hqpos
  obtain ⟨hloglog, hsmall⟩ := hN δ n q hδ hn hq
  have hLog' : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hLog
  have hnpos := (Real.rpow_pos_of_pos hLog' (3 / 4 : ℝ)).trans_le hn
  have hqpos' : (0 : ℝ) < q := by exact_mod_cast hqpos
  have hsmall' := (div_le_iff₀ hloglog).mp hsmall
  have hqpow : (q : ℝ) ^ K ≤ Real.log (n : ℝ) ^ (A - a) := by
    apply (Real.le_rpow_iff_log_le (Real.rpow_pos_of_pos hqpos' K) hnpos).mpr
    rw [Real.log_rpow hqpos']
    exact (mul_le_mul_of_nonneg_left hsmall' hK).trans <| by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hεK hloglog.le
  refine ⟨hqpow, (mul_le_mul_of_nonneg_right hqpow (Real.rpow_nonneg hnpos.le _)).trans_eq ?_⟩
  rw [← Real.rpow_add hnpos, show A - a + -A = -a by ring]

/-- The density-iteration form of the small-modulus comparison. The
modulus bound is the exact logarithmic iteration budget from Section 3,
and the cutoff is independent of the initial set and the stage index. -/
theorem eventually_density_iteration_moduli_small {η b K E c ε : ℝ}
    (hη : 0 < η) (hb : 1 ≤ b) (hK : 0 < K) (hE : 0 ≤ E)
    (hcD : c * (Real.log b / Real.log (1 + η) + 2 * E) < 1) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (δ : ℝ) (i n q : ℕ),
      Real.log (Real.log (N : ℝ)) ^ (-c) ≤ δ → δ ≤ 1 →
      i ≤ densityIterationSteps η δ → 0 < q →
      Real.log (N : ℝ) ^ (3 / 4 : ℝ) ≤ Real.log (n : ℝ) →
      Real.log (q : ℝ) ≤ b ^ i * Real.log (initialModulus ⌈K * δ ^ (-E)⌉₊ : ℝ) →
      0 < Real.log (Real.log (n : ℝ)) ∧
        Real.log (q : ℝ) / Real.log (Real.log (n : ℝ)) ≤ ε ∧
        (q : ℝ) ≤ Real.log (n : ℝ) ^ ε := by
  have hD : 0 ≤ Real.log b / Real.log (1 + η) + 2 * E :=
    add_nonneg (div_nonneg (Real.log_nonneg hb) (Real.log_nonneg (by linarith)))
      (mul_nonneg (by norm_num) hE)
  have hC : 0 ≤ b * (K + 1)^2 := mul_nonneg (by linarith) (sq_nonneg _)
  have hNlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hNloglog := Real.tendsto_log_atTop.comp hNlog
  filter_upwards [eventually_log_modulus_le_logLog_at_doubleLog_density hC hD hcD hε,
    hNlog.eventually (eventually_ge_atTop (1 : ℝ)),
    hNloglog.eventually (eventually_ge_atTop (1 : ℝ))]
    with N hN hLog hLogLog δ i n q hδ hδ₁ hi hqpos hn hq
  have hδpos := (Real.rpow_pos_of_pos (zero_lt_one.trans_le hLogLog) (-c)).trans_le hδ
  have hnpos := (Real.rpow_pos_of_pos (zero_lt_one.trans_le hLog) (3 / 4 : ℝ)).trans_le hn
  have hqpos' : (0 : ℝ) < q := by exact_mod_cast hqpos
  obtain ⟨hln, hsmall⟩ := hN δ n q hδ hn
    (log_iteration_modulus_le_density_power hη hδpos hδ₁ hb hK hE hi hq)
  exact ⟨hln, hsmall, (Real.le_rpow_iff_log_le hqpos' hnpos).mpr ((div_le_iff₀ hln).mp hsmall)⟩

/-- Saturating the modulus budget by a power of the initial modulus
gives a smooth admissible modulus with logarithm at least half the budget. -/
private theorem exists_modulus_near_budget {w : ℕ} (hw : 2 ≤ w) :
    ∃ q : ℕ, 0 < q ∧ initialModulus w ∣ q ∧ ModulusSmooth w q ∧
      (w : ℝ)^2 / 2 < Real.log (q : ℝ) ∧ Real.log (q : ℝ) ≤ (w : ℝ)^2 := by
  let L := initialModulus w
  let R := Real.log (L : ℝ)
  have hL : 0 < L := initialModulus_pos w
  have hL₁ : 1 < L := by
    have hdiv : 2 ∣ L := Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr ⟨by decide, hw⟩)
    exact (by decide : 1 < 2).trans_le (Nat.le_of_dvd hL hdiv)
  have hR : 0 < R := Real.log_pos (by exact_mod_cast hL₁)
  have hwpos : (0 : ℝ) < w := by exact_mod_cast (show 0 < w by omega)
  have hlogw : Real.log (w : ℝ) ≤ (w : ℝ) / 2 := by
    have h := Real.log_le_sub_one_of_pos (div_pos hwpos (by norm_num : (0 : ℝ) < 2))
    rw [Real.log_div hwpos.ne' (by norm_num : (2 : ℝ) ≠ 0)] at h
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hRhalf : R ≤ (w : ℝ)^2 / 2 := calc
    _ ≤ (w : ℝ) * Real.log (w : ℝ) := log_initialModulus_le w
    _ ≤ (w : ℝ) * ((w : ℝ) / 2) := mul_le_mul_of_nonneg_left hlogw hwpos.le
    _ = _ := by ring
  let z := (w : ℝ)^2 / R
  let e := ⌊z⌋₊
  have hz : 1 ≤ z := by
    apply (le_div_iff₀ hR).mpr
    linarith [sq_nonneg (w : ℝ)]
  have he : 0 < e := by
    exact Nat.le_floor (show ((1 : ℕ) : ℝ) ≤ z by exact_mod_cast hz)
  have hcap : (e : ℝ) * R ≤ (w : ℝ)^2 :=
    (le_div_iff₀ hR).mp (Nat.floor_le (zero_le_one.trans hz))
  have hnear : (w : ℝ)^2 < ((e : ℝ) + 1) * R :=
    (div_lt_iff₀ hR).mp (Nat.lt_floor_add_one z)
  obtain ⟨hdiv, hsmooth⟩ :=
    modulus_power_preserves_prime_support he (dvd_refl L) (initialModulus_smooth w)
  refine ⟨L^e, pow_pos hL _, hdiv, hsmooth, ?_⟩
  rw [Nat.cast_pow, Real.log_pow]
  exact ⟨by nlinarith only [hnear, hRhalf], hcap⟩

/-- At polylogarithmic density the numerical hypotheses of Proposition 3.1
permit moduli larger than every fixed power of `log N`. The witnesses
are admissible choices of parameters for all densities at or above the
threshold, without requiring a particular sequence of increment stages. -/
theorem eventually_large_admissible_modulus_at_polylog_density {K E c κ : ℝ}
    (hK : 0 < K) (hE : 0 < E) (hκ : 0 < κ) (hc : κ * E < c)
    (A : ℝ) (hA : 0 ≤ A) :
    ∀ᶠ N : ℕ in atTop, ∃ w q : ℕ, 0 < q ∧
      (∀ δ : ℝ, Real.log (N : ℝ)^(-κ) ≤ δ → K * δ^(-E) ≤ (w : ℝ)) ∧
      (w : ℝ) ≤ Real.log (N : ℝ)^c ∧ initialModulus w ∣ q ∧ ModulusSmooth w q ∧
      Real.log (q : ℝ) ≤ (w : ℝ)^2 ∧ Real.log (N : ℝ)^A < (q : ℝ) := by
  let p := κ * E
  have hp : 0 < p := mul_pos hκ hE
  have hNlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpTop := (tendsto_rpow_atTop hp).comp hNlog
  have hcpTop := (tendsto_rpow_atTop (sub_pos.mpr hc)).comp hNlog
  filter_upwards [hNlog.eventually (eventually_ge_atTop (1 : ℝ)),
    hpTop.eventually (eventually_ge_atTop (2 / K)),
    hpTop.eventually (eventually_ge_atTop (2 * A / (p * K^2))),
    hcpTop.eventually (eventually_ge_atTop (K+1))] with N ht hW₂ hWA hTop
  let t := Real.log (N : ℝ)
  let w := ⌈K * t^p⌉₊
  have htpos : 0 < t := zero_lt_one.trans_le ht
  have htp : 0 < t^p := Real.rpow_pos_of_pos htpos p
  have hwLow : K * t^p ≤ (w : ℝ) := Nat.le_ceil _
  have hw₂ : 2 ≤ w := by
    have hh := ((div_le_iff₀ hK).mp hW₂).trans (by simpa only [mul_comm] using hwLow)
    exact_mod_cast hh
  have hwUp : (w : ℝ) ≤ t^c := by
    calc
      _ ≤ K * t^p + 1 := (Nat.ceil_lt_add_one (mul_nonneg hK.le htp.le)).le
      _ ≤ (K + 1) * t^p := by rw [add_mul, one_mul]; linarith [Real.one_le_rpow ht hp.le]
      _ ≤ t^(c-p) * t^p := mul_le_mul_of_nonneg_right hTop htp.le
      _ = _ := by rw [← Real.rpow_add htpos, sub_add_cancel]
  obtain ⟨q, hq, hdiv, hsmooth, hlow, hcap⟩ := exists_modulus_near_budget hw₂
  refine ⟨w, q, hq, ?_, hwUp, hdiv, hsmooth, hcap, ?_⟩
  · intro δ hδ
    have hδPow := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos htpos (-κ)) hδ
      (neg_nonpos.mpr hE.le)
    rw [← Real.rpow_mul htpos.le, neg_mul_neg] at hδPow
    exact (mul_le_mul_of_nonneg_left hδPow hK.le).trans hwLow
  · have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
    apply (Real.log_lt_log_iff (Real.rpow_pos_of_pos htpos A) hqpos).mp
    rw [Real.log_rpow htpos]
    have hlog : Real.log t ≤ t^p / p := by
      apply (le_div_iff₀ hp).mpr
      have h := Real.log_le_sub_one_of_pos htp
      rw [Real.log_rpow htpos] at h
      linarith
    have hcoeff := (div_le_iff₀ (mul_pos hp (sq_pos_of_pos hK))).mp hWA
    change 2 * A ≤ t^p * (p * K^2) at hcoeff
    have hsq := pow_le_pow_left₀ (mul_nonneg hK.le htp.le) hwLow 2
    calc
      A * Real.log t ≤ A * (t^p / p) := mul_le_mul_of_nonneg_left hlog hA
      _ ≤ (K * t^p)^2 / 2 := by
        apply le_of_mul_le_mul_right _ hp
        rw [show A * (t^p / p) * p = A * t^p by field_simp]
        nlinarith only [mul_le_mul_of_nonneg_right hcoeff htp.le]
      _ ≤ (w : ℝ)^2 / 2 := div_le_div_of_nonneg_right hsq (by norm_num)
      _ < _ := hlow

end NilBohr
