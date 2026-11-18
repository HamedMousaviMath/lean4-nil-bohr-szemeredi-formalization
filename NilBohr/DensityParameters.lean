import NilBohr.Density

open Filter
open scoped Topology

namespace NilBohr

theorem initialModulus_pos (w : ℕ) : 0 < initialModulus w := by
  apply Nat.pos_of_ne_zero
  unfold initialModulus
  rw [ne_eq, Finset.lcm_eq_zero_iff]
  rintro ⟨v, hv, rfl⟩
  have := (Finset.mem_Icc.mp hv).1
  omega

theorem initialModulus_dvd_factorial (w : ℕ) : initialModulus w ∣ w.factorial :=
  Finset.lcm_dvd (fun _ hn => Nat.dvd_factorial (Finset.mem_Icc.mp hn).1
    (Finset.mem_Icc.mp hn).2)

theorem initialModulus_smooth (w : ℕ) : ModulusSmooth w (initialModulus w) :=
  fun _ hp h => hp.dvd_factorial.mp (h.trans (initialModulus_dvd_factorial w))

theorem log_initialModulus_le (w : ℕ) :
    Real.log (initialModulus w : ℝ) ≤ (w : ℝ) * Real.log w := by
  have hqpos : 0 < initialModulus w := initialModulus_pos w
  have hqle : initialModulus w ≤ w^w :=
    (Nat.le_of_dvd (Nat.factorial_pos _) (initialModulus_dvd_factorial w)).trans
      (Nat.factorial_le_pow w)
  have hlog := Real.log_le_log (show (0 : ℝ) < initialModulus w by exact_mod_cast hqpos)
    (show (initialModulus w : ℝ) ≤ (w : ℝ)^w by exact_mod_cast hqle)
  simpa only [Real.log_pow] using hlog

private theorem eventually_scaled_power_le (C p q : ℝ) (hpq : p < q) :
    ∀ᶠ t : ℝ in atTop, C * t ^ p ≤ t ^ q := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (tendsto_rpow_atTop (sub_pos.mpr hpq)).eventually_ge_atTop C] with t ht hC
  have ht₀ : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have heq : p + (q - p) = q := by ring
  have hmul := mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg ht₀.le p)
  simpa only [← Real.rpow_add ht₀, add_comm (q - p) p, heq] using hmul

private theorem log_le_two_sqrt {w : ℝ} (hw : 0 < w) :
    Real.log w ≤ 2 * Real.sqrt w := by
  have hs := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hw)
  rw [Real.sqrt_eq_rpow, Real.log_rpow hw, ← Real.sqrt_eq_rpow] at hs
  linarith

private theorem log_modulus_budget {w : ℕ} {δ η b D : ℝ}
    (hw : 0 < w) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hη : 0 < η) (hb : 1 ≤ b)
    (hD : D = Real.log b / Real.log (1 + η)) (hlower : 4 * b^2 * δ ^ (-(2 * D)) ≤ (w : ℝ))
    {i : ℕ} (hi : i ≤ densityIterationSteps η δ) :
    b^i * Real.log (initialModulus w : ℝ) ≤ (w : ℝ)^2 := by
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  have hqR : (1 : ℝ) ≤ initialModulus w := by exact_mod_cast initialModulus_pos w
  have hpow := modulus_growth_to_density_power hη hδ hδ₁ hb hi
  rw [← hD] at hpow
  let z := 2 * b * δ ^ (-D)
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hsq : z^2 ≤ (w : ℝ) := by
    convert hlower using 1
    have heq : -(2 * D) = -D + -D := by ring
    rw [heq, Real.rpow_add hδ]
    dsimp [z]
    ring
  have hsqrt := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq hz] at hsqrt
  have hWlog := log_initialModulus_le w
  have hWsqrt := mul_le_mul_of_nonneg_left (log_le_two_sqrt hwR) hwR.le
  calc
    _ ≤ (b * δ ^ (-D)) * Real.log (initialModulus w : ℝ) :=
      mul_le_mul_of_nonneg_right hpow (Real.log_nonneg hqR)
    _ ≤ (b * δ ^ (-D)) * ((w : ℝ) * Real.log w) := by
      exact mul_le_mul_of_nonneg_left hWlog (by positivity)
    _ ≤ (b * δ ^ (-D)) * ((w : ℝ) * (2 * Real.sqrt w)) := by
      exact mul_le_mul_of_nonneg_left hWsqrt (by positivity)
    _ = z * ((w : ℝ) * Real.sqrt w) := by dsimp [z]; ring
    _ ≤ Real.sqrt w * ((w : ℝ) * Real.sqrt w) := by
      exact mul_le_mul_of_nonneg_right hsqrt (by positivity)
    _ = (w : ℝ)^2 := by nlinarith [Real.sq_sqrt hwR.le]

private theorem initial_logLength_budget {N q M : ℕ} (hN : 0 < N) (hq : 0 < q)
    {t : ℝ} (ht : t = Real.log N) (hlarge : 4 * Real.log 2 ≤ t)
    (hsmallq : Real.log q ≤ t / 4) (hM : (N : ℝ) / q - 1 < (M : ℝ)) :
    t / 2 ≤ Real.log M := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hquot : 0 < (N : ℝ) / q := div_pos hN' hq'
  have hcompare : 2 * Real.exp (t / 2) ≤ (N : ℝ) / q := by
    apply (Real.log_le_log_iff (mul_pos zero_lt_two (Real.exp_pos _)) hquot).mp
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.exp_pos _).ne', Real.log_exp,
      Real.log_div hN'.ne' hq'.ne', ← ht]
    linarith
  have hExp : 1 ≤ Real.exp (t / 2) := Real.one_le_exp (by linarith [Real.log_pos (show 1 < (2 : ℝ) by norm_num)])
  have hlog := Real.log_le_log (Real.exp_pos (t / 2))
    (show Real.exp (t / 2) ≤ (M : ℝ) by linarith)
  simpa only [Real.log_exp] using hlog

private theorem floor_parameterScale_of_logs {n q d : ℕ} (hn : 0 < n) (hq : 0 < q)
    (hd : 0 < d)
    (h : (d : ℝ) * Real.log 2 + ((d - 1 : ℕ) : ℝ) * Real.log q ≤ Real.log n) :
    2 ≤ ((n : ℝ) / (q : ℝ) ^ (d - 1)) ^ ((d : ℝ)⁻¹) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hb := div_pos hn' (pow_pos hq' (d - 1))
  have hr := Real.rpow_pos_of_pos hb ((d : ℝ)⁻¹)
  apply (Real.log_le_log_iff zero_lt_two hr).mp
  rw [Real.log_rpow hb, Real.log_div hn'.ne' (pow_pos hq' _).ne', Real.log_pow,
    ← div_eq_inv_mul]
  apply (le_div_iff₀ hd').mpr
  linarith


/-- The full density iteration leading to Theorem 1.2, conditional on
the manuscript's density increment. This discharges the asymptotic resource
conditions of `recurrence_of_density_increment_at_scale`. -/
theorem recurrenceConclusion_of_density_increment {ℓ d r : ℕ}
    (P : Fin (ℓ + 1) → Polynomial ℤ) (hP : ∀ i, (P i).coeff 0 = 0)
    (selector : ℕ → Prop) (hr : 0 < r) (hrd : r ≤ d)
    (c : DensityIncrementConstants)
    (increment : DensityIncrementAtParameters P selector d r c) :
    RecurrenceConclusion P selector := by
  have hd : 0 < d := hr.trans_le hrd
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  let a := (r : ℝ) / d
  let b := (c.Bmax : ℝ) + 1
  have ha : 0 < a := div_pos (by exact_mod_cast hr) hd'
  have ha₁ : a ≤ 1 :=
    (div_le_iff₀ hd').mpr (by simpa using (show (r : ℝ) ≤ (d : ℝ) by exact_mod_cast hrd))
  have hb : 1 ≤ b := le_add_of_nonneg_left (Nat.cast_nonneg c.Bmax)
  let ℓη := Real.log (1 + c.η)
  have hℓη : 0 < ℓη := Real.log_pos (by linarith [c.η_pos])
  let D₀ := Real.log b / ℓη
  let D₁ := -(Real.log a / ℓη)
  have hD₀ : 0 ≤ D₀ := div_nonneg (Real.log_nonneg hb) hℓη.le
  have hD₁ : 0 ≤ D₁ := neg_nonneg.mpr (div_nonpos_of_nonpos_of_nonneg
    (Real.log_nonpos ha.le ha₁) hℓη.le)
  let K := max (4 * b^2) (max c.K 1)
  let E := max (2 * D₀) (max c.E 1)
  let U := max E D₁
  have hK₁ : 1 ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  have hKpos : 0 < K := zero_lt_one.trans_le hK₁
  have hKc : c.K ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hKb : 4 * b^2 ≤ K := le_max_left _ _
  have hE₁ : 1 ≤ E := (le_max_right _ _).trans (le_max_right _ _)
  have hEc : c.E ≤ E := (le_max_left _ _).trans (le_max_right _ _)
  have hED : 2 * D₀ ≤ E := le_max_left _ _
  have hEpos : 0 < E := zero_lt_one.trans_le hE₁
  have hUpos : 0 < U := hEpos.trans_le (le_max_left _ _)
  let s := min (1 / 16 : ℝ) (c.c / 4)
  have hs : 0 < s := lt_min (by norm_num) (by linarith [c.c_pos])
  have hs₁ : s ≤ 1 / 16 := min_le_left _ _
  have hs₂ : s ≤ c.c / 4 := min_le_right _ _
  let κ := s / U
  have hκ : 0 < κ := div_pos hs hUpos
  have hκE : κ * E ≤ s := by
    calc
      κ * E ≤ κ * U := mul_le_mul_of_nonneg_left (le_max_left _ _) hκ.le
      _ = s := div_mul_cancel₀ _ hUpos.ne'
  have hκD : κ * D₁ ≤ s := by
    calc
      κ * D₁ ≤ κ * U := mul_le_mul_of_nonneg_left (le_max_right _ _) hκ.le
      _ = s := div_mul_cancel₀ _ hUpos.ne'
  have hκ₁ : κ ≤ s :=
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hE₁ hκ.le : κ ≤ κ * E).trans hκE
  let W := a * ((d - 1 : ℕ) : ℝ) + c.C₁
  let R := W + c.C₁ + |Real.log c.lengthConstant| + (r : ℝ) * Real.log 2
  let S := (1 / ℓη) + 1
  let T := (d : ℝ) * Real.log 2 + ((d - 1 : ℕ) : ℝ)
  have hW : 0 ≤ W := add_nonneg (mul_nonneg ha.le (Nat.cast_nonneg _)) c.C₁_pos.le
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hT : ∀ᶠ t : ℝ in atTop,
      1 ≤ t ∧ 4 * Real.log 2 ≤ t ∧
      (K + 1) * t^s ≤ t^(2*s) ∧
      R * t^(4*s) ≤ t^(5*s) ∧ S * t^s ≤ t^(2*s) ∧
      4 * t^(4*s) ≤ t ∧ T * t^(4*s) ≤ t^(3/4 : ℝ) ∧
      2 * t^(3/4 : ℝ) ≤ (a/2) * t^(1-s) ∧
      Real.log (c.Nmin + 1 : ℕ) ≤ t^(3/4 : ℝ) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (4 * Real.log 2),
      eventually_scaled_power_le (K + 1) s (2*s) (by linarith),
      eventually_scaled_power_le R (4*s) (5*s) (by linarith),
      eventually_scaled_power_le S s (2*s) (by linarith),
      eventually_scaled_power_le 4 (4*s) 1 (by linarith),
      eventually_scaled_power_le T (4*s) (3/4) (by linarith),
      eventually_scaled_power_le (4/a) (3/4) (1-s) (by linarith),
      eventually_scaled_power_le (Real.log (c.Nmin + 1 : ℕ)) 0 (3/4) (by norm_num)]
      with t ht ht₂ hw hR hS hsmall hscale hdom hlarge
    have hh := mul_le_mul_of_nonneg_left hdom (show 0 ≤ a / 2 by positivity)
    have hh' : (a / 2) * (4 / a * t^(3/4 : ℝ)) = 2 * t^(3/4 : ℝ) := by
      field_simp
      ring
    rw [hh'] at hh
    exact ⟨ht, ht₂, hw, hR, hS, by simpa only [Real.rpow_one] using hsmall, hscale, hh,
      by simpa only [Real.rpow_zero, mul_one] using hlarge⟩
  have hloglimit : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hNevent := (eventually_ge_atTop (1 : ℕ)).and (hloglimit.eventually hT)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hNevent
  refine ⟨κ, hκ, N₀, ?_⟩
  intro N hNN A hA hdensity
  obtain ⟨hN, ht, ht₂, htW, htR, htS, htSmall, htScale, htDom, htNmin⟩ := hN₀ N hNN
  let t := Real.log (N : ℝ)
  let δ := setDensity A N
  have hNpos : 0 < N := hN
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hδmin : t ^ (-κ) ≤ δ := by
    apply (le_div_iff₀ hNreal).mpr
    simpa [t, mul_comm] using hdensity
  have htpos : 0 < t := zero_lt_one.trans_le ht
  have hδ : 0 < δ := (Real.rpow_pos_of_pos htpos _).trans_le hδmin
  have hδ₁ : δ ≤ 1 := setDensity_le_one hNpos hA
  have hnegpow (F : ℝ) (hF : 0 ≤ F) (hκF : κ * F ≤ s) :
      δ ^ (-F) ≤ t ^ s := by
    have hmon := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos htpos (-κ)) hδmin
      (neg_nonpos.mpr hF)
    rw [← Real.rpow_mul htpos.le, neg_mul_neg] at hmon
    exact hmon.trans (Real.rpow_le_rpow_of_exponent_le ht hκF)
  have hδposP : t ^ (-s) ≤ δ ^ D₁ := calc
    _ ≤ t ^ (-κ * D₁) := Real.rpow_le_rpow_of_exponent_le ht (by linarith [hκD])
    _ = (t ^ (-κ)) ^ D₁ := Real.rpow_mul htpos.le _ _
    _ ≤ δ ^ D₁ := Real.rpow_le_rpow (Real.rpow_nonneg htpos.le _) hδmin hD₁
  let w := ⌈K * δ^(-E)⌉₊
  have hceil : K * δ^(-E) ≤ (w : ℝ) := Nat.le_ceil _
  have hw₀ : 0 < w := by
    have hwp := (mul_pos hKpos (Real.rpow_pos_of_pos hδ (-E))).trans_le hceil
    exact_mod_cast hwp
  have hKδ : c.K * δ^(-c.E) ≤ (w : ℝ) :=
    (mul_le_mul hKc (Real.rpow_le_rpow_of_exponent_ge hδ hδ₁ (neg_le_neg hEc))
      (Real.rpow_nonneg hδ.le _) hKpos.le).trans hceil
  have hBδ : 4 * b^2 * δ ^ (-(2 * D₀)) ≤ (w : ℝ) :=
    (mul_le_mul hKb (Real.rpow_le_rpow_of_exponent_ge hδ hδ₁ (neg_le_neg hED))
      (Real.rpow_nonneg hδ.le _) hKpos.le).trans hceil
  have hwU : (w : ℝ) ≤ t ^ (2*s) := by
    have hupper : (w : ℝ) < K * δ ^ (-E) + 1 :=
      Nat.ceil_lt_add_one (mul_nonneg hKpos.le (Real.rpow_nonneg hδ.le _))
    have hh := mul_le_mul_of_nonneg_left (hnegpow E hEpos.le hκE) hKpos.le
    apply le_trans _ htW
    rw [add_mul, one_mul]
    linarith [Real.one_le_rpow ht hs.le]
  have hwsq : (w : ℝ)^2 ≤ t^(4*s) := by
    have hpow := pow_le_pow_left₀ (Nat.cast_nonneg w : (0 : ℝ) ≤ (w : ℝ)) hwU 2
    rw [← Real.rpow_natCast (t^(2*s)), ← Real.rpow_mul htpos.le] at hpow
    norm_num at hpow
    convert hpow using 2
    ring
  let q₀ := initialModulus w
  have hq₀ : 0 < q₀ := initialModulus_pos w
  let J := densityIterationSteps c.η δ
  have hmod (i : ℕ) (hi : i ≤ J) : b ^ i * Real.log (q₀ : ℝ) ≤ (w : ℝ)^2 :=
    log_modulus_budget hw₀ hδ hδ₁ c.η_pos hb rfl hBδ hi
  have hstartq : Real.log (q₀ : ℝ) ≤ t / 4 := by
    have hh : Real.log (q₀ : ℝ) ≤ (w : ℝ)^2 := by
      simpa only [pow_zero, one_mul] using hmod 0 (Nat.zero_le J)
    linarith [hh.trans hwsq]
  have hlogδpos : 0 ≤ Real.log δ⁻¹ := Real.log_nonneg ((one_le_inv₀ hδ).mpr hδ₁)
  have hlogδ : Real.log δ⁻¹ ≤ t^s := by
    have h := hnegpow 1 (by norm_num) (by simpa using hκ₁)
    rw [Real.rpow_neg_one] at h
    linarith [Real.log_le_sub_one_of_pos (inv_pos.mpr hδ)]
  have hJ : (J : ℝ) ≤ t^(2*s) := by
    apply le_trans _ htS
    have h := densityIterationSteps_le c.η_pos hδ hδ₁
    change (J : ℝ) ≤ Real.log δ⁻¹ / ℓη + 1 at h
    have hh := div_le_div_of_nonneg_right hlogδ hℓη.le
    dsimp only [S]
    rw [add_mul, one_mul, one_div, inv_mul_eq_div]
    linarith [Real.one_le_rpow ht hs.le]
  let loss := W * (w : ℝ)^2 + c.C₁ * Real.log δ⁻¹ + |Real.log c.lengthConstant| +
    (r : ℝ) * Real.log 2
  have hloss : 0 ≤ loss :=
    add_nonneg (add_nonneg (add_nonneg (mul_nonneg hW (sq_nonneg _))
      (mul_nonneg c.C₁_pos.le hlogδpos)) (abs_nonneg _))
      (mul_nonneg (Nat.cast_nonneg _) hlog2)
  have hlossUpper : loss ≤ t^(5*s) := by
    apply le_trans _ htR
    have hpow₁ : 1 ≤ t^(4*s) := Real.one_le_rpow ht (by linarith)
    have hpows : t^s ≤ t^(4*s) := Real.rpow_le_rpow_of_exponent_le ht (by linarith)
    have hfirst := mul_le_mul_of_nonneg_left hwsq hW
    have hsecond := mul_le_mul_of_nonneg_left (hlogδ.trans hpows) c.C₁_pos.le
    have hthird := le_mul_of_one_le_right (abs_nonneg (Real.log c.lengthConstant)) hpow₁
    have hfourth := le_mul_of_one_le_right (mul_nonneg (Nat.cast_nonneg r) hlog2) hpow₁
    calc
      loss ≤ W * t^(4*s) + c.C₁ * t^(4*s) + |Real.log c.lengthConstant| * t^(4*s) +
          ((r : ℝ) * Real.log 2) * t^(4*s) :=
        add_le_add (add_le_add (add_le_add hfirst hsecond) hthird) hfourth
      _ = R * t^(4*s) := by unfold R; ring
  have hlossBound : W * (w : ℝ)^2 -
      c.C₁ * Real.log δ - Real.log c.lengthConstant + (r : ℝ) * Real.log 2 ≤ loss := by
    dsimp only [loss]
    rw [Real.log_inv]
    linarith [neg_abs_le (Real.log c.lengthConstant)]
  apply recurrence_of_density_increment_at_scale P hP selector c increment A hNpos hA
    hq₀ (dvd_refl q₀) (initialModulus_smooth w) hrd hδ hKδ loss (t/2) hloss
    (fun L hL => initial_logLength_budget hNpos hq₀ rfl ht₂ hstartq hL) hlossBound
  intro i n q hi hn hq hqBound hnBound
  have hi' : i ≤ J := hi.le
  have hqT : Real.log q ≤ (w : ℝ)^2 := hqBound.trans (hmod i hi')
  have hAδ : a * δ ^ D₁ ≤ a ^ i := length_contraction_to_density_power
    c.η_pos hδ hδ₁ ha ha₁ hi'
  have hmain : (a / 2) * t^(1-s) ≤ a^i * (t/2) := by
    have hval := (mul_le_mul_of_nonneg_left hδposP ha.le).trans hAδ
    have hh := mul_le_mul_of_nonneg_right hval (show 0 ≤ t / 2 by positivity)
    calc
      _ = (a * t^(-s)) * (t/2) := by
        have he : 1 - s = -s + 1 := by ring
        rw [he, Real.rpow_add htpos, Real.rpow_one]
        ring
      _ ≤ _ := hh
  have herr : (i : ℝ) * loss ≤ t^(3/4 : ℝ) := by
    have hic : (i : ℝ) ≤ t^(2*s) :=
      (show (i : ℝ) ≤ (J : ℝ) by exact_mod_cast hi').trans hJ
    have hmul := mul_le_mul hic hlossUpper hloss (Real.rpow_nonneg htpos.le _)
    rw [← Real.rpow_add htpos] at hmul
    exact hmul.trans (Real.rpow_le_rpow_of_exponent_le ht (by linarith))
  have hnT : t^(3/4 : ℝ) ≤ Real.log n := by
    change a^i * (t/2) - (i : ℝ) * loss ≤ Real.log n at hnBound
    linarith [htDom.trans hmain, herr]
  have hnN : c.Nmin ≤ n := by
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hv : (0 : ℝ) < ((c.Nmin + 1 : ℕ) : ℝ) := by positivity
    have hh := (Real.log_le_log_iff hv hn').mp (htNmin.trans hnT)
    have hh' : c.Nmin + 1 ≤ n := by exact_mod_cast hh
    omega
  have hnW : (w : ℝ) ≤ Real.log n ^ c.c := by
    calc
      _ ≤ t^(2*s) := hwU
      _ ≤ t^((3/4 : ℝ)*c.c) := Real.rpow_le_rpow_of_exponent_le ht (by linarith [c.c_pos])
      _ = (t^(3/4 : ℝ)) ^ c.c := Real.rpow_mul htpos.le _ _
      _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg htpos.le _) hnT c.c_pos.le
  have hScale : (d : ℝ) * Real.log 2 + ((d - 1 : ℕ) : ℝ) * Real.log q ≤ Real.log n := by
    have hq' := mul_le_mul_of_nonneg_left (hqT.trans hwsq)
      (Nat.cast_nonneg (d - 1) : (0 : ℝ) ≤ ((d - 1 : ℕ) : ℝ))
    have hs' := le_mul_of_one_le_right (mul_nonneg hd'.le hlog2)
      (Real.one_le_rpow ht (show 0 ≤ 4*s by positivity))
    dsimp only [T] at htScale
    rw [add_mul] at htScale
    linarith [htScale.trans hnT]
  exact ⟨hnN, hnW, hqT, floor_parameterScale_of_logs hn hq hd hScale⟩


/-- The asymptotic recurrence statement with the manuscript's actual
smallest and largest polynomial degrees. -/
theorem recurrenceConclusion_of_densityIncrementFor {ℓ : ℕ}
    (P : Fin (ℓ + 1) → Polynomial ℤ) (hP : FixedPolynomialFamily P)
    (selector : ℕ → Prop) (hinc : DensityIncrementFor P selector) :
    RecurrenceConclusion P selector := by
  rcases hP with ⟨hℓ, hPzero, hP₀, hPdegree⟩
  have hfin : (0 : Fin (ℓ + 1)) < 1 := by
    change 0 < 1 % (ℓ + 1)
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hr : 0 < (P 1).natDegree := by simpa [hPzero] using hPdegree hfin
  have hrd : (P 1).natDegree ≤ (P (Fin.last ℓ)).natDegree :=
    hPdegree.monotone (Fin.le_last _)
  obtain ⟨c, hc⟩ := hinc
  exact recurrenceConclusion_of_density_increment P hP₀ selector hr hrd c hc

/-- Theorem 1.2 follows from its unresolved density increment. This theorem
formalizes the downstream implication without treating that increment as an
external theorem. -/
theorem heisenbergRecurrence_of_density_increment
    (hinc : ∀ {ℓ : ℕ} (P : Fin (ℓ + 1) → Polynomial ℤ), FixedPolynomialFamily P →
      ∀ (α β : ℝ), BadlyApproximable α → AdmissibleBeta β → ∀ J : OpenArc,
        DensityIncrementFor P (fun p => J.Contains (heisenbergPhase α β ((p : ℤ) - 1)))) :
    HeisenbergRecurrence := by
  intro ℓ P hP α β hα hβ J
  exact recurrenceConclusion_of_densityIncrementFor P hP _ (hinc P hP α β hα hβ J)

end NilBohr
