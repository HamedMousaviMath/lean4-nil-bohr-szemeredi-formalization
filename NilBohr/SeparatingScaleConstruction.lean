import NilBohr.DensityIncrementProof
import NilBohr.SeparatingScales
import NilBohr.AdmissibleDenominators

/-! The explicit separating scales of Appendix A. -/

open Filter
open scoped Topology

namespace NilBohr

noncomputable def separatingW (r : ℕ) : ℕ :=
  ⌊Real.log (r : ℝ)⌋₊

noncomputable def separatingExponent (r : ℕ) : ℕ :=
  ⌊(separatingW r : ℝ)^2 / Real.log (initialModulus (separatingW r) : ℝ)⌋₊

noncomputable def separatingModulus (r : ℕ) : ℕ :=
  initialModulus (separatingW r) ^ separatingExponent r

noncomputable def separatingLengthQuotient (r R : ℕ) : ℕ :=
  ⌊(R : ℝ)^(1/4 : ℝ) / (r : ℝ)⌋₊

noncomputable def separatingLength (r R : ℕ) : ℕ :=
  r * separatingLengthQuotient r R

noncomputable def separatingScaleX (r R : ℕ) : ℕ :=
  separatingModulus r * separatingLength r R

noncomputable def separatingSpatialScale (r R : ℕ) : ℕ :=
  separatingModulus r * (separatingLength r R)^2

structure SeparatingScale (r R : ℕ) : Prop where
  w_large : 16 ≤ separatingW r
  q_pos : 0 < separatingModulus r
  H_pos : 0 < separatingLengthQuotient r R
  M_pos : 0 < separatingLength r R
  H_lower : (R : ℝ)^(1/6 : ℝ) ≤ (separatingLengthQuotient r R : ℝ)
  M_lower : (R : ℝ)^(1/5 : ℝ) ≤ (separatingLength r R : ℝ)
  M_upper : (separatingLength r R : ℝ) ≤ (R : ℝ)^(1/4 : ℝ)
  X_lower : (R : ℝ)^(1/5 : ℝ) ≤ (separatingScaleX r R : ℝ)
  X_upper : (separatingScaleX r R : ℝ) ≤ (R : ℝ)^(1/3 : ℝ)
  log_q_lower : (Real.log (r : ℝ))^2 / 8 ≤ Real.log (separatingModulus r : ℝ)
  log_q_upper : Real.log (separatingModulus r : ℝ) ≤ (separatingW r : ℝ)^2
  q_divisible : 8 * (∏ p ∈ primesThrough (separatingW r), p) ∣ separatingModulus r
  q_smooth : Smooth (separatingModulus r) (separatingW r)
  coprime : (separatingModulus r).Coprime r
  bracket_left : (r : ℝ) ≤ (separatingScaleX r R : ℝ)^(1/100 : ℝ)
  bracket_right : (separatingScaleX r R : ℝ)^(1/100 : ℝ) < (R : ℝ)
  q_le_M : separatingModulus r ≤ separatingLength r R

/-- A fixed power of the logarithm of the current denominator is eventually
dominated by the logarithm of the next denominator, with any fixed factor. -/
theorem eventually_separatingLogPower {β : ℝ} {r : ℕ → ℕ}
    (hr : AdmissibleBetaDenominators β r) (p K : ℝ) (hK : 0 < K) :
    ∀ᶠ j : ℕ in atTop, K * (Real.log (r j : ℝ))^p ≤ Real.log (r (j+1) : ℝ) := by
  obtain ⟨hMono, a, _, hPrime, c, C, D, hc, hC, hD, hBounds⟩ := hr
  let t := fun j : ℕ => Real.log (r j : ℝ)
  have ht : Tendsto t atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hMono.tendsto_atTop)
  let s := fun j : ℕ => Real.sqrt (t j)
  have hs : Tendsto s atTop atTop := by
    simpa only [s, Real.sqrt_eq_rpow, Function.comp_apply] using
      (tendsto_rpow_atTop (show 0 < (1/2 : ℝ) by norm_num)).comp ht
  have hExp : Tendsto (fun j => Real.exp (s j)) atTop atTop := Real.tendsto_exp_atTop.comp hs
  have hPower := hs.eventually ((isLittleO_rpow_exp_atTop (2*p)).bound
    (show 0 < (2*K)⁻¹ by positivity))
  filter_upwards [ht.eventually_ge_atTop 1, hPower,
    hExp.eventually_ge_atTop (2*|Real.log c|)] with j ht₁ hp he
  have ht₀ : 0 ≤ t j := zero_le_one.trans ht₁
  have hsq : (s j)^2 = t j := Real.sq_sqrt ht₀
  have hpow : (s j)^(2*p) = (t j)^p := by
    rw [Real.rpow_mul (Real.sqrt_nonneg _), Real.rpow_two, hsq]
  change ‖(s j)^(2*p)‖ ≤ (2*K)⁻¹ * ‖Real.exp (s j)‖ at hp
  rw [hpow, Real.norm_of_nonneg (Real.rpow_nonneg ht₀ _),
    Real.norm_of_nonneg (Real.exp_pos _).le] at hp
  have hhalf : (2*K) * (t j)^p ≤ Real.exp (s j) := by
    exact (le_inv_mul_iff₀ (by positivity : 0 < 2*K)).mp hp
  have hlog := Real.log_le_log (mul_pos hc (Real.exp_pos _)) (hBounds j).1
  change Real.log (c*Real.exp (Real.exp (s j))) ≤ Real.log (r (j+1) : ℝ) at hlog
  rw [Real.log_mul hc.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
  change K * (t j)^p ≤ Real.log (r (j+1) : ℝ)
  linarith only [hhalf, he, hlog, neg_le_abs (Real.log c)]

private theorem separatingModulus_bounds {r : ℕ} (hw : 16 ≤ separatingW r) :
    0 < separatingModulus r ∧
    (Real.log (r : ℝ))^2 / 8 ≤ Real.log (separatingModulus r : ℝ) ∧
    Real.log (separatingModulus r : ℝ) ≤ (separatingW r : ℝ)^2 ∧
    8 * (∏ p ∈ primesThrough (separatingW r), p) ∣ separatingModulus r ∧
    Smooth (separatingModulus r) (separatingW r) := by
  let w := separatingW r
  let L := initialModulus w
  let e := separatingExponent r
  let q := separatingModulus r
  let t := Real.log (r : ℝ)
  have hL₀ : 0 < L := initialModulus_pos w
  have h16 : 16 ∣ L := by
    unfold L initialModulus
    exact Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr ⟨by decide, hw⟩)
  have hL₁ : (1 : ℝ) < L := by
    have h := Nat.le_of_dvd hL₀ h16
    exact_mod_cast (show 1 < L by omega)
  have hlogL := Real.log_pos hL₁
  have hwR : (16 : ℝ) ≤ w := by exact_mod_cast hw
  have hw₀ : (0 : ℝ) < w := by linarith
  have hfw : (w : ℝ) ≤ t := by
    change (⌊t⌋₊ : ℝ) ≤ t
    apply Nat.floor_le
    have h := Nat.lt_floor_add_one t
    by_contra! hn
    have : ⌊t⌋₊ = 0 := Nat.floor_of_nonpos hn.le
    change 16 ≤ ⌊t⌋₊ at hw
    omega
  have hfwt : t < (w : ℝ)+1 := Nat.lt_floor_add_one t
  have hlogw : Real.log (w : ℝ) ≤ (w : ℝ)/2 := by
    have hs := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hw₀)
    rw [Real.sqrt_eq_rpow, Real.log_rpow hw₀, ← Real.sqrt_eq_rpow] at hs
    have hs₄ : 4 ≤ Real.sqrt (w : ℝ) := (Real.le_sqrt (by norm_num) hw₀.le).mpr (by nlinarith)
    nlinarith only [hs, Real.sq_sqrt hw₀.le,
      mul_nonneg (Real.sqrt_nonneg (w : ℝ)) (sub_nonneg.mpr hs₄)]
  have hbudget : Real.log (L : ℝ) ≤ (w : ℝ)^2 / 2 := by
    have h := mul_le_mul_of_nonneg_left hlogw hw₀.le
    nlinarith only [log_initialModulus_le w, h]
  have heq : (q : ℝ) = (L : ℝ)^e := by simp [q, separatingModulus, L, w, e]
  have hq₀ : 0 < q := pow_pos hL₀ _
  have hqlog : Real.log (q : ℝ) = (e : ℝ) * Real.log (L : ℝ) := by rw [heq, Real.log_pow]
  have hfloor : (e : ℝ) ≤ (w : ℝ)^2/Real.log (L : ℝ) := Nat.floor_le (by positivity)
  have hupper := (le_div_iff₀ hlogL).mp hfloor
  have hfloor' : (w : ℝ)^2/Real.log (L : ℝ) < (e : ℝ)+1 := Nat.lt_floor_add_one _
  have hlower := (div_lt_iff₀ hlogL).mp hfloor'
  have ht_half : t / 2 ≤ (w : ℝ) := by linarith
  have hlog_lower : t^2/8 ≤ Real.log (q : ℝ) := by
    have hs := pow_le_pow_left₀ (by linarith : 0 ≤ t/2) ht_half 2
    rw [hqlog]
    nlinarith only [hs, hlower, hbudget]
  have he_pos : 0 < e := by
    by_contra! hbad
    have he_zero : e = 0 := by omega
    have ht : 0 < t := hw₀.trans_le hfw
    have hp : 0 < Real.log (q : ℝ) := (div_pos (pow_pos ht 2) (by norm_num)).trans_le hlog_lower
    rw [hqlog, he_zero] at hp
    simp at hp
  refine ⟨hq₀, hlog_lower, hqlog ▸ hupper, ?_, ?_⟩
  · exact (eight_mul_primeProduct_dvd_initialModulus hw).trans (dvd_pow_self _ he_pos.ne')
  · intro p hp hd
    exact initialModulus_smooth w p hp (hp.dvd_of_dvd_pow hd)

/-- Explicit (q,M) have all of the power and prime-step relations needed
for the three norm assertions in Proposition A.1. -/
theorem eventually_separatingScale {β : ℝ} {r : ℕ → ℕ}
    (hr : AdmissibleBetaDenominators β r) :
    ∀ᶠ j : ℕ in atTop, SeparatingScale (r j) (r (j+1)) := by
  have hGrowth := eventually_separatingLogPower hr 2 1000 (by norm_num)
  obtain ⟨hMono, a, _, hPrime, c, C, D, hc, hC, hD, hBounds⟩ := hr
  let t := fun j : ℕ => Real.log (r j : ℝ)
  have ht : Tendsto t atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hMono.tendsto_atTop)
  filter_upwards [ht.eventually_ge_atTop 16, hGrowth] with j ht₁ hbudget
  let b := r j
  let R := r (j+1)
  let u := Real.log (R : ℝ)
  let w := separatingW b
  let q := separatingModulus b
  let H := separatingLengthQuotient b R
  let M := separatingLength b R
  let X := separatingScaleX b R
  have hb : 0 < (b : ℝ) := by exact_mod_cast (hPrime j).1.pos
  have hR : 1 < (R : ℝ) := by exact_mod_cast (hPrime (j+1)).1.one_lt
  have hR₀ : 0 < (R : ℝ) := by linarith
  have hu : 0 < u := Real.log_pos hR
  change 1000 * (t j)^(2:ℝ) ≤ u at hbudget
  rw [Real.rpow_two] at hbudget
  have htt : t j ≤ (t j)^2 := by nlinarith only [mul_nonneg (show 0 ≤ t j by linarith) (show 0 ≤ t j - 1 by linarith)]
  have htu : t j ≤ u/1000 := by linarith
  have hU : 20 ≤ u := by nlinarith only [hbudget, htt, ht₁]
  have hw : 16 ≤ w := Nat.le_floor (by simpa using ht₁)
  obtain ⟨hq, hql, hquw, hqdiv, hqsm⟩ := separatingModulus_bounds hw
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hwub : (w : ℝ) ≤ t j := Nat.floor_le (by linarith)
  have hqu : Real.log (q : ℝ) ≤ u/1000 := by
    have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ w) hwub 2
    linarith
  let Z := (R : ℝ)^(1/4 : ℝ)/(b : ℝ)
  have hZ : 0 < Z := div_pos (Real.rpow_pos_of_pos hR₀ _) hb
  have hZlog : Real.log Z = u/4 - t j := by
    dsimp only [Z]
    rw [Real.log_div (Real.rpow_pos_of_pos hR₀ _).ne' hb.ne', Real.log_rpow hR₀]
    dsimp [u, t, b]
    ring
  have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (show 0 < (2:ℝ) by norm_num)]
  have hZ2 : 2 ≤ Z := (Real.log_le_log_iff zero_lt_two hZ).mp (by rw [hZlog]; linarith)
  have hHfloor : (H : ℝ) ≤ Z := Nat.floor_le hZ.le
  have hHfloor' : Z < (H : ℝ)+1 := Nat.lt_floor_add_one Z
  have hH_lb : Z/2 ≤ (H : ℝ) := by linarith
  have hH₀ : 0 < (H : ℝ) := (half_pos hZ).trans_le hH_lb
  have hH : 0 < H := by exact_mod_cast hH₀
  have hM : 0 < M := Nat.mul_pos (hPrime j).1.pos hH
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hM_eq : (M : ℝ) = (b : ℝ)*(H : ℝ) := by simp [M, separatingLength, b, H]
  have hbZ : (b : ℝ)*Z = (R : ℝ)^(1/4 : ℝ) := by
    dsimp only [Z]
    rw [mul_div_left_comm, div_self hb.ne', mul_one]
  have hMl : (R : ℝ)^(1/4 : ℝ)/2 ≤ (M : ℝ) := by
    rw [hM_eq]
    calc
      _ = (b : ℝ)*(Z/2) := by rw [← hbZ]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hH_lb hb.le
  have hMu : (M : ℝ) ≤ (R : ℝ)^(1/4 : ℝ) := by
    rw [hM_eq, ← hbZ]
    exact mul_le_mul_of_nonneg_left hHfloor hb.le
  have hMlog : u/5 ≤ Real.log (M : ℝ) := by
    have h := Real.log_le_log (half_pos (Real.rpow_pos_of_pos hR₀ _)) hMl
    rw [Real.log_div (Real.rpow_pos_of_pos hR₀ _).ne' (by norm_num : (2:ℝ) ≠ 0),
      Real.log_rpow hR₀] at h
    change (1/4 : ℝ) * u - Real.log 2 ≤ Real.log (M : ℝ) at h
    linarith
  have hMl' : (R : ℝ)^(1/5 : ℝ) ≤ (M : ℝ) := by
    apply (Real.log_le_log_iff (Real.rpow_pos_of_pos hR₀ _) hMR).mp
    rw [Real.log_rpow hR₀]
    change (1/5:ℝ)*u ≤ Real.log (M : ℝ)
    linarith
  have hHlog : u/6 ≤ Real.log (H : ℝ) := by
    have h := hMlog
    rw [hM_eq, Real.log_mul hb.ne' hH₀.ne'] at h
    change u/5 ≤ t j + Real.log (H : ℝ) at h
    linarith
  have hHl : (R : ℝ)^(1/6 : ℝ) ≤ (H : ℝ) := by
    apply (Real.log_le_log_iff (Real.rpow_pos_of_pos hR₀ _) hH₀).mp
    rw [Real.log_rpow hR₀]
    change (1/6:ℝ)*u ≤ Real.log (H : ℝ)
    linarith
  have hX_eq : (X : ℝ) = (q : ℝ)*(M : ℝ) := by simp [X, separatingScaleX, q, M]
  have hX₀ : (0 : ℝ) < X := by rw [hX_eq]; positivity
  have hq₁ : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hXl : (R : ℝ)^(1/5 : ℝ) ≤ (X : ℝ) := by
    rw [hX_eq]
    exact hMl'.trans (le_mul_of_one_le_left hMR.le hq₁)
  have hXu : (X : ℝ) ≤ (R : ℝ)^(1/3 : ℝ) := by
    have hh := Real.log_le_log hMR hMu
    rw [Real.log_rpow hR₀] at hh
    change Real.log (M : ℝ) ≤ (1/4:ℝ)*u at hh
    apply (Real.log_le_log_iff hX₀ (Real.rpow_pos_of_pos hR₀ _)).mp
    rw [hX_eq, Real.log_mul hqR.ne' hMR.ne', Real.log_rpow hR₀]
    change Real.log (q : ℝ) + Real.log (M : ℝ) ≤ (1/3 : ℝ)*u
    linarith
  have hXlog_lb : u/5 ≤ Real.log (X : ℝ) := by
    have hh := Real.log_le_log (Real.rpow_pos_of_pos hR₀ _) hXl
    rw [Real.log_rpow hR₀] at hh
    dsimp [u]
    linarith
  have hXlog_ub : Real.log (X : ℝ) ≤ u/3 := by
    have hh := Real.log_le_log hX₀ hXu
    rw [Real.log_rpow hR₀] at hh
    dsimp [u]
    linarith
  have hcop : q.Coprime b := by
    apply Nat.Coprime.symm
    refine (Nat.Prime.coprime_iff_not_dvd (hPrime j).1).mpr fun hd => ?_
    have h := hqsm b (hPrime j).1 hd
    have h' := Real.log_le_sub_one_of_pos hb
    have h'' : (b : ℝ) ≤ w := by exact_mod_cast h
    change t j ≤ (b : ℝ)-1 at h'
    linarith
  have hBl : (b : ℝ) ≤ (X : ℝ)^(1/100 : ℝ) := by
    apply (Real.log_le_log_iff hb (Real.rpow_pos_of_pos hX₀ _)).mp
    rw [Real.log_rpow hX₀]
    change t j ≤ (1/100:ℝ)*Real.log (X : ℝ)
    linarith
  have hBr : (X : ℝ)^(1/100 : ℝ) < (R : ℝ) := by
    apply (Real.log_lt_log_iff (Real.rpow_pos_of_pos hX₀ _) hR₀).mp
    rw [Real.log_rpow hX₀]
    change (1/100:ℝ)*Real.log (X : ℝ) < u
    linarith
  have hqM : q ≤ M := by
    exact_mod_cast (Real.log_le_log_iff hqR hMR).mp (by linarith : Real.log (q : ℝ) ≤ Real.log (M : ℝ))
  exact ⟨hw, hq, hH, hM, hHl, hMl', hMu, hXl, hXu, hql, hquw, hqdiv, hqsm, hcop, hBl, hBr, hqM⟩

theorem SeparatingScale.log_length_lower {r R : ℕ} (h : SeparatingScale r R)
    (hR : 0 < R) :
    Real.log (R : ℝ) / 5 ≤ Real.log (separatingLength r R : ℝ) := by
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have he := Real.log_le_log (Real.rpow_pos_of_pos hR' _) h.M_lower
  rw [Real.log_rpow hR'] at he
  linarith

theorem SeparatingScale.log_lengthQuotient_lower {r R : ℕ} (h : SeparatingScale r R)
    (hR : 0 < R) :
    Real.log (R : ℝ) / 6 ≤ Real.log (separatingLengthQuotient r R : ℝ) := by
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have he := Real.log_le_log (Real.rpow_pos_of_pos hR' _) h.H_lower
  rw [Real.log_rpow hR'] at he
  linarith

theorem SeparatingScale.log_X_lower {r R : ℕ} (h : SeparatingScale r R) (hR : 0 < R) :
    Real.log (R : ℝ) / 5 ≤ Real.log (separatingScaleX r R : ℝ) := by
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have he := Real.log_le_log (Real.rpow_pos_of_pos hR' _) h.X_lower
  rw [Real.log_rpow hR'] at he
  linarith

theorem SeparatingScale.log_length_upper {r R : ℕ} (h : SeparatingScale r R)
    (hR : 0 < R) :
    Real.log (separatingLength r R : ℝ) ≤ Real.log (R : ℝ) / 4 := by
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have he := Real.log_le_log (show (0 : ℝ) < separatingLength r R by exact_mod_cast h.M_pos)
    h.M_upper
  rw [Real.log_rpow hR'] at he
  linarith

theorem SeparatingScale.sqrt_X_le_length {r R : ℕ} (h : SeparatingScale r R) :
    (separatingScaleX r R : ℝ)^(1/2 : ℝ) ≤ (separatingLength r R : ℝ) := by
  rw [← Real.sqrt_eq_rpow]
  apply (Real.sqrt_le_iff).mpr
  refine ⟨Nat.cast_nonneg _, ?_⟩
  push_cast [separatingScaleX]
  have hqM : (separatingModulus r : ℝ) ≤ separatingLength r R := by exact_mod_cast h.q_le_M
  simpa only [pow_two] using mul_le_mul_of_nonneg_right hqM (Nat.cast_nonneg _)

private theorem separating_next_atTop {β : ℝ} {r : ℕ → ℕ}
    (hr : AdmissibleBetaDenominators β r) :
    Tendsto (fun j : ℕ => (r (j+1) : ℝ)) atTop atTop :=
  (tendsto_natCast_atTop_atTop.comp hr.1.tendsto_atTop).comp (tendsto_add_atTop_nat 1)

/-- The quotient length tends to infinity along the same sequence. -/
theorem tendsto_separatingLengthQuotient {β : ℝ} {r : ℕ → ℕ}
    (hr : AdmissibleBetaDenominators β r) :
    Tendsto (fun j => separatingLengthQuotient (r j) (r (j+1))) atTop atTop := by
  apply (tendsto_natCast_atTop_iff (R := ℝ)).mp
  apply tendsto_atTop_mono' _ _ ((tendsto_rpow_atTop (show 0 < (1/6:ℝ) by norm_num)).comp
    (separating_next_atTop hr))
  exact (eventually_separatingScale hr).mono (fun _ h => h.H_lower)

/-- The length parameter tends to infinity. -/
theorem tendsto_separatingLength {β : ℝ} {r : ℕ → ℕ}
    (hr : AdmissibleBetaDenominators β r) :
    Tendsto (fun j => separatingLength (r j) (r (j+1))) atTop atTop := by
  apply (tendsto_natCast_atTop_iff (R := ℝ)).mp
  apply tendsto_atTop_mono' _ _ ((tendsto_rpow_atTop (show 0 < (1/5:ℝ) by norm_num)).comp
    (separating_next_atTop hr))
  exact (eventually_separatingScale hr).mono (fun _ h => h.M_lower)

theorem tendsto_separatingScaleX {β : ℝ} {r : ℕ → ℕ}
    (hr : AdmissibleBetaDenominators β r) :
    Tendsto (fun j => separatingScaleX (r j) (r (j+1))) atTop atTop := by
  apply (tendsto_natCast_atTop_iff (R := ℝ)).mp
  apply tendsto_atTop_mono' _ _ ((tendsto_rpow_atTop (show 0 < (1/5:ℝ) by norm_num)).comp
    (separating_next_atTop hr))
  exact (eventually_separatingScale hr).mono (fun _ h => h.X_lower)

private theorem separating_w_le_log {r R : ℕ} (h : SeparatingScale r R) :
    (separatingW r : ℝ) ≤ Real.log (r : ℝ) := by
  apply Nat.floor_le
  by_contra! hneg
  have hz : separatingW r = 0 := Nat.floor_of_nonpos hneg.le
  have := h.w_large
  omega

private theorem separating_log_q_le_square {r R : ℕ} (h : SeparatingScale r R) :
    Real.log (separatingModulus r : ℝ) ≤ (Real.log (r : ℝ))^2 :=
  h.log_q_upper.trans (pow_le_pow_left₀ (Nat.cast_nonneg _) (separating_w_le_log h) 2)

/-- Every fixed product of powers of (q) and (r) is dominated by
positive powers of the quotient length. -/
theorem eventually_separatingLengthQuotient_subpower {β : ℝ} {r : ℕ → ℕ}
    (hr : AdmissibleBetaDenominators β r) (B C : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j : ℕ in atTop,
      (separatingModulus (r j) : ℝ)^B * (r j : ℝ)^C ≤
        (separatingLengthQuotient (r j) (r (j+1)) : ℝ)^ε := by
  let K : ℝ := 6*((B : ℝ)+C+1)/ε
  have hK : 0 < K := by dsimp [K]; positivity
  have hLogR : Tendsto (fun j => Real.log (r j : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hr.1.tendsto_atTop)
  obtain ⟨a, ha, hprime, hrest⟩ := hr.2
  filter_upwards [eventually_separatingScale hr, eventually_separatingLogPower hr 2 K hK,
    hLogR.eventually_ge_atTop 1] with j hj hg ht
  let q := separatingModulus (r j)
  let H := separatingLengthQuotient (r j) (r (j+1))
  let R := r (j+1)
  let t := Real.log (r j : ℝ)
  have hq : (0 : ℝ) < q := by exact_mod_cast hj.q_pos
  have hb : (0 : ℝ) < r j := by exact_mod_cast (hprime j).1.pos
  have hH : (0 : ℝ) < H := by exact_mod_cast hj.H_pos
  have hHlog := hj.log_lengthQuotient_lower (hprime (j+1)).1.pos
  have hqlog := separating_log_q_le_square hj
  have htt : t ≤ t^2 := by
    have ht₀ : 0 ≤ t := by dsimp [t]; linarith
    have ht₁ : 1 ≤ t := ht
    nlinarith only [mul_nonneg ht₀ (sub_nonneg.mpr ht₁)]
  change K * t^(2:ℝ) ≤ Real.log (R : ℝ) at hg
  rw [Real.rpow_two] at hg
  have hFactor := mul_le_mul_of_nonneg_left hg hε.le
  have hCancel : ε*K = 6*((B : ℝ)+C+1) := by dsimp [K]; field_simp
  rw [← mul_assoc, hCancel] at hFactor
  change (q : ℝ)^B * (r j : ℝ)^C ≤ (H : ℝ)^ε
  apply (Real.log_le_log_iff (mul_pos (pow_pos hq _) (pow_pos hb _)) (Real.rpow_pos_of_pos hH _)).mp
  rw [Real.log_mul (pow_pos hq _).ne' (pow_pos hb _).ne', Real.log_pow, Real.log_pow, Real.log_rpow hH]
  change (B : ℝ)*Real.log (q : ℝ) + (C : ℝ)*t ≤ ε*Real.log (H : ℝ)
  calc
    _ ≤ (B : ℝ)*t^2 + (C : ℝ)*t^2 :=
      add_le_add (mul_le_mul_of_nonneg_left hqlog (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_left htt (Nat.cast_nonneg _))
    _ ≤ _ := by
      have he := mul_le_mul_of_nonneg_left hHlog hε.le
      nlinarith only [he, hFactor, sq_nonneg t]

/-- The exact modulus sequence is sub-power relative to (M), even after
raising it to any fixed power. -/
theorem eventually_separatingModulus_subpower {β : ℝ} {r : ℕ → ℕ}
    (hr : AdmissibleBetaDenominators β r) (B : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j : ℕ in atTop,
      (separatingModulus (r j) : ℝ)^B ≤ (separatingLength (r j) (r (j+1)) : ℝ)^ε := by
  obtain ⟨a, ha, hprime, hrest⟩ := hr.2
  filter_upwards [eventually_separatingLengthQuotient_subpower hr B 0 hε] with j hj
  rw [pow_zero, mul_one] at hj
  refine hj.trans (Real.rpow_le_rpow (Nat.cast_nonneg _) ?_ hε.le)
  push_cast [separatingLength]
  have hb : (1 : ℝ) ≤ r j := by exact_mod_cast (hprime j).1.one_le
  exact le_mul_of_one_le_left (Nat.cast_nonneg _) hb

/-- The step required by the Heisenberg progression estimate, uniformly
for exponents bounded by a fixed integer. -/
theorem eventually_separatingStep {β : ℝ} {r : ℕ → ℕ}
    (hr : AdmissibleBetaDenominators β r) (B : ℕ) :
    ∀ᶠ j : ℕ in atTop,
      ((separatingModulus (r j)^(B+1) : ℕ) : ℝ) ≤
        ((separatingModulus (r j) : ℝ)*separatingLength (r j) (r (j+1)))^(1/10000 : ℝ) := by
  filter_upwards [eventually_separatingScale hr,
    eventually_separatingModulus_subpower hr (B+1)
      (by norm_num : (0 : ℝ) < 1/10000)] with j hj hstep
  rw [Nat.cast_pow]
  refine hstep.trans (Real.rpow_le_rpow (Nat.cast_nonneg _) ?_ (by norm_num))
  have hq : (1 : ℝ) ≤ separatingModulus (r j) := by exact_mod_cast hj.q_pos
  exact le_mul_of_one_le_left (Nat.cast_nonneg _) hq

private theorem eventually_log_length_power {β : ℝ} {r : ℕ → ℕ}
    (hr : AdmissibleBetaDenominators β r) (p : ℝ) :
    ∀ᶠ j : ℕ in atTop,
      (Real.log (r j : ℝ))^p ≤ Real.log (separatingLength (r j) (r (j+1)) : ℝ) := by
  obtain ⟨a, ha, hprime, hrest⟩ := hr.2
  filter_upwards [eventually_separatingScale hr,
      eventually_separatingLogPower hr p 5 (by norm_num)] with j hj hP
  exact ((le_div_iff₀ (by norm_num : 0 < (5 : ℝ))).mpr (by convert hP using 1; ring)).trans
    (hj.log_length_lower (hprime (j+1)).1.pos)

theorem eventually_separatingModulus_log_power {β : ℝ} {r : ℕ → ℕ}
    (hr : AdmissibleBetaDenominators β r) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j : ℕ in atTop, Real.log (separatingModulus (r j) : ℝ) ≤
      (Real.log (separatingLength (r j) (r (j+1)) : ℝ))^ε := by
  filter_upwards [eventually_separatingScale hr, eventually_log_length_power hr (2/ε)] with j hj hP
  have ht : 0 ≤ Real.log (r j : ℝ) := (Nat.cast_nonneg _).trans (separating_w_le_log hj)
  refine (separating_log_q_le_square hj).trans ?_
  have hh := Real.rpow_le_rpow (Real.rpow_nonneg ht _) hP hε.le
  rw [← Real.rpow_mul ht, div_mul_cancel₀ _ hε.ne', Real.rpow_two] at hh
  exact hh

theorem eventually_separatingModulus_subexponential {β : ℝ} {r : ℕ → ℕ}
    (hr : AdmissibleBetaDenominators β r) :
    ∀ᶠ j : ℕ in atTop, (separatingModulus (r j) : ℝ) ≤
      Real.exp (Real.log ((separatingModulus (r j) * separatingLength (r j) (r (j+1))^2 : ℕ) : ℝ) ^
        (1/10 : ℝ)) := by
  filter_upwards [eventually_separatingScale hr,
    eventually_separatingModulus_log_power hr (by norm_num : (0 : ℝ) < 1/10)] with j hj hq
  let q := separatingModulus (r j)
  let M := separatingLength (r j) (r (j+1))
  let N := q*M^2
  have hqR : (0 : ℝ) < q := by exact_mod_cast hj.q_pos
  have hMR : (0 : ℝ) < M := by exact_mod_cast hj.M_pos
  have hM₁ : (1 : ℝ) ≤ M := by exact_mod_cast hj.M_pos
  have hMN : (M : ℝ) ≤ N := by
    push_cast [N]
    have hq₁ : (1 : ℝ) ≤ q := by exact_mod_cast hj.q_pos
    calc
      _ ≤ (M : ℝ)^2 := by nlinarith only [mul_nonneg hMR.le (sub_nonneg.mpr hM₁)]
      _ ≤ _ := le_mul_of_one_le_left (by positivity) hq₁
  have hlog := Real.log_le_log hMR hMN
  change (q : ℝ) ≤ Real.exp ((Real.log (N : ℝ))^(1/10 : ℝ))
  rw [← Real.exp_log hqR]
  exact Real.exp_le_exp.mpr (hq.trans (Real.rpow_le_rpow (Real.log_nonneg hM₁) hlog (by norm_num)))


theorem SeparatingScale.length_le_spatialScale {r R : ℕ} (h : SeparatingScale r R) :
    separatingLength r R ≤ separatingSpatialScale r R := by
  unfold separatingSpatialScale
  have hM := h.M_pos
  have hq := h.q_pos
  calc
    _ ≤ (separatingLength r R)^2 := by
      rw [pow_two]
      exact Nat.le_mul_of_pos_left _ hM
    _ ≤ _ := Nat.le_mul_of_pos_left _ hq

theorem SeparatingScale.log_length_le_spatialScale {r R : ℕ} (h : SeparatingScale r R) :
    Real.log (separatingLength r R : ℝ) ≤ Real.log (separatingSpatialScale r R : ℝ) :=
  Real.log_le_log (by exact_mod_cast h.M_pos) (by exact_mod_cast h.length_le_spatialScale)

/-- The smoothness, divisibility and cutoff conditions hold for every fixed
positive choice of the cutoff exponents and every fixed starting threshold. -/
theorem eventually_separatingRelativeModulus {β : ℝ} {r : ℕ → ℕ}
    (hr : AdmissibleBetaDenominators β r) {c₀ cRel : ℝ} (hc₀ : 0 < c₀)
    (hcRel : 0 < cRel) (w₀ : ℕ) :
    ∀ᶠ j : ℕ in atTop, RelativeModulus c₀ cRel w₀ (separatingSpatialScale (r j) (r (j+1)))
      (separatingModulus (r j)) (separatingW (r j)) := by
  let d := c₀*cRel
  have hd : 0 < d := mul_pos hc₀ hcRel
  have ht := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hr.1.tendsto_atTop)
  have hLogM := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop.comp (tendsto_separatingLength hr))
  filter_upwards [eventually_separatingScale hr, eventually_log_length_power hr (1/d),
    ht.eventually_ge_atTop (w₀ : ℝ), hLogM.eventually_ge_atTop 1] with j hj hp hlog hw
  let N := separatingSpatialScale (r j) (r (j+1))
  let t := Real.log (r j : ℝ)
  have hNlog := hj.log_length_le_spatialScale
  have hN : 1 ≤ Real.log (N : ℝ) := hw.trans hNlog
  have hPow : t ≤ (Real.log (N : ℝ))^d := by
    have ht0 : 0 ≤ t := (Nat.cast_nonneg _).trans (separating_w_le_log hj)
    have hm := Real.rpow_le_rpow (Real.rpow_nonneg ht0 _) (hp.trans hNlog) hd.le
    rwa [← Real.rpow_mul ht0, one_div_mul_cancel hd.ne', Real.rpow_one] at hm
  refine ⟨Nat.le_floor hlog, hj.q_pos, ?_, hj.q_divisible, hj.q_smooth, hj.log_q_upper⟩
  calc
    (separatingW (r j) : ℝ) ≤ t := separating_w_le_log hj
    _ ≤ (Real.log (N : ℝ))^d := hPow
    _ = ((Real.log (N : ℝ))^c₀)^cRel := Real.rpow_mul (by linarith) _ _
    _ ≤ _ := Real.rpow_le_rpow (by positivity) (cramerCutoff_log_bounds hc₀.le hN).2.1 hcRel.le

/-- The parameter lengths lie in the full smooth-modulus scale window as
well as satisfying the exact relation (N=qM^2). -/
theorem eventually_separatingRelativeScaleWindow {β : ℝ} {r : ℕ → ℕ}
    (hr : AdmissibleBetaDenominators β r) :
    ∀ᶠ j : ℕ in atTop,
      RelativeScaleWindow 2 (separatingSpatialScale (r j) (r (j+1)))
        (separatingLength (r j) (r (j+1))) := by
  filter_upwards [eventually_separatingScale hr,
    eventually_separatingModulus_log_power hr (by norm_num : (0 : ℝ) < 1/2)]
    with j hj hq
  let N := separatingSpatialScale (r j) (r (j+1))
  let q := separatingModulus (r j)
  let M := separatingLength (r j) (r (j+1))
  have hqR : (0 : ℝ) < q := by exact_mod_cast hj.q_pos
  have hMR : (0 : ℝ) < M := by exact_mod_cast hj.M_pos
  have hq₁ : (1 : ℝ) ≤ q := by exact_mod_cast hj.q_pos
  have hMR₁ : (1 : ℝ) ≤ M := by exact_mod_cast hj.M_pos
  have hN_eq : (N : ℝ) = (q : ℝ)*(M : ℝ)^2 := by
    simp [N, separatingSpatialScale, q, M]
  have hNR : (0 : ℝ) < N := by rw [hN_eq]; positivity
  have hLog : Real.log (N : ℝ) = Real.log (q : ℝ) + 2*Real.log (M : ℝ) := by
    rw [hN_eq, Real.log_mul hqR.ne' (pow_pos hMR _).ne', Real.log_pow]
    norm_cast
  have hq' : Real.log (q : ℝ) ≤ Real.sqrt (Real.log (N : ℝ)) := by
    rw [Real.sqrt_eq_rpow]
    exact hq.trans (Real.rpow_le_rpow (Real.log_nonneg hMR₁) hj.log_length_le_spatialScale
      (by norm_num))
  change (N : ℝ)^(1/(2:ℝ))*Real.exp (-(2:ℝ)*Real.sqrt (Real.log (N : ℝ))) ≤ (M : ℝ) ∧
    (M : ℝ) ≤ (N : ℝ)^(1/(2:ℝ))
  constructor
  · have h : 0 < (N : ℝ)^(1/(2:ℝ))*Real.exp (-(2:ℝ)*Real.sqrt (Real.log (N : ℝ))) := by
      positivity
    apply (Real.log_le_log_iff h hMR).mp
    rw [Real.log_mul (Real.rpow_pos_of_pos hNR _).ne' (Real.exp_pos _).ne',
      Real.log_rpow hNR, Real.log_exp, hLog]
    rw [hLog] at hq'
    linarith only [hq', Real.sqrt_nonneg (Real.log (q : ℝ) + 2*Real.log (M : ℝ))]
  · apply (Real.log_le_log_iff hMR (Real.rpow_pos_of_pos hNR _)).mp
    rw [Real.log_rpow hNR, hLog]
    linarith only [Real.log_nonneg hq₁]

/-- The quadratic coefficient factor on the exceptional residue class is
little-oh of the quotient length. -/
theorem tendsto_separatingCoefficient_div_lengthQuotient {β : ℝ} {r : ℕ → ℕ}
    (hr : AdmissibleBetaDenominators β r) (a : ℕ → ℕ) (ha : ∀ j, a j ≤ r j) :
    Tendsto (fun j : ℕ => (a j : ℝ)*(separatingModulus (r j) : ℝ)^2*(r j : ℝ) /
      (separatingLengthQuotient (r j) (r (j+1)) : ℝ)) atTop (𝓝 0) := by
  have hl : Tendsto (fun j : ℕ => (separatingLengthQuotient (r j) (r (j+1)) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_separatingLengthQuotient hr)
  apply squeeze_zero' (Eventually.of_forall (fun _ => by positivity)) ?_
    ((tendsto_rpow_neg_atTop (show 0 < (1/2 : ℝ) by norm_num)).comp hl)
  filter_upwards [eventually_separatingScale hr,
    eventually_separatingLengthQuotient_subpower hr 2 2 (by norm_num : (0 : ℝ) < 1/2)]
    with j hj hP
  let H := separatingLengthQuotient (r j) (r (j+1))
  have hH : (0 : ℝ) < H := by exact_mod_cast hj.H_pos
  change (a j : ℝ)*(separatingModulus (r j) : ℝ)^2*(r j : ℝ)/(H : ℝ) ≤
    (H : ℝ)^(-(1/2) : ℝ)
  apply (div_le_iff₀ hH).mpr
  have hp : (H : ℝ)^(-(1/2) : ℝ)*(H : ℝ) = (H : ℝ)^(1/2 : ℝ) := by
    calc
      _ = (H : ℝ)^(-(1/2) : ℝ)*(H : ℝ)^(1:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hH, show -(1/2:ℝ)+1 = 1/2 by norm_num]
  rw [hp]
  refine le_trans ?_ hP
  have h : (a j : ℝ) ≤ r j := by exact_mod_cast ha j
  calc
    _ ≤ (r j : ℝ)*(separatingModulus (r j) : ℝ)^2*(r j : ℝ) := by gcongr
    _ = _ := by ring

/-- The bracket phase's error bound on the chosen residue class tends to
zero at the actual argument scale (qM). -/
theorem tendsto_separatingErrorScale {β : ℝ} {r : ℕ → ℕ}
    (hr : AdmissibleBetaDenominators β r) {D : ℝ} (hD : 0 ≤ D) :
    Tendsto (fun j : ℕ => D/(r (j+1) : ℝ) *
      ((separatingModulus (r j) : ℝ)*(separatingLength (r j) (r (j+1)) : ℝ))^2)
      atTop (𝓝 0) := by
  have hn := (tendsto_rpow_neg_atTop (show 0 < (1/3:ℝ) by norm_num)).comp (separating_next_atTop hr)
  have hzero : Tendsto (fun j : ℕ => D*(r (j+1) : ℝ)^(-(1/3) : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x := D)).mul hn
  apply squeeze_zero' (Eventually.of_forall (fun _ => by positivity)) ?_ hzero
  obtain ⟨a, ha, hp, hrest⟩ := hr.2
  filter_upwards [eventually_separatingScale hr] with j hj
  let R := r (j+1)
  let X := separatingScaleX (r j) R
  have hR : (0 : ℝ) < R := by exact_mod_cast (hp (j+1)).1.pos
  have hX : (X : ℝ) = (separatingModulus (r j) : ℝ)*(separatingLength (r j) R : ℝ) := by
    simp [X, separatingScaleX]
  change D/(R : ℝ) * _ ≤ D*(R : ℝ)^(-(1/3) : ℝ)
  rw [← hX]
  calc
    _ ≤ D/(R : ℝ) * ((R : ℝ)^(1/3 : ℝ))^2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hj.X_upper 2)
        (div_nonneg hD hR.le)
    _ = D*((R : ℝ)^(2/3 : ℝ)/(R : ℝ)) := by
      rw [← Real.rpow_mul_natCast hR.le]
      norm_num
      ring
    _ = D*((R : ℝ)^(2/3 : ℝ)/(R : ℝ)^(1:ℝ)) := by rw [Real.rpow_one]
    _ = _ := by rw [← Real.rpow_sub hR]; norm_num

theorem tendsto_separatingApproximation {β : ℝ} {r : ℕ → ℕ}
    (hr : AdmissibleBetaDenominators β r) (a : ℕ → ℕ) {D : ℝ} (hD : 0 ≤ D)
    (hApprox₀ : ∀ j, 0 ≤ β - (a j : ℝ)/(r j : ℝ))
    (hApprox₁ : ∀ j, β - (a j : ℝ)/(r j : ℝ) ≤ D/(r (j+1) : ℝ)) :
    Tendsto (fun j : ℕ => (β - (a j : ℝ)/(r j : ℝ)) *
      ((separatingModulus (r j) : ℝ)*(separatingLength (r j) (r (j+1)) : ℝ))^2)
      atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun j => mul_nonneg (hApprox₀ j) (sq_nonneg _)))
    (Eventually.of_forall (fun j => mul_le_mul_of_nonneg_right (hApprox₁ j) (sq_nonneg _)))
    (tendsto_separatingErrorScale hr hD)


/-- The floor definition selects the largest power allowed by the
logarithmic modulus budget. -/
theorem separatingExponent_maximal {r e : ℕ} (hw : 16 ≤ separatingW r)
    (he : Real.log ((initialModulus (separatingW r)^e : ℕ) : ℝ) ≤ (separatingW r : ℝ)^2) :
    e ≤ separatingExponent r := by
  let L := initialModulus (separatingW r)
  have hL₀ : 0 < L := initialModulus_pos _
  have h16 : 16 ∣ L := by
    unfold L initialModulus
    exact Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr ⟨by decide, hw⟩)
  have hL₁ : (1 : ℝ) < L := by
    have h := Nat.le_of_dvd hL₀ h16
    exact_mod_cast (show 1 < L by omega)
  have hlogL := Real.log_pos hL₁
  change Real.log ((L^e : ℕ) : ℝ) ≤ _ at he
  rw [Nat.cast_pow, Real.log_pow] at he
  exact Nat.le_floor ((le_div_iff₀ hlogL).mpr he)

/-- The fourth power of the double logarithm of (M) and the logarithm
of (q) are comparable on the constructed sequence. -/
theorem eventually_separatingLogModulus_logLogLength {β : ℝ} {r : ℕ → ℕ}
    (hr : AdmissibleBetaDenominators β r) :
    ∀ᶠ j : ℕ in atTop,
      let v := Real.log (Real.log (separatingLength (r j) (r (j+1)) : ℝ))
      v^4/8 ≤ Real.log (separatingModulus (r j) : ℝ) ∧
        Real.log (separatingModulus (r j) : ℝ) ≤ 16*v^4 := by
  have hscales := eventually_separatingScale hr
  obtain ⟨hMono, a, _, hPrime, c, C, D, hc, hC, hD, hBounds⟩ := hr
  let t := fun j : ℕ => Real.log (r j : ℝ)
  let s := fun j : ℕ => Real.sqrt (t j)
  have ht : Tendsto t atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hMono.tendsto_atTop)
  have hs : Tendsto s atTop atTop := by
    simpa only [s, Real.sqrt_eq_rpow, Function.comp_apply] using
      (tendsto_rpow_atTop (show 0 < (1/2 : ℝ) by norm_num)).comp ht
  have hExp : Tendsto (fun j => Real.exp (s j)) atTop atTop := Real.tendsto_exp_atTop.comp hs
  filter_upwards [hscales, hs.eventually_ge_atTop (2*Real.log 10),
    hExp.eventually_ge_atTop (max (2*|Real.log c|) |Real.log C|)] with j hj hsg hExpG
  let R := r (j+1)
  let M := separatingLength (r j) R
  let q := separatingModulus (r j)
  let u := Real.log (R : ℝ)
  let m := Real.log (M : ℝ)
  let v := Real.log m
  have hR : 0 < R := (hPrime (j+1)).1.pos
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have hLower := Real.log_le_log (mul_pos hc (Real.exp_pos _)) (hBounds j).1
  have hUpper := Real.log_le_log hR' (hBounds j).2.1
  change Real.log (c*Real.exp (Real.exp (s j))) ≤ u at hLower
  change u ≤ Real.log (C*Real.exp (Real.exp (s j))) at hUpper
  rw [Real.log_mul hc.ne' (Real.exp_pos _).ne', Real.log_exp] at hLower
  rw [Real.log_mul hC.ne' (Real.exp_pos _).ne', Real.log_exp] at hUpper
  have hExpc : 2*|Real.log c| ≤ Real.exp (s j) := (le_max_left _ _).trans hExpG
  have hExpC : |Real.log C| ≤ Real.exp (s j) := (le_max_right _ _).trans hExpG
  have hml : Real.exp (s j)/10 ≤ m := by
    have h := hj.log_length_lower hR
    change u/5 ≤ m at h
    linarith only [h, hExpc, hLower, neg_le_abs (Real.log c)]
  have hmu : m ≤ Real.exp (s j) := by
    have h := hj.log_length_upper hR
    change m ≤ u/4 at h
    linarith only [h, hExpC, hUpper, le_abs_self (Real.log C), Real.exp_pos (s j)]
  have hm : 0 < m := (div_pos (Real.exp_pos _) (by norm_num)).trans_le hml
  have hvl : s j/2 ≤ v := by
    have hh := Real.log_le_log (div_pos (Real.exp_pos _) (by norm_num : 0 < (10:ℝ))) hml
    rw [Real.log_div (Real.exp_pos _).ne' (by norm_num), Real.log_exp] at hh
    change s j - Real.log 10 ≤ v at hh
    linarith
  have hvu : v ≤ s j := by
    have hh := Real.log_le_log hm hmu
    simpa only [Real.log_exp] using hh
  have hs₀ : 0 ≤ s j := Real.sqrt_nonneg _
  have hv₀ : 0 ≤ v := (div_nonneg hs₀ (by norm_num)).trans hvl
  have ht₀ : 0 ≤ t j := Real.log_nonneg (by exact_mod_cast (hPrime j).1.one_le)
  have hs4 : (s j)^4 = (t j)^2 := by
    calc
      _ = ((s j)^2)^2 := by ring
      _ = _ := by rw [show (s j)^2 = t j from Real.sq_sqrt ht₀]
  have hv4 := pow_le_pow_left₀ hv₀ hvu 4
  have hs4' := pow_le_pow_left₀ (div_nonneg hs₀ (by norm_num : (0:ℝ) ≤ 2)) hvl 4
  have hsq : (t j)^2 ≤ 16*v^4 := by
    calc
      _ = 16*(s j/2)^4 := by rw [← hs4]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hs4' (by norm_num)
  change v^4/8 ≤ Real.log (q : ℝ) ∧ Real.log (q : ℝ) ≤ 16*v^4
  refine ⟨?_, (separating_log_q_le_square hj).trans hsq⟩
  rw [hs4] at hv4
  exact (div_le_div_of_nonneg_right hv4 (by norm_num : (0:ℝ) ≤ 8)).trans hj.log_q_lower

end NilBohr
