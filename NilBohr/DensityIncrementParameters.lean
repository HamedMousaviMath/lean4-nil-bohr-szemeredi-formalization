import NilBohr.DensityIncrementProof

/-! Power-scale bookkeeping for the uniform density increment. -/

open Filter
open scoped Topology

namespace NilBohr

theorem eventually_linearSqrt_lt {a : ℝ} (ha : 0 < a) (b c : ℝ) :
    ∀ᶠ t : ℝ in atTop, b * Real.sqrt t + c < a * t := by
  have hsqrt : Tendsto Real.sqrt atTop atTop := by
    rw [show Real.sqrt = fun t => t ^ (1/2 : ℝ) from funext Real.sqrt_eq_rpow]
    exact tendsto_rpow_atTop (by norm_num)
  filter_upwards [hsqrt.eventually_ge_atTop (max 1 ((b + |c| + 1) / a)),
    eventually_ge_atTop (0 : ℝ)] with t hs ht
  have hs₁ : 1 ≤ Real.sqrt t := (le_max_left _ _).trans hs
  have hs₂ : b + |c| + 1 ≤ a * Real.sqrt t := by
    rw [mul_comm a]
    exact (div_le_iff₀ ha).mp ((le_max_right _ _).trans hs)
  have hs₃ : (b + |c| + 1) * Real.sqrt t ≤ a * t := calc
    _ ≤ (a * Real.sqrt t) * Real.sqrt t :=
      mul_le_mul_of_nonneg_right hs₂ (Real.sqrt_nonneg t)
    _ = a * (Real.sqrt t)^2 := by ring
    _ = _ := by rw [Real.sq_sqrt ht]
  have hc := mul_le_mul_of_nonneg_left hs₁ (abs_nonneg c)
  nlinarith [le_abs_self c]

theorem log_le_two_sqrt_density {t : ℝ} (ht : 0 < t) :
    Real.log t ≤ 2 * Real.sqrt t := by
  have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr ht)
  rw [Real.sqrt_eq_rpow, Real.log_rpow ht, ← Real.sqrt_eq_rpow] at h
  linarith

/-- Exceptional prime-power and collision mass, with the explicit constants
from the finite count bound. -/
noncomputable def densityExceptionMass (k d q M : ℕ) : ℝ :=
  (((k : ℝ)^2 * d) * Real.log (q * M + 1 : ℕ) +
    (4 / Real.log 2) * Real.sqrt (q * M + 1 : ℕ) * (Real.log (q * M + 1 : ℕ))^2) / (M : ℝ)

set_option maxHeartbeats 1200000 in
/-- For polylogarithmic densities and subexponential moduli, the model
cutoff is nonempty, the weak regularity small-scale alternative is rejected,
and exceptional mass is negligible relative to the model density. -/
theorem densityIncrement_parameter_bounds {d k : ℕ} (hd : 0 < d)
    {τ c₃ A₁ D₁ B : ℝ} (hτ : 0 < τ) (hc₃ : 0 < c₃)
    (hA₁ : 0 < A₁) (hD₁ : 0 < D₁) (hB : 0 < B) :
    ∀ᶠ N : ℕ in atTop, ∀ {q : ℕ} {δ : ℝ}, 0 < q → 0 < δ →
      Real.log q ≤ Real.sqrt (Real.log N) →
      δ^(-(k : ℝ)) ≤ Real.log N →
      let M := parameterLength N q d
      0 < M ∧ 2 ≤ τ * (M : ℝ) ∧
      A₁ * ((q : ℝ) / (c₃ * δ^k / 8))^D₁ < (M : ℝ) ∧
      densityExceptionMass k d q M ≤ B * δ^k := by
  let a : ℝ := (8 * (d : ℝ))⁻¹
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hd₁ : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have ha : 0 < a := by dsimp [a]; positivity
  let D : ℝ := 2 * (k : ℝ)^2 * d + 32 / Real.log 2
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hD : 0 < D := by dsimp [D]; positivity
  have he : Tendsto (fun t : ℝ => D * (t^3 * Real.exp (-a*t))) atTop (𝓝 (D * 0)) := by
    refine tendsto_const_nhds.mul ?_
    refine (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 3 a ha).congr (fun t => ?_)
    rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  have hN : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hTmin := hN.eventually_ge_atTop (max 1 (2 * Real.log 2))
  have hQgrowth := hN.eventually
    (eventually_linearSqrt_lt ha 1 0)
  have hFloorgrowth := hN.eventually
    (eventually_linearSqrt_lt (show (0 : ℝ) < 1/2 by norm_num)
      ((d - 1 : ℕ) : ℝ) ((d : ℝ) * Real.log 2))
  have hSmallAlt := hN.eventually
    (eventually_linearSqrt_lt (show 0 < 4*a by positivity) (3*D₁)
      (Real.log A₁ + D₁ * (Real.log 8 - Real.log c₃)))
  have hBsmall := hN.eventually (he.eventually (gt_mem_nhds (show D*0 < B by simpa)))
  have hModel := hN.eventually
    ((Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (show 0 < 4*a by positivity))).eventually_ge_atTop (2 / τ))
  filter_upwards [eventually_ge_atTop 2, hTmin, hQgrowth, hFloorgrowth, hSmallAlt, hBsmall, hModel]
    with N hN₂ hTmin hQgrowth hFloorgrowth hSmallAlt hBsmall hModel
  intro q δ hq hδ hlogq hδbound
  let t := Real.log (N : ℝ)
  let s := a * t
  let M := parameterLength N q d
  have ht₁ : 1 ≤ t := (le_max_left _ _).trans hTmin
  have ht₂ : 2 * Real.log 2 ≤ t := (le_max_right _ _).trans hTmin
  have ht : 0 < t := zero_lt_one.trans_le ht₁
  have hs : 0 ≤ s := mul_nonneg ha.le ht.le
  have hN' : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN'
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hq₁ : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqsmall : Real.log q ≤ s := by dsimp only [t, s]; linarith
  have hqexp : (q : ℝ) ≤ Real.exp s := by
    rw [← Real.exp_log hqR]
    exact Real.exp_le_exp.mpr hqsmall
  have hsa : 4 * s = t / (2 * (d : ℝ)) := by
    dsimp [s, a]
    field_simp
    ring
  have hsone : s ≤ t / 8 := by
    have hq₀ : (1 : ℝ) / d ≤ 1 := (div_le_iff₀ hdR).mpr (by simpa using hd₁)
    calc
      s = (t / 8) * (1 / (d : ℝ)) := by dsimp [s,a]; ring
      _ ≤ _ := mul_le_of_le_one_right (by positivity) hq₀
  have hqFloor : ((d - 1 : ℕ) : ℝ) * Real.log q + (d : ℝ) * Real.log 2 ≤ t / 2 := by
    have hm := mul_le_mul_of_nonneg_left hlogq (Nat.cast_nonneg (d-1) : (0 : ℝ) ≤ _)
    dsimp only [t]
    linarith
  let R := ((N : ℝ) / (q : ℝ)^(d-1))^((d : ℝ)⁻¹)
  have hR : 0 < R := by dsimp [R]; positivity
  have hexp_scale : 2 * Real.exp (4*s) ≤ R := by
    apply (Real.log_le_log_iff (mul_pos (by norm_num) (Real.exp_pos _)) hR).mp
    dsimp [R, t]
    rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp,
      Real.log_rpow (div_pos hNR (pow_pos hqR _)),
      Real.log_div hNR.ne' (pow_pos hqR _).ne', Real.log_pow, ← div_eq_inv_mul]
    apply (le_div_iff₀ hdR).mpr
    rw [← show t = Real.log (N : ℝ) from rfl, hsa, add_mul, div_mul_eq_mul_div]
    have hfrac : t * (d : ℝ) / (2 * (d : ℝ)) = t / 2 := by field_simp; ring
    rw [hfrac]
    linarith
  have hMexp : Real.exp (4 * s) ≤ (M : ℝ) := by
    have hf : R < (M : ℝ) + 1 := Nat.lt_floor_add_one R
    have h1 : 1 ≤ Real.exp (4 * s) := Real.one_le_exp (by positivity)
    linarith
  have hMpos : 0 < M := by exact_mod_cast (Real.exp_pos _).trans_le hMexp
  have hMpos' : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hMpos
  have hMmodel : 2 ≤ τ * (M : ℝ) := by
    have hME : 2 / τ ≤ Real.exp (4*s) := by
      simpa only [Function.comp_apply, id_eq, s, t, mul_assoc] using hModel
    exact (div_le_iff₀' hτ).mp (hME.trans hMexp)
  have hδinv : (δ^k)⁻¹ ≤ t := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg hδ.le]
    exact hδbound
  have hδmul : 1 ≤ t * δ^k := by
    have hh := mul_le_mul_of_nonneg_right hδinv (pow_nonneg hδ.le k)
    rwa [inv_mul_cancel₀ (pow_pos hδ _).ne'] at hh
  have hδlog : -Real.log (δ^k) ≤ Real.log t := by
    simpa only [Real.log_inv] using Real.log_le_log (inv_pos.mpr (pow_pos hδ k)) hδinv
  have hεpos : 0 < c₃ * δ^k / 8 := by positivity
  have hεlog : Real.log ((q : ℝ) / (c₃ * δ^k / 8)) ≤
        3 * Real.sqrt t + (Real.log 8 - Real.log c₃) := by
    rw [Real.log_div hqR.ne' hεpos.ne', Real.log_div (mul_pos hc₃ (pow_pos hδ _)).ne' (by norm_num),
      Real.log_mul hc₃.ne' (pow_pos hδ _).ne']
    have hlogt := log_le_two_sqrt_density ht
    linarith
  have hMweak : A₁ * ((q : ℝ) / (c₃ * δ^k / 8))^D₁ < (M : ℝ) := by
    apply (Real.log_lt_log_iff (mul_pos hA₁ (Real.rpow_pos_of_pos (div_pos hqR hεpos) _)) hMpos').mp
    rw [Real.log_mul hA₁.ne' (Real.rpow_pos_of_pos (div_pos hqR hεpos) _).ne',
      Real.log_rpow (div_pos hqR hεpos)]
    have hMlog := Real.log_le_log (Real.exp_pos _) hMexp
    rw [Real.log_exp] at hMlog
    have hh := mul_le_mul_of_nonneg_left hεlog hD₁.le
    change 3*D₁ * Real.sqrt t + (Real.log A₁ + D₁ * (Real.log 8 - Real.log c₃)) < 4 * a * t at hSmallAlt
    dsimp only [s] at hMlog
    linarith
  have hMle : (M : ℝ) ≤ N := calc
    _ ≤ (M : ℝ)^d := by
      simpa only [pow_one] using pow_le_pow_right₀ hM1 (show 1 ≤ d by omega)
    _ ≤ (q : ℝ)^(d-1) * (M : ℝ)^d :=
      le_mul_of_one_le_left (by positivity) (one_le_pow₀ hq₁)
    _ ≤ _ := parameterLength_power_le hq hd
  let Y := ((q*M+1 : ℕ) : ℝ)
  have hy : Y ≤ 2 * (q : ℝ) * (M : ℝ) := by
    push_cast [Y]
    nlinarith [mul_le_mul hq₁ hM1 (show (0 : ℝ) ≤ 1 by norm_num) hqR.le]
  have hy₁ : 1 ≤ Y := by dsimp [Y]; exact_mod_cast (Nat.succ_le_succ (Nat.zero_le _))
  have hYlog : 0 ≤ Real.log Y := Real.log_nonneg hy₁
  have hYlogmax : Real.log Y ≤ 2*t := by
    have hlogY := Real.log_le_log (zero_lt_one.trans_le hy₁) hy
    rw [Real.log_mul (mul_pos (by norm_num) hqR).ne' hMpos'.ne',
      Real.log_mul (by norm_num) hqR.ne'] at hlogY
    have hlogM := Real.log_le_log hMpos' hMle
    linarith
  have hm_inv : (M : ℝ)⁻¹ ≤ Real.exp (-s) := by
    rw [Real.exp_neg]
    exact (inv_le_inv₀ hMpos' (Real.exp_pos _)).mpr
      ((Real.exp_le_exp.mpr (by linarith : s ≤ 4*s)).trans hMexp)
  have hqcomp : (q : ℝ) ≤ Real.exp (-2*s) * (M : ℝ) := calc
    _ ≤ Real.exp (2*s) := hqexp.trans (Real.exp_le_exp.mpr (by linarith : s ≤ 2*s))
    _ = Real.exp (-2*s) * Real.exp (4*s) := by rw [← Real.exp_add]; ring_nf
    _ ≤ _ := mul_le_mul_of_nonneg_left hMexp (Real.exp_pos _).le
  have hroot : Real.sqrt Y / (M : ℝ) ≤ 2 * Real.exp (-s) := by
    apply (div_le_iff₀ hMpos').mpr
    have hr := Real.sq_sqrt (zero_le_one.trans hy₁)
    have hprod := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hqcomp (by norm_num : (0:ℝ) ≤ 2)) hMpos'.le
    have he2 : Real.exp (-2*s) = (Real.exp (-s))^2 := by
      rw [← Real.exp_nat_mul]
      push_cast
      ring_nf
    rw [he2] at hprod
    have hbound := hy.trans hprod
    have hsqr : (Real.sqrt Y)^2 ≤ (2 * Real.exp (-s) * (M : ℝ))^2 := by
      rw [hr]
      nlinarith [sq_nonneg (Real.exp (-s) * (M : ℝ))]
    exact (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp hsqr
  have hlogfirst : Real.log Y / (M : ℝ) ≤ 2 * t^2 * Real.exp (-s) := calc
    _ = Real.log Y * (M : ℝ)⁻¹ := div_eq_mul_inv _ _
    _ ≤ (2*t) * Real.exp (-s) := mul_le_mul hYlogmax hm_inv (by positivity) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg (t-1)]) (Real.exp_pos _).le
  have hlogsecond : (Real.sqrt Y / (M : ℝ)) * (Real.log Y)^2 ≤ 8 * t^2 * Real.exp (-s) := calc
    _ ≤ (2 * Real.exp (-s)) * (2*t)^2 := mul_le_mul hroot
      (pow_le_pow_left₀ hYlog hYlogmax _) (by positivity) (by positivity)
    _ = _ := by ring
  have hmass : densityExceptionMass k d q M ≤ D * t^2 * Real.exp (-s) := calc
    _ = ((k : ℝ)^2*d) * (Real.log Y / (M : ℝ)) +
      (4 / Real.log 2) * ((Real.sqrt Y / (M : ℝ)) * (Real.log Y)^2) := by
        dsimp [densityExceptionMass, Y]
        ring
    _ ≤ ((k : ℝ)^2*d) * (2*t^2 * Real.exp (-s)) +
      (4 / Real.log 2) * (8*t^2 * Real.exp (-s)) :=
        add_le_add (mul_le_mul_of_nonneg_left hlogfirst (by positivity))
          (mul_le_mul_of_nonneg_left hlogsecond (by positivity))
    _ = _ := by dsimp [D]; ring
  refine ⟨hMpos, hMmodel, hMweak, hmass.trans ?_⟩
  have hDsmall : D * (t^3 * Real.exp (-a*t)) ≤ B := le_of_lt hBsmall
  have hsmall : D * t^2 * Real.exp (-s) ≤ B * (δ^k) := by
    apply le_of_mul_le_mul_right _ ht
    calc
      _ = D * (t^3 * Real.exp (-a*t)) := by dsimp [s]; ring_nf
      _ ≤ B := hDsmall
      _ ≤ _ := by
        rw [mul_assoc, mul_comm (δ^k)]
        exact le_mul_of_one_le_right hB.le hδmul
  exact hsmall

end NilBohr
