import NilBohr.AdmissibleDenominators

open Filter

namespace NilBohr

private theorem eventually_const_add_mul_lt_sq (A B : ℝ) :
    ∀ᶠ t : ℝ in atTop, A + B * t < t^2 := by
  filter_upwards [eventually_ge_atTop (2*(|A|+|B|+1))] with t ht
  have hA := le_abs_self A
  have hB := le_abs_self B
  have hA₀ := abs_nonneg A
  have hB₀ := abs_nonneg B
  have ht₀ : 0 ≤ t := by linarith
  have ht₁ : 1 ≤ t := by linarith
  have hmul := mul_le_mul_of_nonneg_right (show B ≤ t/2 by linarith) ht₀
  have hsq := mul_le_mul_of_nonneg_right ht₁ ht₀
  nlinarith

private theorem eventually_rpow_log_bound (A K L : ℝ) (hA : 0 < A) (hK : 0 < K) :
    ∀ᶠ R : ℝ in atTop, K * (A * Real.exp (Real.sqrt (Real.log R)))^L < R := by
  have hs : Tendsto (fun R : ℝ => Real.sqrt (Real.log R)) atTop atTop := by
    simpa only [Real.sqrt_eq_rpow, Function.comp_apply] using
      (tendsto_rpow_atTop (show 0 < (1/2 : ℝ) by norm_num)).comp Real.tendsto_log_atTop
  filter_upwards [eventually_ge_atTop (1 : ℝ), hs.eventually
    (eventually_const_add_mul_lt_sq (Real.log K + L * Real.log A) L)] with R hR ht
  have hR₀ : 0 < R := by linarith
  have hlogR : 0 ≤ Real.log R := Real.log_nonneg hR
  have hinner : 0 < A * Real.exp (Real.sqrt (Real.log R)) := by positivity
  refine (Real.log_lt_log_iff (by positivity) hR₀).mp ?_
  rw [Real.log_mul hK.ne' (Real.rpow_pos_of_pos hinner _).ne', Real.log_rpow hinner,
    Real.log_mul hA.ne' (Real.exp_pos _).ne', Real.log_exp]
  rw [Real.sq_sqrt hlogR] at ht
  linarith

private theorem eventually_rpow_le_doubleExpSqrtLog (c : ℝ) (hc : 0 < c) :
    ∀ᶠ R : ℝ in atTop, R^4 ≤ c * Real.exp (Real.exp (Real.sqrt (Real.log R))) := by
  have hs : Tendsto (fun R : ℝ => Real.sqrt (Real.log R)) atTop atTop := by
    simpa only [Real.sqrt_eq_rpow, Function.comp_apply] using
      (tendsto_rpow_atTop (show 0 < (1/2 : ℝ) by norm_num)).comp Real.tendsto_log_atTop
  have he : ∀ᶠ t : ℝ in atTop, 8 * t^2 ≤ Real.exp t := by
    filter_upwards [(isLittleO_rpow_exp_atTop (2 : ℝ)).bound
      (show 0 < (1/8:ℝ) by norm_num)] with t ht
    simp only [Real.rpow_two, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t),
      abs_of_pos (Real.exp_pos t)] at ht
    linarith
  have hh : ∀ᶠ t : ℝ in atTop, -Real.log c ≤ 4*t^2 := by
    filter_upwards [eventually_ge_atTop (|Real.log c|+1)] with t ht
    have hA := abs_nonneg (Real.log c)
    have hB := neg_le_abs (Real.log c)
    have h₁ : 1 ≤ t := by linarith
    have h₂ := mul_le_mul_of_nonneg_right h₁ (show 0 ≤ t by linarith)
    nlinarith
  filter_upwards [eventually_ge_atTop (1 : ℝ), hs.eventually he, hs.eventually hh] with R hR he hh
  have hR₀ : 0 < R := by linarith
  have hlogR : 0 ≤ Real.log R := Real.log_nonneg hR
  have hleft : 0 < R^4 := by positivity
  have hright : 0 < c * Real.exp (Real.exp (Real.sqrt (Real.log R))) := by positivity
  refine (Real.log_le_log_iff hleft hright).mp ?_
  rw [Real.log_pow, Real.log_mul hc.ne' (Real.exp_pos _).ne', Real.log_exp]
  rw [Real.sq_sqrt hlogR] at he hh
  norm_num
  linarith

/-- Both growth estimates for the bracketing pair of denominators in Lemma 6.1.
The constants are uniform over all pairs satisfying the displayed scale bounds. -/
theorem horizontal_scale_bounds (c C L K : ℝ) (hc : 0 < c) (hC : 0 < C)
    (hL : 0 < L) (hK : 0 < K) :
    ∀ᶠ X : ℝ in atTop, ∀ r rNext : ℕ, 0 < r →
      c * denominatorScale r ≤ (rNext : ℝ) → (rNext : ℝ) ≤ C * denominatorScale r →
      X ^ (1/100 : ℝ) < (rNext : ℝ) →
      K * Real.log X ^ L < r ∧ X ^ (1/200 : ℝ) * (r : ℝ)^2 ≤ rNext := by
  let A : ℝ := 100 * (1 + |Real.log C|)
  have hA : 0 < A := by dsimp [A]; positivity
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.mp <|
    (eventually_rpow_log_bound A K L hA hK).and (eventually_rpow_le_doubleExpSqrtLog c hc)
  let R₁ := max R₀ 1
  have hxlarge := (tendsto_rpow_atTop (show 0 < (1/100:ℝ) by norm_num)).eventually
    (eventually_ge_atTop (C * Real.exp (Real.exp (Real.sqrt (Real.log R₁)))))
  filter_upwards [eventually_ge_atTop (2 : ℝ), hxlarge] with X hX hxlarge
  intro r rNext hr hlo hhi hgap
  have hrR : 1 ≤ (r : ℝ) := by exact_mod_cast hr
  have hrpos : 0 < (r : ℝ) := by positivity
  have hXpos : 0 < X := by linarith
  have hXone : 1 ≤ X := by linarith
  have hR₁ : R₁ ≤ (r : ℝ) := by
    by_contra! hbad
    have hmono : denominatorScale r ≤ Real.exp (Real.exp (Real.sqrt (Real.log R₁))) := by
      unfold denominatorScale
      exact Real.exp_le_exp.mpr (Real.exp_le_exp.mpr
        (Real.sqrt_le_sqrt (Real.log_le_log hrpos hbad.le)))
    exact (not_lt_of_ge (hxlarge.trans' (hhi.trans (mul_le_mul_of_nonneg_left hmono hC.le)))) hgap
  have hR := hR₀ (r : ℝ) ((le_max_left _ _).trans hR₁)
  constructor
  · let s := Real.sqrt (Real.log (r : ℝ))
    have hNextpos : 0 < (rNext : ℝ) := (Real.rpow_pos_of_pos hXpos _).trans hgap
    have hlog1 := Real.log_lt_log (Real.rpow_pos_of_pos hXpos _) hgap
    have hlog2 := Real.log_le_log hNextpos hhi
    rw [Real.log_rpow hXpos] at hlog1
    change Real.log (rNext : ℝ) ≤ Real.log (C * Real.exp (Real.exp s)) at hlog2
    rw [Real.log_mul hC.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog2
    have hExp : 1 ≤ Real.exp s := (Real.one_le_exp_iff).mpr (Real.sqrt_nonneg _)
    have hlog : Real.log X ≤ A * Real.exp s := by
      dsimp [A]
      nlinarith [le_abs_self (Real.log C), mul_nonneg (abs_nonneg (Real.log C)) (sub_nonneg.mpr hExp)]
    exact (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Real.log_nonneg hXone) hlog hL.le)
      hK.le).trans_lt hR.1
  · have hpow : (X ^ (1/400 : ℝ))^2 = X ^ (1/200 : ℝ) := by
      rw [← Real.rpow_mul_natCast hXpos.le]
      congr 1
      norm_num
    by_cases hrsmall : (r : ℝ) ≤ X ^ (1/400 : ℝ)
    · calc
        X ^ (1/200 : ℝ) * (r : ℝ)^2 ≤ X ^ (1/200 : ℝ) * (X ^ (1/400 : ℝ))^2 := by gcongr
        _ = X ^ (1/100 : ℝ) := by
          rw [hpow, ← Real.rpow_add hXpos]
          congr 1
          norm_num
        _ ≤ rNext := hgap.le
    · have hsq : X ^ (1/200 : ℝ) ≤ (r : ℝ)^2 := by
        rw [← hpow]
        gcongr
        exact le_of_not_ge hrsmall
      calc
        X ^ (1/200 : ℝ) * (r : ℝ)^2 ≤ (r : ℝ)^2 * (r : ℝ)^2 := by gcongr
        _ = (r : ℝ)^4 := by ring
        _ ≤ rNext := hR.2.trans hlo

private theorem inverse_rpow_bound {X η R : ℝ} (hX : 0 < X) (hη : 0 ≤ η) (hR : 0 < R)
    (h : R ≤ X^(1/20 : ℝ)) : η * X^(-(1/20 : ℝ)) ≤ η / R := by
  rw [Real.rpow_neg hX.le, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left ((inv_le_inv₀ (by positivity) hR).mpr h) hη

set_option maxHeartbeats 1000000 in
/-- The uniform Diophantine conclusion in Lemma 6.1, for any consecutive
approximating pair bracketing `X^(1/100)`. The implied lower constant depends
only on the badly approximable number. The threshold can also depend on the
logarithmic exponent and on the constants in the rational approximations. -/
theorem horizontal_diophantine_bound_uniform_in_beta (α : ℝ) (hα : BadlyApproximable α) :
    ∃ η : ℝ, 0 < η ∧ ∀ (c C D L : ℝ), 0 < c → 0 < C → 0 < D → 0 < L →
    ∀ᶠ X : ℝ in atTop, ∀ (β : ℝ) (a r rNext : ℕ), r.Prime → 0 < a → a < r →
      c * denominatorScale r ≤ (rNext : ℝ) → (rNext : ℝ) ≤ C * denominatorScale r →
      |β - (a : ℝ)/r| ≤ D / (rNext : ℝ) →
      (r : ℝ) ≤ X ^ (1/100 : ℝ) → X ^ (1/100 : ℝ) < (rNext : ℝ) →
      ∀ (v : ℕ) (k l : ℤ), 0 < v → (v : ℝ) ≤ X ^ (1/5000 : ℝ) → ¬ r ∣ v →
      0 < max |(k : ℝ)| |(l : ℝ)| → max |(k : ℝ)| |(l : ℝ)| ≤ Real.log X ^ L →
      η * X ^ (-(1/20 : ℝ)) ≤ torusNorm ((v : ℝ) * (k*α+l*β)) := by
  obtain ⟨b, hb, hbad⟩ := hα
  let η := min (b/2) (1/2)
  have hη : 0 < η := by dsimp [η]; positivity
  refine ⟨η, hη, fun c C D L hc hC hD hL => ?_⟩
  have hlogs := (isLittleO_log_rpow_rpow_atTop L (show 0 < (1/1000 : ℝ) by norm_num)).bound
    (show 0 < (1:ℝ) by norm_num)
  have hlarge := (tendsto_rpow_atTop (show 0 < (13/5000:ℝ) by norm_num)).eventually
    (eventually_ge_atTop (D / η))
  filter_upwards [eventually_ge_atTop (Real.exp 1), hlogs, hlarge,
    horizontal_scale_bounds c C L 1 hc hC hL one_pos] with X hX hlogs hlarge hscale
  have hXone : 1 ≤ X := (Real.one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 1)).trans hX
  have hXpos : 0 < X := (Real.exp_pos 1).trans_le hX
  let W := Real.log X ^ L
  have hWone : 1 ≤ W := Real.one_le_rpow ((Real.le_log_iff_exp_le hXpos).mpr hX) hL.le
  have hW : W ≤ X^(1/1000 : ℝ) := by
    change ‖W‖ ≤ 1 * ‖X^(1/1000 : ℝ)‖ at hlogs
    simpa only [Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans hWone),
      abs_of_pos (Real.rpow_pos_of_pos hXpos _), one_mul] using hlogs
  have hD' : D ≤ η * X^(13/5000 : ℝ) := by
    simpa only [mul_comm] using (div_le_iff₀ hη).mp hlarge
  intro β a r rNext hr ha har hlo hhi happ hrX hgap v k l hv hvX hvr hnon hfreq
  obtain ⟨hWr, hgrowth⟩ := hscale r rNext hr.pos hlo hhi hgap
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast hr.pos
  have hrOne : 1 ≤ (r : ℝ) := by exact_mod_cast hr.pos
  have hvpos : 0 < (v : ℝ) := by exact_mod_cast hv
  have hvOne : 1 ≤ (v : ℝ) := by exact_mod_cast hv
  have hNpos : 0 < (rNext : ℝ) := (Real.rpow_pos_of_pos hXpos _).trans hgap
  have hkW : |(k : ℝ)| ≤ W := (le_max_left _ _).trans hfreq
  have hlW : |(l : ℝ)| ≤ W := (le_max_right _ _).trans hfreq
  have hmass : D * W^2 * (v : ℝ)^2 * (r : ℝ)^2 ≤ η * (rNext : ℝ) := by
    calc
      D * W^2 * (v : ℝ)^2 * (r : ℝ)^2 ≤
          (η * X^(13/5000:ℝ)) * (X^(1/1000:ℝ))^2 * (X^(1/5000:ℝ))^2 * (r : ℝ)^2 := by gcongr
      _ = η * (X^(1/200:ℝ) * (r : ℝ)^2) := by
        have hpow : X^(13/5000:ℝ) * (X^(1/1000:ℝ))^2 * (X^(1/5000:ℝ))^2 = X^(1/200:ℝ) := by
          rw [← Real.rpow_mul_natCast hXpos.le, ← Real.rpow_mul_natCast hXpos.le,
            ← Real.rpow_add hXpos, ← Real.rpow_add hXpos]
          congr 1
          norm_num
        rw [← hpow]
        ring
      _ ≤ η * (rNext : ℝ) := by gcongr
  have hηb : η ≤ b / 2 := min_le_left _ _
  have hη1 : η ≤ 1 / 2 := min_le_right _ _
  by_cases hk : k = 0
  · have hl : l ≠ 0 := by
      intro hl
      simp [hk, hl] at hnon
    have hlr : ¬ (r : ℤ) ∣ l := by
      intro hdvd
      have hle := Nat.le_of_dvd (Int.natAbs_pos.mpr hl) (Int.natCast_dvd.mp hdvd)
      have hrle : (r : ℝ) ≤ |(l : ℝ)| := by
        simpa only [Int.cast_natAbs, Int.cast_abs] using (Nat.cast_le (α := ℝ)).mpr hle
      have hWr' : W < (r : ℝ) := by simpa only [one_mul] using hWr
      exact (not_lt_of_ge (hrle.trans hlW)) hWr'
    have hprime : Prime (r : ℤ) := Nat.prime_iff_prime_int.mp hr
    have hva : ¬ (r : ℤ) ∣ (v : ℤ) * l * (a : ℤ) := by
      intro hdvd
      rcases hprime.dvd_mul.mp hdvd with hvd | had
      · rcases hprime.dvd_mul.mp hvd with hvd | hld
        · exact hvr (Int.natCast_dvd_natCast.mp hvd)
        · exact hlr hld
      · exact (not_le_of_gt har) (Nat.le_of_dvd ha (Int.natCast_dvd_natCast.mp had))
    have hlin : D * |(l : ℝ)| * (v : ℝ) * (r : ℝ) ≤ η * (rNext : ℝ) := by
      have hle : D * |(l : ℝ)| * (v : ℝ) * (r : ℝ) ≤ D * W^2 * (v : ℝ)^2 * (r : ℝ)^2 := by
        gcongr
        · exact hlW.trans (by nlinarith [mul_le_mul_of_nonneg_right hWone (show 0 ≤ W by linarith)])
        · nlinarith [mul_le_mul_of_nonneg_right hvOne hvpos.le]
        · nlinarith [mul_le_mul_of_nonneg_right hrOne hrpos.le]
      exact hle.trans hmass
    have herr : |(l : ℝ)| * v * |β - (a : ℝ)/r| ≤ η / (r : ℝ) := by
      apply (le_div_iff₀ hrpos).mpr
      calc
        (|(l : ℝ)| * v * |β - (a : ℝ)/r|) * r = (|(l : ℝ)| * v * r) * |β - (a : ℝ)/r| := by ring
        _ ≤ (|(l : ℝ)| * v * r) * (D / (rNext : ℝ)) := by gcongr
        _ = (D * |(l : ℝ)| * v * r) / (rNext : ℝ) := by ring
        _ ≤ η := (div_le_iff₀ hNpos).mpr hlin
    have hRpow := hrX.trans (Real.rpow_le_rpow_of_exponent_le hXone (by norm_num : (1/100:ℝ) ≤ 1/20))
    have hlower := horizontal_zero_alpha_bound β r v a l (by exact_mod_cast hr.pos)
      (by positivity) hva
    push_cast at hlower
    rw [hk, Int.cast_zero, zero_mul, zero_add, ← mul_assoc]
    calc
      η * X ^ (-(1/20 : ℝ)) ≤ η / (r : ℝ) := inverse_rpow_bound hXpos hη.le hrpos hRpow
      _ ≤ (1-η) / (r : ℝ) := div_le_div_of_nonneg_right (by linarith) hrpos.le
      _ = 1 / (r : ℝ) - η / (r : ℝ) := sub_div _ _ _
      _ ≤ 1 / (r : ℝ) - |(l : ℝ)| * v * |β - (a : ℝ)/r| := by linarith
      _ ≤ torusNorm ((v : ℝ)*l*β) := hlower
  · let R := |(k : ℝ)| * (v : ℝ) * (r : ℝ)^2
    have hR : 0 < R := by dsimp [R]; positivity
    have hlin : D * (|(l : ℝ)| * |(k : ℝ)|) * (v : ℝ)^2 * (r : ℝ)^2 ≤ η * (rNext : ℝ) := by
      have hle : D * (|(l : ℝ)| * |(k : ℝ)|) * (v : ℝ)^2 * (r : ℝ)^2 ≤
          D * W^2 * (v : ℝ)^2 * (r : ℝ)^2 := by
        rw [pow_two W]
        gcongr
      exact hle.trans hmass
    have herr : |(l : ℝ)| * v * |β - (a : ℝ)/r| ≤ η / R := by
      apply (le_div_iff₀ hR).mpr
      calc
        (|(l : ℝ)| * v * |β - (a : ℝ)/r|) * R =
            (|(l : ℝ)| * |(k : ℝ)| * (v : ℝ)^2 * (r : ℝ)^2) * |β - (a : ℝ)/r| := by dsimp [R]; ring
        _ ≤ (|(l : ℝ)| * |(k : ℝ)| * (v : ℝ)^2 * (r : ℝ)^2) * (D / (rNext : ℝ)) := by gcongr
        _ = (D * (|(l : ℝ)| * |(k : ℝ)|) * (v : ℝ)^2 * (r : ℝ)^2) / (rNext : ℝ) := by ring
        _ ≤ η := (div_le_iff₀ hNpos).mpr hlin
    have hRpow : R ≤ X^(1/20 : ℝ) := by
      calc
        R ≤ X ^ (1/1000:ℝ) * X ^ (1/5000:ℝ) * (X ^ (1/100:ℝ))^2 := by dsimp [R]; gcongr; exact hkW.trans hW
        _ = X ^ (53/2500:ℝ) := by
          rw [← Real.rpow_mul_natCast hXpos.le, ← Real.rpow_add hXpos, ← Real.rpow_add hXpos]
          congr 1
          norm_num
        _ ≤ X ^ (1/20:ℝ) := Real.rpow_le_rpow_of_exponent_le hXone (by norm_num)
    have hlower := horizontal_nonzero_alpha_bound α β b r v a k l hr.pos hv hk hbad
    push_cast at hlower
    calc
      η * X ^ (-(1/20 : ℝ)) ≤ η / R := inverse_rpow_bound hXpos hη.le hR hRpow
      _ ≤ (b-η) / R := div_le_div_of_nonneg_right (by linarith) hR.le
      _ = b / R - η / R := sub_div _ _ _
      _ ≤ b / R - |(l : ℝ)| * v * |β - (a : ℝ)/r| := by linarith
      _ ≤ torusNorm ((v : ℝ)*(k*α+l*β)) := hlower

/-- The bound specialized to a fixed horizontal coordinate. Its leading
constant can be chosen independently of that coordinate. -/
theorem horizontal_diophantine_bound (α β : ℝ) (hα : BadlyApproximable α) :
    ∃ η : ℝ, 0 < η ∧ ∀ (c C D L : ℝ), 0 < c → 0 < C → 0 < D → 0 < L →
    ∀ᶠ X : ℝ in atTop, ∀ a r rNext : ℕ, r.Prime → 0 < a → a < r →
      c * denominatorScale r ≤ (rNext : ℝ) → (rNext : ℝ) ≤ C * denominatorScale r →
      |β - (a : ℝ)/r| ≤ D / (rNext : ℝ) →
      (r : ℝ) ≤ X ^ (1/100 : ℝ) → X ^ (1/100 : ℝ) < (rNext : ℝ) →
      ∀ (v : ℕ) (k l : ℤ), 0 < v → (v : ℝ) ≤ X ^ (1/5000 : ℝ) → ¬ r ∣ v →
      0 < max |(k : ℝ)| |(l : ℝ)| → max |(k : ℝ)| |(l : ℝ)| ≤ Real.log X ^ L →
      η * X ^ (-(1/20 : ℝ)) ≤ torusNorm ((v : ℝ) * (k*α+l*β)) := by
  obtain ⟨η, hη, hBound⟩ := horizontal_diophantine_bound_uniform_in_beta α hα
  exact ⟨η, hη, fun c C D L hc hC hD hL => (hBound c C D L hc hC hD hL).mono fun _ h => h β⟩

/-- The index in the proof of Lemma 6.1 exists once the scale reaches the
first denominator. Strict increase forces the denominators to be unbounded. -/
theorem exists_bracketing_denominators (r : ℕ → ℕ) (hr : StrictMono r) (Y : ℝ)
    (hY : (r 0 : ℝ) ≤ Y) : ∃ j : ℕ, (r j : ℝ) ≤ Y ∧ Y < (r (j+1) : ℝ) := by
  classical
  have hex : ∃ j : ℕ, Y < (r j : ℝ) := by
    obtain ⟨j, hj⟩ := exists_nat_gt Y
    exact ⟨j, hj.trans_le (by exact_mod_cast (hr.le_apply : j ≤ r j))⟩
  let m := Nat.find hex
  have hm : Y < (r m : ℝ) := Nat.find_spec hex
  have hmpos : 0 < m := by
    by_contra! hn
    have hmzero : m = 0 := by omega
    rw [hmzero] at hm
    exact (not_lt_of_ge hY) hm
  let j := m - 1
  have hj : j + 1 = m := by dsimp [j]; omega
  have hjm : j < m := by omega
  exact ⟨j, le_of_not_gt (Nat.find_min hex hjm), by rwa [hj]⟩

/-- The three conclusions of Lemma 6.1 for any given admissible
sequence of prime approximants to β. -/
theorem heisenberg_horizontal_for_denominators (α β : ℝ) (hα : BadlyApproximable α)
    {r : ℕ → ℕ} (hβ : AdmissibleBetaDenominators β r) :
    (∀ᶠ X : ℝ in atTop,
      ∃ j : ℕ, (r j : ℝ) ≤ X^(1/100 : ℝ) ∧ X^(1/100 : ℝ) < (r (j+1) : ℝ)) ∧
    (∀ L K : ℝ, 0 < L → 0 < K → ∀ᶠ X : ℝ in atTop,
      ∀ j : ℕ, (r j : ℝ) ≤ X^(1/100 : ℝ) → X^(1/100 : ℝ) < (r (j+1) : ℝ) →
        K * Real.log X ^ L < (r j : ℝ)) ∧
    (∃ η : ℝ, 0 < η ∧ ∀ L : ℝ, 0 < L → ∀ᶠ X : ℝ in atTop,
      ∀ j : ℕ, (r j : ℝ) ≤ X^(1/100 : ℝ) → X^(1/100 : ℝ) < (r (j+1) : ℝ) →
      ∀ (v : ℕ) (k l : ℤ), 0 < v → (v : ℝ) ≤ X^(1/5000 : ℝ) → ¬ r j ∣ v →
      0 < max |(k : ℝ)| |(l : ℝ)| → max |(k : ℝ)| |(l : ℝ)| ≤ Real.log X ^ L →
      η * X^(-(1/20 : ℝ)) ≤ torusNorm ((v : ℝ)*(k*α+l*β))) := by
  obtain ⟨hr, a, _, hprime, c, C, D, hc, hC, hD, happ⟩ := hβ
  refine ⟨?_, ?_, ?_⟩
  · have hlarge := (tendsto_rpow_atTop (show 0 < (1/100 : ℝ) by norm_num)).eventually
      (eventually_ge_atTop (r 0 : ℝ))
    filter_upwards [hlarge] with X hX
    exact exists_bracketing_denominators r hr _ hX
  · intro L K hL hK
    filter_upwards [horizontal_scale_bounds c C L K hc hC hL hK] with X hX
    intro j _ hj₁
    obtain ⟨hlo, hhi, _, _⟩ := happ j
    exact (hX (r j) (r (j+1)) (hprime j).1.pos hlo hhi hj₁).1
  · obtain ⟨η, hη, hmain⟩ := horizontal_diophantine_bound α β hα
    refine ⟨η, hη, fun L hL => ?_⟩
    filter_upwards [hmain c C D L hc hC hD hL] with X hX
    intro j hj₀ hj₁ v k l hv hvX hvr hfreq₀ hfreq₁
    obtain ⟨hlo, hhi, ha₀, ha₁⟩ := happ j
    obtain ⟨hp, ha, har⟩ := hprime j
    exact hX (a j) (r j) (r (j+1)) hp ha har hlo hhi
      (by rwa [abs_of_pos ha₀]) hj₀ hj₁ v k l hv hvX hvr hfreq₀ hfreq₁

/-- Lemma 6.1 under the manuscript's badly approximable and admissible-beta
hypotheses. The first conjunct supplies a bracketing index. The second is
`e:infcondition`, expressed by exceeding every constant multiple. The third
is the uniform bound for mixed horizontal frequencies. -/
theorem heisenberg_horizontal (α β : ℝ) (hα : BadlyApproximable α) (hβ : AdmissibleBeta β) :
    ∃ r : ℕ → ℕ, StrictMono r ∧ (∀ᶠ X : ℝ in atTop,
      ∃ j : ℕ, (r j : ℝ) ≤ X^(1/100 : ℝ) ∧ X^(1/100 : ℝ) < (r (j+1) : ℝ)) ∧
    (∀ L K : ℝ, 0 < L → 0 < K → ∀ᶠ X : ℝ in atTop,
      ∀ j : ℕ, (r j : ℝ) ≤ X^(1/100 : ℝ) → X^(1/100 : ℝ) < (r (j+1) : ℝ) →
        K * Real.log X ^ L < (r j : ℝ)) ∧
    (∃ η : ℝ, 0 < η ∧ ∀ L : ℝ, 0 < L → ∀ᶠ X : ℝ in atTop,
      ∀ j : ℕ, (r j : ℝ) ≤ X^(1/100 : ℝ) → X^(1/100 : ℝ) < (r (j+1) : ℝ) →
      ∀ (v : ℕ) (k l : ℤ), 0 < v → (v : ℝ) ≤ X^(1/5000 : ℝ) → ¬ r j ∣ v →
      0 < max |(k : ℝ)| |(l : ℝ)| → max |(k : ℝ)| |(l : ℝ)| ≤ Real.log X ^ L →
      η * X^(-(1/20 : ℝ)) ≤ torusNorm ((v : ℝ)*(k*α+l*β))) := by
  obtain ⟨_, _, r, hr⟩ := (admissibleBeta_iff_exists_denominators β).mp hβ
  exact ⟨r, hr.1, heisenberg_horizontal_for_denominators α β hα hr⟩

/-- The explicit choice of α in the abstract is badly approximable.
The integer norm `3m²-z²` of the nearest-integer error is nonzero. -/
theorem badlyApproximable_sqrt_three : BadlyApproximable (Real.sqrt 3) := by
  refine ⟨1/5, by norm_num, fun m hm => ?_⟩
  let x : ℝ := (m : ℝ) * Real.sqrt 3
  let z : ℤ := round x
  change (1/5 : ℝ) ≤ (m : ℝ) * torusNorm x
  rw [torusNorm_eq]
  change (1/5 : ℝ) ≤ (m : ℝ) * |x - z|
  have hmone : 1 ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : 0 < (m : ℝ) := by positivity
  have hsnon := Real.sqrt_nonneg 3
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hsone : 1 ≤ Real.sqrt 3 := by nlinarith
  have hstwo : Real.sqrt 3 ≤ 2 := by nlinarith
  have hxlow : (m : ℝ) ≤ x := by
    dsimp [x]
    simpa using mul_le_mul_of_nonneg_left hsone hmpos.le
  have hxhi : x ≤ (m : ℝ)*2 := mul_le_mul_of_nonneg_left hstwo hmpos.le
  have hz : |x - z| ≤ (1/2 : ℝ) := abs_sub_round x
  have habs := abs_le.mp hz
  have hplus : 0 < x + z := by linarith [habs.2]
  have hsum : |x + z| ≤ 5*(m : ℝ) := by
    rw [abs_of_pos hplus]
    linarith [habs.1]
  have hIrr : Irrational (Real.sqrt 3) := by simpa using Nat.prime_three.irrational_sqrt
  have hne : x - z ≠ 0 := by
    intro h
    have he : Real.sqrt 3 = (z : ℝ)/(m : ℝ) :=
      (eq_div_iff hmpos.ne').mpr (by dsimp [x] at h; linarith [mul_comm (m : ℝ) (Real.sqrt 3)])
    exact (irrational_iff_ne_rational _).mp hIrr z (m : ℤ) (by simpa using he)
  have hmult : (x - z)*(x + z) = (3 : ℝ)*(m : ℝ)^2 - (z : ℝ)^2 := by
    calc
      (x - z)*(x + z) = x^2 - (z : ℝ)^2 := by ring
      _ = (3 : ℝ)*(m : ℝ)^2 - (z : ℝ)^2 := by dsimp [x]; rw [mul_pow, hs]; ring
  have hint : 3*(m : ℤ)^2 - z^2 ≠ 0 := by
    intro he
    have heR : (3 : ℝ)*(m : ℝ)^2 - (z : ℝ)^2 = 0 := by exact_mod_cast he
    exact (mul_ne_zero hne hplus.ne') (hmult.trans heR)
  have hnat : (1 : ℝ) ≤ |((3*(m : ℤ)^2 - z^2 : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs hint
  push_cast at hnat
  rw [← hmult, abs_mul] at hnat
  have hb := hnat.trans (mul_le_mul_of_nonneg_left hsum (abs_nonneg (x - z)))
  linarith

end NilBohr
