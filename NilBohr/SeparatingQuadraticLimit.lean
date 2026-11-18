import NilBohr.SeparatingScales
import NilBohr.TwistedOrbit
import NilBohr.SeparatingFourier

/-! Quadratic equidistribution on the denominator multiples in Appendix A. -/

open Filter Polynomial MeasureTheory AddCircle
open scoped BigOperators Topology ComplexConjugate NNReal

namespace NilBohr

private noncomputable abbrev prefixMean (H : ℕ) (f : ℕ → ℂ) : ℂ :=
  prefixAverage f H

private theorem prefixMean_eq (H : ℕ) (f : ℕ → ℂ) :
    prefixMean H f = (∑ n ∈ Finset.range H, f n) / (H : ℂ) := by
  simp [prefixMean, prefixAverage, Complex.real_smul, div_eq_mul_inv, mul_comm]

private theorem norm_prefixMean_le {H : ℕ} {f : ℕ → ℂ} {R : ℝ}
    (hR : 0 ≤ R) (hf : ∀ n ∈ Finset.range H, ‖f n‖ ≤ R) :
    ‖prefixMean H f‖ ≤ R := by
  by_cases h : H = 0
  · simpa [prefixMean_eq, h] using hR
  have hH : 0 < (H : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero h)
  rw [prefixMean_eq, norm_div, Complex.norm_natCast, div_le_iff₀ hH]
  exact (norm_sum_le _ _).trans ((Finset.sum_le_sum hf).trans_eq (by simp [mul_comm]))

private theorem prefixMean_sub (H : ℕ) (f g : ℕ → ℂ) :
    prefixMean H (fun n => f n - g n) = prefixMean H f - prefixMean H g := by
  simp only [prefixMean_eq, Finset.sum_sub_distrib, sub_div]

private theorem prefixMean_const_mul (H : ℕ) (c : ℂ) (f : ℕ → ℂ) :
    prefixMean H (fun n => c * f n) = c * prefixMean H f := by
  simp only [prefixMean_eq, ← Finset.mul_sum, mul_div_assoc]

private theorem prefixMean_shift_eq (H : ℕ) (f : ℕ → ℂ) (a : ℕ) :
    prefixMean H (fun n => f (n+(a+1))) -
      prefixMean H (fun n => f (n+a)) = (f (H+a) - f a) / (H : ℂ) := by
  rw [← prefixMean_sub, prefixMean_eq]
  congr 1
  calc
    _ = ∑ n ∈ Finset.range H, (f ((n+1)+a) - f (n+a)) := by
      apply Finset.sum_congr rfl
      intro n _
      rw [show n+(a+1) = (n+1)+a by omega]
    _ = _ := by simpa only [Nat.zero_add] using Finset.sum_range_sub (fun n => f (n+a)) H

private theorem norm_prefixMean_shift_sub_le (H : ℕ) (f : ℕ → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (a : ℕ) :
    ‖prefixMean H (fun n => f (n+a)) - prefixMean H f‖ ≤ (2 : ℝ)*a/H := by
  induction a with
  | zero => simp
  | succ a ih =>
    let old := prefixMean H (fun n => f (n+a))
    have hstep : ‖prefixMean H (fun n => f (n+(a+1))) - old‖ ≤ 2/(H : ℝ) := by
      rw [show old = prefixMean H (fun n => f (n+a)) from rfl, prefixMean_shift_eq,
        norm_div, Complex.norm_natCast]
      exact div_le_div_of_nonneg_right
        ((norm_sub_le _ _).trans (by linarith [hf (H+a), hf a])) (Nat.cast_nonneg H)
    calc
      _ = ‖(prefixMean H (fun n => f (n+(a+1))) - old) + (old - prefixMean H f)‖ := by
        rw [sub_add_sub_cancel]
      _ ≤ ‖prefixMean H (fun n => f (n+(a+1))) - old‖ + ‖old - prefixMean H f‖ :=
        norm_add_le _ _
      _ ≤ 2/(H : ℝ) + 2*a/H := add_le_add hstep ih
      _ = _ := by push_cast; ring

private theorem prefixMean_swap (H K : ℕ) (f : ℕ → ℕ → ℂ) :
    prefixMean H (fun n => prefixMean K (f n)) =
      prefixMean K (fun a => prefixMean H (fun n => f n a)) := by
  simp only [prefixMean_eq, ← Finset.sum_div]
  rw [Finset.sum_comm]
  ring

private theorem norm_prefixMean_sq_le (H : ℕ) (f : ℕ → ℂ) :
    ‖prefixMean H f‖^2 ≤ (∑ n ∈ Finset.range H, ‖f n‖^2)/(H : ℝ) := by
  rw [prefixMean_eq, norm_div, Complex.norm_natCast]
  have hsum := div_le_div_of_nonneg_right (norm_sum_le (Finset.range H) f) (Nat.cast_nonneg H)
  have hsq := pow_le_pow_left₀ (by positivity) hsum 2
  exact hsq.trans (by simpa only [Finset.card_range] using
    (sum_div_card_sq_le_sum_sq_div_card (s := Finset.range H) (f := fun n => ‖f n‖)))

private theorem ofReal_prefixMean_norm_sq (H K : ℕ) (f : ℕ → ℕ → ℂ) :
    Complex.ofReal ((∑ n ∈ Finset.range H, ‖prefixMean K (f n)‖^2)/(H : ℝ)) =
      (∑ a ∈ Finset.range K, ∑ b ∈ Finset.range K,
        prefixMean H (fun n => f n a * conj (f n b))) / (K : ℂ)^2 := by
  simp only [Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_sum, Complex.sq_norm,
    ← Complex.mul_conj]
  simp only [prefixMean_eq, map_div₀, map_natCast, div_mul_div_comm, ← pow_two,
    map_sum, Finset.sum_mul_sum, ← Finset.sum_div, div_div]
  rw [mul_comm ((K : ℂ)^2) (H : ℂ)]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]

/-- A fixed-shift van der Corput criterion for a family of finite averages.
The length varies with the family index, and each fixed pair of different
shifts is tested on that length. -/
theorem prefixAverage_tendsto_zero_of_shift_correlations
    (H : ℕ → ℕ) (f : ℕ → ℕ → ℂ) (hH : Tendsto H atTop atTop)
    (hf : ∀ j n, ‖f j n‖ = 1)
    (hCorr : ∀ a b : ℕ, a ≠ b →
      Tendsto (fun j => prefixAverage (fun n => f j (n+a) * conj (f j (n+b))) (H j))
        atTop (𝓝 0)) :
    Tendsto (fun j => prefixAverage (f j) (H j)) atTop (𝓝 0) := by
  change Tendsto (fun j => prefixMean (H j) (f j)) atTop (𝓝 0)
  classical
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨K, hKsmall⟩ := exists_nat_one_div_lt (show 0 < (ε/2)^2 by positivity)
  let L := K+1
  have hLsmall : 1/(L : ℝ) < (ε/2)^2 := by simpa [L] using hKsmall
  have hLpos : 0 < (L : ℝ) := by positivity
  have hLposC : (L : ℂ) ≠ 0 := by exact_mod_cast (show L ≠ 0 by dsimp [L]; omega)
  have hHpos : ∀ᶠ j in atTop, 0 < H j := hH.eventually (eventually_gt_atTop 0)
  let g (j n : ℕ) := prefixMean L (fun a => f j (n+a))
  let C (j a b : ℕ) := prefixMean (H j) (fun n => f j (n+a) * conj (f j (n+b)))
  have hC (a b : ℕ) :
      Tendsto (fun j => C j a b) atTop (𝓝 (if a = b then (1 : ℂ) else 0)) := by
    by_cases hab : a = b
    · subst b
      simp only [if_pos rfl]
      apply tendsto_const_nhds.congr'
      filter_upwards [hHpos] with j hj
      have hHJ : (H j : ℂ) ≠ 0 := by exact_mod_cast hj.ne'
      simp [C, prefixMean_eq, Complex.mul_conj, ← Complex.sq_norm, hf, hHJ]
    · simp only [if_neg hab]
      exact hCorr a b hab
  have hSqComplex : Tendsto (fun j =>
      Complex.ofReal ((∑ n ∈ Finset.range (H j), ‖g j n‖^2)/(H j : ℝ))) atTop
      (𝓝 ((1/(L : ℝ) : ℝ) : ℂ)) := by
    have h := (tendsto_finset_sum (Finset.range L) (fun a _ =>
      tendsto_finset_sum (Finset.range L) (fun b _ => hC a b))).div_const ((L : ℂ)^2)
    have heq (a : ℕ) (ha : a ∈ Finset.range L) :
        (∑ b ∈ Finset.range L, if a = b then (1 : ℂ) else 0) = 1 := by
      simp [eq_comm, ha]
    have hdiag :
        (∑ a ∈ Finset.range L, ∑ b ∈ Finset.range L, if a = b then (1 : ℂ) else 0) = L := by
      rw [Finset.sum_congr rfl heq]
      simp
    rw [hdiag, show (L : ℂ)/(L : ℂ)^2 = ((1/(L : ℝ) : ℝ) : ℂ) by
      push_cast; field_simp; ring] at h
    convert h using 1
    ext j
    exact ofReal_prefixMean_norm_sq (H j) L (fun n a => f j (n+a))
  have hSq : Tendsto (fun j => (∑ n ∈ Finset.range (H j), ‖g j n‖^2)/(H j : ℝ))
      atTop (𝓝 (1/(L : ℝ))) := by
    simpa only [Function.comp_apply, Complex.ofReal_re] using
      (Complex.continuous_re.tendsto ((1/(L : ℝ) : ℝ) : ℂ)).comp hSqComplex
  have hShift : Tendsto (fun j => (2 : ℝ)*L/H j) atTop (𝓝 0) := by
    have he := (tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.comp hH : Tendsto (fun j => (H j : ℝ)) atTop atTop)).const_mul
        ((2 : ℝ)*L)
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using he
  filter_upwards [hSq.eventually_lt_const hLsmall, hShift.eventually_lt_const (show 0 < ε/2 by positivity)]
    with j hSqj hShiftj
  have hSmall : ‖prefixMean (H j) (g j)‖ < ε/2 := by
    have hs := (norm_prefixMean_sq_le (H j) (g j)).trans_lt hSqj
    nlinarith only [hs, norm_nonneg (prefixMean (H j) (g j)), hε]
  have hErr : ‖prefixMean (H j) (g j) - prefixMean (H j) (f j)‖ ≤ (2 : ℝ)*L/H j := by
    rw [show prefixMean (H j) (g j) = prefixMean L
        (fun a => prefixMean (H j) (fun n => f j (n+a))) from prefixMean_swap _ _ _]
    have hc : prefixMean L (fun _ => prefixMean (H j) (f j)) =
        prefixMean (H j) (f j) := by simp [prefixMean_eq, hLposC]
    rw [← hc, ← prefixMean_sub]
    apply norm_prefixMean_le (by positivity)
    intro a ha
    have hal : (a : ℝ) ≤ (L : ℝ) := by exact_mod_cast (Finset.mem_range.mp ha).le
    exact (norm_prefixMean_shift_sub_le _ _ (fun n => (hf _ n).le) a).trans
      (div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg _))
  rw [dist_zero_right]
  calc
    ‖prefixMean (H j) (f j)‖ =
        ‖(prefixMean (H j) (f j) - prefixMean (H j) (g j)) +
          prefixMean (H j) (g j)‖ := by rw [sub_add_cancel]
    _ ≤ ‖prefixMean (H j) (f j) - prefixMean (H j) (g j)‖ +
        ‖prefixMean (H j) (g j)‖ := norm_add_le _ _
    _ < ε := by
      rw [norm_sub_rev]
      linarith only [hErr, hShiftj, hSmall]

/-- On the unit circle the additive character has distance at least four
times the torus distance from the trivial character. -/
theorem four_mul_torusNorm_le_norm_phase_sub_one (t : ℝ) :
    4*torusNorm t ≤ ‖phase t-1‖ := by
  rw [torusNorm_eq]
  have ht : phase t = phase (t-(round t : ℝ)) := by
    apply phase_eq_of_sub_int
    exact ⟨round t, by ring⟩
  rw [ht]
  exact phaseExponential_sub_one_lower _ (abs_sub_round t)

/-- Cancellation of the geometric sum at an arbitrary real frequency,
expressed without division by the distance of the frequency to an integer. -/
theorem norm_prefixAverage_linear_mul_torusNorm_le (H : ℕ) (θ c : ℝ) :
    ‖prefixAverage (fun n => phase (θ*(n : ℝ)+c)) H‖ *
      ((H : ℝ)*torusNorm θ) ≤ 1 := by
  change ‖prefixMean H (fun n => phase (θ*(n : ℝ)+c))‖ * ((H : ℝ)*torusNorm θ) ≤ 1
  let f (n : ℕ) := phase (θ*(n : ℝ)+c)
  have hf (n : ℕ) : f n*phase θ = f (n+1) := by
    dsimp [f]
    rw [← phase_add]
    push_cast
    congr 1
    ring
  have htel : ((∑ n ∈ Finset.range H, f n)*(phase θ-1)) = f H-f 0 := by
    simp only [Finset.sum_mul, mul_sub, mul_one, hf]
    simpa only [Finset.sum_sub_distrib] using Finset.sum_range_sub f H
  have hb : ‖∑ n ∈ Finset.range H, f n‖ * (4*torusNorm θ) ≤ 2 := by
    calc
      _ ≤ ‖∑ n ∈ Finset.range H, f n‖ * ‖phase θ-1‖ :=
        mul_le_mul_of_nonneg_left (four_mul_torusNorm_le_norm_phase_sub_one θ) (norm_nonneg _)
      _ = ‖f H-f 0‖ := by rw [← norm_mul, htel]
      _ ≤ _ := by simpa only [f, norm_phase, show (1 : ℝ)+1=2 by norm_num] using norm_sub_le (f H) (f 0)
  by_cases hH : H = 0
  · simp [hH]
  have hH' : 0 < (H : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hH)
  change ‖prefixMean H f‖ * _ ≤ 1
  rw [prefixMean_eq, norm_div, Complex.norm_natCast, ← mul_assoc, div_mul_cancel₀ _ hH'.ne']
  nlinarith only [hb]

private theorem separatingQuadratic_eval_multiple (α : ℝ) (a r q : ℕ) (hr : 0 < r)
    (t : ℝ) :
    (separatingQuadratic α (a : ℤ) (r : ℤ) q).eval ((r : ℝ)*t) =
      -α * (a : ℝ)/2 * ((q : ℝ)^2 * (r : ℝ)*t^2 + (q : ℝ)*t) := by
  have hr' : (r : ℝ) ≠ 0 := (Nat.cast_pos.mpr hr).ne'
  simp only [separatingQuadratic, eval_mul, eval_C, eval_add, eval_pow, eval_X, Int.cast_natCast]
  field_simp
  ring

private theorem fourier_coe_eq_quadratic_phase (k : ℤ) (x : ℝ) :
    fourier (T := 1) k (x : Circle) = phase ((k : ℝ)*x) := by
  simp only [fourier_coe_apply, Complex.ofReal_one, div_one, phase,
    Complex.ofReal_mul, Complex.ofReal_intCast]
  congr 1
  ring

/-- Equidistribution on the denominator multiples only needs the ratio
of the integer quadratic coefficient to the number of samples to go to
zero. Applying van der Corput with fixed shifts gives this conclusion
without a restriction on how quickly the sample length tends to infinity. -/
theorem separatingQuadratic_modes_tendsto_zero (α : ℝ) (hα : BadlyApproximable α)
    (a r q H : ℕ → ℕ) (hH : Tendsto H atTop atTop)
    (hpos : ∀ᶠ j in atTop, 0 < a j ∧ 0 < r j ∧ 0 < q j)
    (hSize : Tendsto (fun j => ((a j : ℝ)*(q j : ℝ)^2*(r j : ℝ))/(H j : ℝ))
      atTop (𝓝 0)) (k : ℤ) (hk : k ≠ 0) :
    Tendsto (fun j =>
      (∑ n ∈ Finset.range (H j),
        fourier (T := 1) k
          (((separatingQuadratic α (a j : ℤ) (r j : ℤ) (q j)).eval
            ((r j : ℝ)*((n : ℝ)+1)) : ℝ) : Circle)) / (H j : ℂ)) atTop (𝓝 0) := by
  obtain ⟨c, hc, hbad⟩ := hα
  let Q (j : ℕ) := separatingQuadratic α (a j : ℤ) (r j : ℤ) (q j)
  let θ (j n : ℕ) := (k : ℝ) * (Q j).eval ((r j : ℝ)*((n : ℝ)+1))
  have hAvg (j : ℕ) : (∑ n ∈ Finset.range (H j),
        fourier (T := 1) k (((Q j).eval ((r j : ℝ)*((n : ℝ)+1)) : ℝ) : Circle))
        / (H j : ℂ) = prefixMean (H j) (fun n => phase (θ j n)) := by
    simp only [prefixMean_eq, fourier_coe_eq_quadratic_phase, θ]
  simp_rw [show ∀ j : ℕ, separatingQuadratic α (a j : ℤ) (r j : ℤ) (q j) = Q j from fun _ => rfl,
    hAvg]
  apply prefixAverage_tendsto_zero_of_shift_correlations H (fun j n => phase (θ j n)) hH
  · exact fun _ _ => norm_phase _
  intro v w hvw
  let m (j : ℕ) : ℤ := -k * (a j : ℤ)*(q j : ℤ)^2*(r j : ℤ) * ((v : ℤ)-w)
  let C := |(k : ℝ)| * |(v : ℝ)-(w : ℝ)| / c
  have hGrow := hSize.const_mul C
  rw [mul_zero] at hGrow
  refine squeeze_zero_norm' ?_ hGrow
  filter_upwards [hpos, hH.eventually (eventually_gt_atTop 0)] with j ⟨ha, hr, hq⟩ hHj
  have hm : m j ≠ 0 := by
    dsimp [m]
    have hvw' : (v : ℤ)-(w : ℤ) ≠ 0 := by exact sub_ne_zero.mpr (by exact_mod_cast hvw)
    have ha' : (a j : ℤ) ≠ 0 := by exact_mod_cast ha.ne'
    have hr' : (r j : ℤ) ≠ 0 := by exact_mod_cast hr.ne'
    have hq' : (q j : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hk) ha')
      (pow_ne_zero _ hq')) hr') hvw'
  have hθ (n : ℕ) : θ j (n+v)-θ j (n+w) =
      ((m j : ℝ)*α)*(n : ℝ) + (θ j v-θ j w) := by
    simp only [θ, Q, m, separatingQuadratic_eval_multiple α _ _ _ hr, Nat.cast_add,
      Int.cast_mul, Int.cast_neg, Int.cast_natCast, Int.cast_pow, Int.cast_sub]
    ring
  let f (n : ℕ) := phase (((m j : ℝ)*α)*(n : ℝ) + (θ j v-θ j w))
  have hf (n : ℕ) : phase (θ j (n+v)) * conj (phase (θ j (n+w))) = f n := by
    change phaseExponential _ * conj (phaseExponential _) = phaseExponential _
    rw [← phaseExponential_sub, hθ]
  simp_rw [hf]
  have hd := badlyApproximable_bound_int hbad (m j) hm
  have hM := norm_prefixAverage_linear_mul_torusNorm_le (H j) ((m j : ℝ)*α) (θ j v-θ j w)
  have hmabs : |(m j : ℝ)| =
      |(k : ℝ)| * (a j : ℝ) * (q j : ℝ)^2 * (r j : ℝ) * |(v : ℝ)-(w : ℝ)| := by
    simp only [m, Int.cast_mul, Int.cast_neg, Int.cast_natCast, Int.cast_pow, Int.cast_sub,
      abs_mul, abs_neg, abs_of_nonneg (Nat.cast_nonneg (a j) : 0 ≤ (a j : ℝ)),
      abs_of_nonneg (Nat.cast_nonneg (r j) : 0 ≤ (r j : ℝ)), abs_of_nonneg (sq_nonneg (q j : ℝ))]
  have hHj' : 0 < (H j : ℝ) := Nat.cast_pos.mpr hHj
  have hFinal : ‖prefixMean (H j) f‖ * ((H j : ℝ)*c) ≤ |(m j : ℝ)| := by
    calc
      _ ≤ ‖prefixMean (H j) f‖ * ((H j : ℝ)*(|(m j : ℝ)| * torusNorm ((m j : ℝ)*α))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hd hHj'.le) (norm_nonneg _)
      _ = (‖prefixMean (H j) f‖ * ((H j : ℝ)*torusNorm ((m j : ℝ)*α))) * |(m j : ℝ)| := by ring
      _ ≤ 1 * |(m j : ℝ)| := mul_le_mul_of_nonneg_right hM (abs_nonneg _)
      _ = _ := one_mul _
  calc
    _ ≤ |(m j : ℝ)| / ((H j : ℝ)*c) := (le_div_iff₀ (mul_pos hHj' hc)).mpr hFinal
    _ = C * (((a j : ℝ)*(q j : ℝ)^2*(r j : ℝ))/(H j : ℝ)) := by
      rw [hmabs]
      dsimp only [C]
      ring

/-- The nonzero Fourier coefficient is detected by quadratic phases on
the denominator multiples. With the manuscript's scale growth this yields
the global lower bound of Proposition A.1. -/
theorem separatingGlobalPhase_lower_bound (α β : ℝ) (hα : BadlyApproximable α)
    (F : C(Circle, ℂ)) {κ : ℝ≥0} (hLip : LipschitzWith κ F)
    (hF : ∃ x y : Circle, F x ≠ F y)
    (a r q H : ℕ → ℕ) (hH : Tendsto H atTop atTop)
    (hpos : ∀ᶠ j in atTop, 0 < a j ∧ 0 < r j ∧ 0 < q j)
    (hbelow : ∀ᶠ j in atTop, 0 ≤ β - (a j : ℝ)/(r j : ℝ))
    (hSize : Tendsto (fun j => ((a j : ℝ)*(q j : ℝ)^2*(r j : ℝ))/(H j : ℝ))
      atTop (𝓝 0))
    (hError : Tendsto (fun j =>
      (β-(a j : ℝ)/(r j : ℝ)) * ((q j : ℝ)*(r j * H j : ℕ))^2)
      atTop (𝓝 0)) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ j in atTop, c/(r j : ℝ) ≤
      phaseNorm 3 (positiveInterval (r j*H j)) (separatingWeight α β F (q j)) := by
  obtain ⟨h, hh, hCoeff⟩ := exists_nonzero_fourierCoeff_of_nonconstant F hF
  let Q (j : ℕ) := separatingQuadratic α (a j : ℤ) (r j : ℤ) (q j)
  let P (j : ℕ) := C (h : ℝ) * Q j
  let Xscale (j : ℕ) := (q j : ℝ)*(r j*H j : ℕ)
  let E (j : ℕ) := β-(a j : ℝ)/(r j : ℝ)
  let x (j n : ℕ) : Circle := ((Q j).eval ((r j : ℝ)*((n : ℝ)+1)) : ℝ)
  let G (j : ℕ) := separatingWeight α β F (q j)
  let u : C(Circle, ℂ) := (F - ContinuousMap.const Circle (circleMean F)) * fourier (T := 1) (-h)
  let Csum (j : ℕ) := phaseAverage (positiveInterval (H j))
    (fun t => G j ((r j : ℤ)*t)) ((P j).comp (C (r j : ℝ)*X))
  let U (j : ℕ) := prefixMean (H j) (fun n => u (x j n))
  have hU : Tendsto U atTop (𝓝 (fourierCoeff F h)) := by
    have hu := tendsto_circle_average_of_fourier H x hH
      (separatingQuadratic_modes_tendsto_zero α hα a r q H hH hpos hSize) u
    have hmean : circleMean u = fourierCoeff F h := circleMean_centered_mul_fourier F hh
    rw [hmean] at hu
    simpa only [U, prefixMean_eq] using hu
  have hSeq (j : ℕ) :
      Csum j = prefixMean (H j) (fun n =>
        G j ((r j : ℤ)*((n : ℤ)+1)) * fourier (T := 1) (-h) (x j n)) := by
    dsimp only [Csum]
    rw [phaseAverage, card_positiveInterval, sum_positiveInterval_eq_zero_prefix, prefixMean_eq]
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    simp only [x, fourier_coe_eq_quadratic_phase, Int.cast_neg, P, eval_comp,
      eval_mul, eval_C, eval_X, Int.cast_add, Int.cast_natCast, Int.cast_one, neg_mul]
  have hClose : Tendsto (fun j => Csum j-U j) atTop (𝓝 0) := by
    have he : Tendsto (fun j => ((κ : ℝ)*|α|/2) * (E j * (Xscale j)^2))
        atTop (𝓝 0) := by
      have he' := hError.const_mul ((κ : ℝ)*|α|/2)
      simpa only [mul_zero] using he'
    refine squeeze_zero_norm' ?_ he
    filter_upwards [hpos, hbelow, hH.eventually (eventually_gt_atTop 0),
      hError.eventually_lt_const (show (0 : ℝ) < 1 by norm_num)] with
      j ⟨_, hr, hq⟩ hE hHj hsmall
    have hX : 1 ≤ Xscale j := by
      dsimp [Xscale]
      have hXnat : 1 ≤ q j * (r j*H j) := Nat.succ_le_of_lt (Nat.mul_pos hq (Nat.mul_pos hr hHj))
      exact_mod_cast hXnat
    have hE' : 0 ≤ E j := hE
    have hsmall' : E j*Xscale j < 1 := by
      have hsmall'' : E j*(Xscale j)^2 < 1 := hsmall
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left
        (by nlinarith only [mul_nonneg (by linarith : 0 ≤ Xscale j) (sub_nonneg.mpr hX)]) hE') hsmall''
    rw [hSeq, show U j = prefixMean (H j) (fun n => u (x j n)) from rfl, ← prefixMean_sub]
    apply norm_prefixMean_le (by positivity)
    intro n hn
    let y : ℤ := (r j : ℤ)*((n : ℤ)+1)
    let z : ℝ := heisenbergPhase α β ((q j : ℤ)*y)
    let ξ : ℝ := (Q j).eval (y : ℝ)
    have hy : y ∈ positiveInterval (r j*H j) := by
      have hni : n < H j := Finset.mem_range.mp hn
      have hr' : (0 : ℤ) < r j := by exact_mod_cast hr
      have hj' : (n : ℤ)+1 ≤ (H j : ℤ) := by omega
      refine Finset.mem_Icc.mpr ⟨?_,?_⟩
      · have hy' : 0 < y := mul_pos hr' (by omega)
        omega
      · simpa only [y, Nat.cast_mul] using mul_le_mul_of_nonneg_left hj' hr'.le
    have hξ : x j n = (ξ : Circle) := by
      simp only [x, ξ, y, Int.cast_mul, Int.cast_natCast, Int.cast_add, Int.cast_one]
    have happrox : |z-ξ| ≤ |α| * E j * (Xscale j)^2/2 :=
      abs_heisenbergPhase_sub_separatingQuadratic_le α β (a j : ℤ) (r j : ℤ)
        (by exact_mod_cast hr.ne') hq hy (dvd_mul_right _ _) hE' le_rfl hsmall'
    have hdiff : ‖F (z : Circle)-F (ξ : Circle)‖ ≤ (κ : ℝ)*|z-ξ| := by
      have hd := hLip.dist_le_mul (z : Circle) (ξ : Circle)
      rw [dist_eq_norm, dist_eq_norm, ← AddCircle.coe_sub] at hd
      exact hd.trans (mul_le_mul_of_nonneg_left (torusNorm_le_abs _) κ.coe_nonneg)
    have hdiff' :
        G j y * fourier (T := 1) (-h) (x j n) - u (x j n) =
          (F (z : Circle)-F (ξ : Circle)) * fourier (T := 1) (-h) (x j n) := by
      simp only [u, ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.const_apply,
        G, separatingWeight, selectorWeight, z]
      rw [← sub_mul, sub_sub_sub_cancel_right, hξ]
    change ‖G j y * _ - u (x j n)‖ ≤ _
    rw [hdiff', norm_mul]
    have hFourNorm : ‖fourier (T := 1) (-h) (x j n)‖ = 1 := by
      rw [hξ, fourier_coe_eq_quadratic_phase, norm_phase]
    rw [hFourNorm, mul_one]
    exact hdiff.trans ((mul_le_mul_of_nonneg_left happrox κ.coe_nonneg).trans_eq (by ring))
  have hC : Tendsto Csum atTop (𝓝 (fourierCoeff F h)) := by
    have hmain := hClose.add hU
    simpa only [sub_add_cancel, zero_add] using hmain
  have hNorm : Tendsto (fun j => ‖Csum j‖) atTop (𝓝 ‖fourierCoeff F h‖) :=
    (continuous_norm.tendsto _).comp hC
  refine ⟨‖fourierCoeff F h‖/2, by positivity, ?_⟩
  have hη : ‖fourierCoeff F h‖/2 < ‖fourierCoeff F h‖ := by
    have hn := norm_pos_iff.mpr hCoeff
    linarith
  filter_upwards [hNorm.eventually_const_lt hη, hpos] with j hj ⟨_, hr, _⟩
  have hdeg : (P j).natDegree < 3 :=
    ((natDegree_C_mul_le _ _).trans (separatingQuadratic_natDegree_le _ _ _ _)).trans_lt (by decide)
  exact (div_le_div_of_nonneg_right hj.le (Nat.cast_nonneg _)).trans
    (residueCorrelation_le_phaseNorm (by decide) hr (G j) (P j) hdeg)

/-- A quantitative van der Corput bound allowing the number of shifts
to grow with the length. The last term accounts for the shift endpoints. -/
theorem prefixAverage_sq_le_of_uniform_shift_correlations
    {H K : ℕ} (hK : 0 < K) (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ = 1)
    {C : ℝ} (hC : 0 ≤ C)
    (hCorr : ∀ a ∈ Finset.range K, ∀ b ∈ Finset.range K, a ≠ b →
      ‖prefixAverage (fun n => f (n+a) * conj (f (n+b))) H‖ ≤ C) :
    ‖prefixAverage f H‖^2 ≤ 2/(K : ℝ) + 2*C + 8*((K : ℝ)/H)^2 := by
  classical
  let g (n : ℕ) := prefixMean K (fun a => f (n+a))
  let D (a b : ℕ) := prefixMean H (fun n => f (n+a) * conj (f (n+b)))
  have hk : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hkC : (K : ℂ) ≠ 0 := by exact_mod_cast hK.ne'
  have hrow (a : ℕ) (ha : a ∈ Finset.range K) : ‖∑ b ∈ Finset.range K, D a b‖ ≤ 1 + K*C := by
    have hterm (b : ℕ) (hb : b ∈ Finset.range K) : ‖D a b‖ ≤ (if b = a then 1 else 0) + C := by
      by_cases hab : b = a
      · subst b
        rw [if_pos rfl]
        have hDiag : ‖D a a‖ ≤ 1 := norm_prefixMean_le zero_le_one (fun n _ => by
          simp only [norm_mul, Complex.norm_conj, hf, mul_one, le_refl])
        linarith only [hDiag, hC]
      · simpa only [if_neg hab, zero_add] using hCorr a ha b hb (Ne.symm hab)
    calc
      _ ≤ ∑ b ∈ Finset.range K, ‖D a b‖ := norm_sum_le _ _
      _ ≤ ∑ b ∈ Finset.range K, ((if b = a then (1 : ℝ) else 0) + C) :=
        Finset.sum_le_sum hterm
      _ = _ := by rw [Finset.sum_add_distrib]; simp [ha, nsmul_eq_mul]
  have hMeanSq : ‖prefixMean H g‖^2 ≤ 1/(K:ℝ) + C := by
    refine (norm_prefixMean_sq_le H g).trans ?_
    let Q := (∑ n ∈ Finset.range H, ‖g n‖^2)/(H:ℝ)
    have hQ : 0 ≤ Q := by dsimp [Q]; positivity
    have hEq : (Q : ℂ) = (∑ a ∈ Finset.range K, ∑ b ∈ Finset.range K, D a b)/(K:ℂ)^2 :=
      ofReal_prefixMean_norm_sq H K (fun n a => f (n+a))
    have hSum : ‖∑ a ∈ Finset.range K, ∑ b ∈ Finset.range K, D a b‖ ≤ (K:ℝ)*(1+K*C) :=
      (norm_sum_le _ _).trans ((Finset.sum_le_sum hrow).trans_eq (by simp [nsmul_eq_mul]; ring))
    change Q ≤ _
    rw [← Complex.norm_of_nonneg hQ, hEq, norm_div, norm_pow, Complex.norm_natCast]
    calc
      _ ≤ ((K:ℝ)*(1+K*C))/(K:ℝ)^2 := div_le_div_of_nonneg_right hSum (by positivity)
      _ = _ := by field_simp [hk.ne']; ring
  have hShift : ‖prefixMean H g - prefixMean H f‖ ≤ 2*((K:ℝ)/H) := by
    rw [show prefixMean H g = prefixMean K (fun a => prefixMean H (fun n => f (n+a))) from
      prefixMean_swap _ _ _]
    have hc : prefixMean K (fun _ => prefixMean H f) = prefixMean H f := by
      simp [prefixMean_eq, hkC]
    rw [← hc, ← prefixMean_sub]
    apply norm_prefixMean_le (by positivity)
    intro a ha
    have hak : (a:ℝ) ≤ K := Nat.cast_le.mpr (Finset.mem_range.mp ha).le
    exact (norm_prefixMean_shift_sub_le H f (fun n => (hf n).le) a).trans
      ((div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hak (by norm_num))
        (Nat.cast_nonneg H)).trans_eq (by ring))
  have hTri : ‖prefixMean H f‖ ≤ ‖prefixMean H g - prefixMean H f‖ + ‖prefixMean H g‖ := by
    rw [norm_sub_rev]
    calc
      _ = ‖(prefixMean H f - prefixMean H g) + prefixMean H g‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  have hTriSq := pow_le_pow_left₀ (norm_nonneg _) hTri 2
  have hShiftSq := pow_le_pow_left₀ (norm_nonneg _) hShift 2
  change ‖prefixMean H f‖^2 ≤ _
  calc
    _ ≤ (‖prefixMean H g - prefixMean H f‖ + ‖prefixMean H g‖)^2 := hTriSq
    _ ≤ 2*‖prefixMean H g - prefixMean H f‖^2 + 2*‖prefixMean H g‖^2 := by
      nlinarith only [sq_nonneg (‖prefixMean H g-prefixMean H f‖ - ‖prefixMean H g‖)]
    _ ≤ 2*(2*((K:ℝ)/H))^2 + 2*(1/(K:ℝ)+C) := by gcongr
    _ = _ := by ring

private theorem norm_prefixMean_quadratic_shift_corr_le {α c : ℝ} (hc : 0 < c)
    (hbad : ∀ d : ℕ, 0 < d → c ≤ (d:ℝ)*torusNorm ((d:ℝ)*α))
    {H : ℕ} (hH : 0 < H) {m : ℤ} (hm : m ≠ 0) (l b : ℝ)
    {v w : ℕ} (hvw : v ≠ w) :
    let p (n : ℕ) := (m:ℝ)*α*(n:ℝ)^2/2 + l*n + b
    ‖prefixMean H (fun n => phase (p (n+v))*conj (phase (p (n+w))))‖ ≤
      |(m:ℝ)| * |(v:ℝ)-(w:ℝ)| / ((H:ℝ)*c) := by
  intro p
  let k := m*((v:ℤ)-(w:ℤ))
  have hk : k ≠ 0 := mul_ne_zero hm (sub_ne_zero.mpr (by exact_mod_cast hvw))
  let f (n : ℕ) := phase (((k:ℝ)*α)*(n:ℝ) + (p v-p w))
  have hphase (n : ℕ) : phase (p (n+v))*conj (phase (p (n+w))) = f n := by
    change phaseExponential _ * conj (phaseExponential _) = phaseExponential _
    rw [← phaseExponential_sub]
    congr 1
    dsimp [p,k]
    push_cast
    ring
  simp_rw [hphase]
  have hb := badlyApproximable_bound_int hbad k hk
  have hM := norm_prefixAverage_linear_mul_torusNorm_le H ((k:ℝ)*α) (p v-p w)
  have hH' : (0:ℝ) < H := Nat.cast_pos.mpr hH
  have hB : ‖prefixMean H f‖ * ((H:ℝ)*torusNorm ((k:ℝ)*α)) ≤ 1 := hM
  have hProd : ‖prefixMean H f‖ * ((H:ℝ)*c) ≤ |(k:ℝ)| := calc
    _ ≤ ‖prefixMean H f‖ * ((H:ℝ)*(|(k:ℝ)| * torusNorm ((k:ℝ)*α))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb hH'.le) (norm_nonneg _)
    _ = (‖prefixMean H f‖ * ((H:ℝ)*torusNorm ((k:ℝ)*α))) * |(k:ℝ)| := by ring
    _ ≤ _ := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hB (abs_nonneg _)
  have hAbs : |(k:ℝ)| = |(m:ℝ)| * |(v:ℝ)-(w:ℝ)| := by simp only [k, Int.cast_mul,
    Int.cast_sub, Int.cast_natCast, abs_mul]
  rw [← hAbs]
  exact (le_div_iff₀ (mul_pos hH' hc)).2 hProd

/-- With `floor(H^(1/3))` shifts, the quadratic Weyl estimate retains the
explicit dependence on the integer part of the leading coefficient. -/
theorem exists_quadraticWeyl_growing_shift_bound {α : ℝ} (hα : BadlyApproximable α) :
    ∃ C : ℝ, 0 < C ∧ ∀ (H : ℕ), 0 < H → ∀ (m : ℤ), m ≠ 0 → ∀ l b : ℝ,
      ‖prefixAverage (fun n => phase ((m:ℝ)*α*(n:ℝ)^2/2 + l*n + b)) H‖^2 ≤
        C*((H:ℝ)^(-(1/3 : ℝ)) + |(m:ℝ)| * (H:ℝ)^(-(2/3 : ℝ))) := by
  obtain ⟨c, hc, hbad⟩ := hα
  refine ⟨12+2/c, by positivity, ?_⟩
  intro H hH m hm l b
  let t := (H:ℝ)
  let x := t^(1/3 : ℝ)
  let K := ⌊x⌋₊
  let p (n : ℕ) := (m:ℝ)*α*(n:ℝ)^2/2 + l*n + b
  have ht₁ : 1 ≤ t := Nat.one_le_cast.mpr hH
  have ht₀ : 0 < t := zero_lt_one.trans_le ht₁
  have hx₁ : 1 ≤ x := Real.one_le_rpow ht₁ (by norm_num)
  have hK₁ : 1 ≤ K := Nat.le_floor (by simpa using hx₁)
  have hK : 0 < K := hK₁
  have hK₁' : (1:ℝ) ≤ K := by exact_mod_cast hK₁
  have hKpos : (0:ℝ) < K := zero_lt_one.trans_le hK₁'
  have hKu : (K:ℝ) ≤ x := Nat.floor_le (zero_le_one.trans hx₁)
  have hKl : x / 2 ≤ (K:ℝ) := by
    have hx := Nat.lt_floor_add_one x
    change x < (K:ℝ)+1 at hx
    linarith
  let B := |(m:ℝ)| * (K:ℝ)/(t*c)
  have hf (n : ℕ) : ‖phase (p n)‖ = 1 := norm_phase _
  have hCorr (v : ℕ) (hv : v ∈ Finset.range K) (w : ℕ) (hw : w ∈ Finset.range K)
      (hvw : v ≠ w) : ‖prefixMean H (fun n => phase (p (n+v))*conj (phase (p (n+w))))‖ ≤ B := by
    have hv' : (v:ℝ) ≤ K := Nat.cast_le.mpr (Finset.mem_range.mp hv).le
    have hw' : (w:ℝ) ≤ K := Nat.cast_le.mpr (Finset.mem_range.mp hw).le
    have hdist : |(v:ℝ)-(w:ℝ)| ≤ K := by
      rw [abs_le]
      constructor <;> linarith only [hv', hw', Nat.cast_nonneg (α := ℝ) v,
        Nat.cast_nonneg (α := ℝ) w]
    exact (norm_prefixMean_quadratic_shift_corr_le hc hbad hH hm l b hvw).trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hdist (abs_nonneg _))
        (mul_pos ht₀ hc).le)
  have hV := prefixAverage_sq_le_of_uniform_shift_correlations hK
    (fun n => phase (p n)) hf (by dsimp [B]; positivity) hCorr
  have hinv : 2/(K:ℝ) ≤ 4*t^(-(1/3:ℝ)) := calc
    _ ≤ 2/(x/2) := div_le_div_of_nonneg_left (by norm_num) (by positivity) hKl
    _ = _ := by rw [Real.rpow_neg ht₀.le]; change 2/(x/2)=4*x⁻¹; field_simp; ring
  have hRatio : (K:ℝ)/t ≤ t^(-(2/3:ℝ)) := calc
    _ ≤ x/t := div_le_div_of_nonneg_right hKu ht₀.le
    _ = t^(1/3:ℝ)/t^(1:ℝ) := by rw [Real.rpow_one]
    _ = _ := by rw [← Real.rpow_sub ht₀]; congr 1; norm_num
  have hRatio₁ : (K:ℝ)/t ≤ 1 := hRatio.trans (Real.rpow_le_one_of_one_le_of_nonpos ht₁ (by norm_num))
  have hRatio₀ : 0 ≤ (K:ℝ)/t := by positivity
  have hSq : ((K:ℝ)/t)^2 ≤ t^(-(1/3:ℝ)) := calc
    _ ≤ (K:ℝ)/t := by nlinarith only [mul_nonneg hRatio₀ (sub_nonneg.mpr hRatio₁)]
    _ ≤ t^(-(2/3:ℝ)) := hRatio
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le ht₁ (by norm_num)
  have hC : 2*B ≤ (2/c)*|(m:ℝ)| * t^(-(2/3:ℝ)) := calc
    _ = (2/c)*|(m:ℝ)| * ((K:ℝ)/t) := by dsimp only [B]; field_simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hRatio (by positivity)
  change ‖prefixAverage (fun n => phase (p n)) H‖^2 ≤ _
  apply hV.trans
  have hCoeff : 0 ≤ 2/c := by positivity
  change 2/(K:ℝ) + 2*B + 8*((K:ℝ)/t)^2 ≤ (12+2/c)*(t^(-(1/3:ℝ))+|(m:ℝ)| * t^(-(2/3:ℝ)))
  calc
    _ ≤ 4*t^(-(1/3:ℝ)) + (2/c)*|(m:ℝ)| * t^(-(2/3:ℝ)) + 8*t^(-(1/3:ℝ)) := by gcongr
    _ = 12*t^(-(1/3:ℝ)) + (2/c)*(|(m:ℝ)| * t^(-(2/3:ℝ))) := by ring
    _ ≤ (12+2/c)*t^(-(1/3:ℝ)) + (12+2/c)*(|(m:ℝ)| * t^(-(2/3:ℝ))) := by
      gcongr <;> linarith only [hCoeff]
    _ = _ := by ring

/-- The quantitative quadratic bound on the denominator multiples in
Appendix A, before taking a limit along the separating scales. -/
theorem separatingQuadratic_mode_sq_le_growing_shift {α : ℝ} (hα : BadlyApproximable α) :
    ∃ C : ℝ, 0 < C ∧ ∀ (H a r q : ℕ) (k : ℤ),
      0 < H → 0 < a → 0 < r → 0 < q → k ≠ 0 →
      ‖(∑ n ∈ Finset.range H,
        fourier (T := 1) k (((separatingQuadratic α (a:ℤ) (r:ℤ) q).eval
          ((r:ℝ)*((n:ℝ)+1)) : ℝ) : Circle))/(H:ℂ)‖^2 ≤
        C*((H:ℝ)^(-(1/3:ℝ)) + |(k:ℝ)| * (a:ℝ)*(q:ℝ)^2*(r:ℝ)*(H:ℝ)^(-(2/3:ℝ))) := by
  obtain ⟨C, hC, hW⟩ := exists_quadraticWeyl_growing_shift_bound hα
  refine ⟨C,hC,?_⟩
  intro H a r q k hH ha hr hq hk
  let m : ℤ := -k*(a:ℤ)*(q:ℤ)^2*(r:ℤ)
  let l : ℝ := -(k:ℝ)*α*(a:ℝ)*(q:ℝ)/2
  have ha' : (a:ℤ) ≠ 0 := by exact_mod_cast ha.ne'
  have hr' : (r:ℤ) ≠ 0 := by exact_mod_cast hr.ne'
  have hq' : (q:ℤ) ≠ 0 := by exact_mod_cast hq.ne'
  have hm : m ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hk) ha')
    (pow_ne_zero _ hq')) hr'
  let u := (m:ℝ)*α+l
  let v := (m:ℝ)*α/2+l
  have hEq (n : ℕ) : fourier (T := 1) k (((separatingQuadratic α (a:ℤ) (r:ℤ) q).eval
      ((r:ℝ)*((n:ℝ)+1)) : ℝ) : Circle) = phase ((m:ℝ)*α*(n:ℝ)^2/2+u*n+v) := by
    rw [fourier_coe_eq_quadratic_phase, separatingQuadratic_eval_multiple α a r q hr]
    congr 1
    dsimp only [m,l,u,v]
    push_cast
    ring
  have hAbs : |(m:ℝ)| = |(k:ℝ)| * (a:ℝ)*(q:ℝ)^2*(r:ℝ) := by
    simp only [m, Int.cast_mul, Int.cast_neg, Int.cast_natCast, Int.cast_pow, abs_mul, abs_neg,
      abs_of_nonneg (Nat.cast_nonneg (α := ℝ) a), abs_of_nonneg (sq_nonneg (q:ℝ)),
      abs_of_nonneg (Nat.cast_nonneg (α := ℝ) r)]
  rw [← hAbs]
  simp_rw [hEq]
  rw [← prefixMean_eq]
  exact hW H hH m hm u v

end NilBohr
