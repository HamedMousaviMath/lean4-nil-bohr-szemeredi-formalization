import NilBohr.External
import NilBohr.LocalPhases
import NilBohr.PointwiseSelector

/-!
# Quantitative smooth ergodic comparison

The input `PrimeLocalPhase` is the upstream estimate in Proposition 6.2,
with its analytic proof treated separately. The only quoted comparison in
this file is `TeravainenFixedFamily`. The spatial support, normalization,
logarithmic rate and passage from bounded inputs to (L^infty) inputs are
handled explicitly.
-/

open Filter MeasureTheory Polynomial
open scoped BigOperators ENNReal NNReal

namespace NilBohr

universe u

theorem parameterLength_pow_one {H d : ℕ} (hd : 0 < d) :
    parameterLength (H ^ d) 1 d = H := by
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  unfold parameterLength
  rw [Nat.cast_pow, Nat.cast_one, one_pow, div_one,
    ← Real.rpow_natCast_mul (Nat.cast_nonneg H), mul_inv_cancel₀ hd', Real.rpow_one]
  exact Nat.floor_natCast H

/-- The phase estimate in Proposition 6.2 applied at (q=1) and (N=H^d). -/
theorem phaseNorm_mangoldt_eventually_log_decay {d : ℕ} (hd : 0 < d)
    (V : ℤ → ℝ) (F : Circle → ℂ) (hp : PrimeLocalPhase d V F)
    {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ H : ℕ in atTop,
      phaseNorm (d + 1) (positiveInterval H)
          (fun n => (ArithmeticFunction.vonMangoldt (n + 1).toNat : ℂ) *
            (F (V n : Circle) - circleMean F)) ≤ C * (Real.log H) ^ (-A) := by
  obtain ⟨C, hC, N₀, h⟩ := hp A 1 1 0 hA zero_lt_one zero_lt_one
  refine ⟨C, hC, ?_⟩
  have hlog : ∀ᶠ H : ℕ in atTop, (1 : ℝ) ≤ Real.log (H : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [eventually_ge_atTop N₀, hlog] with H hHN hHl
  have hH : 1 ≤ H := by
    by_contra hn
    obtain rfl : H = 0 := by omega
    norm_num at hHl
  have hHpow : H ≤ H ^ d := by
    simpa using Nat.pow_le_pow_right hH (show 1 ≤ d by omega)
  have hlogpow : Real.log (H ^ d : ℕ) = (d : ℝ) * Real.log H := by
    rw [Nat.cast_pow, Real.log_pow]
  have hlog_ge : Real.log H ≤ Real.log (H ^ d : ℕ) := by
    rw [hlogpow]
    refine le_mul_of_one_le_left (by linarith) ?_
    exact_mod_cast (show 1 ≤ d by omega)
  have hlog_ge_one : (1 : ℝ) ≤ Real.log (H ^ d : ℕ) := hHl.trans hlog_ge
  have hpower : (Real.log (H ^ d : ℕ)) ^ (-(1 : ℝ)) ≤ 1 := by
    rw [Real.rpow_neg_one]
    exact inv_le_one_of_one_le₀ hlog_ge_one
  specialize h (H ^ d) 1 (hHN.trans hHpow) le_rfl (by simpa using hlog_ge_one)
  rw [parameterLength_pow_one hd] at h
  specialize h 1 (H : ℤ) 0 0 le_rfl (by simp [positiveInterval]) ?_
  · rw [← positiveInterval, card_positiveInterval]
    conv_rhs => rw [← mul_one (H : ℝ)]
    exact mul_le_mul_of_nonneg_left hpower (Nat.cast_nonneg _)
  have hprog : localProgression 1 (H : ℤ) 0 (1 ^ (0 : ℕ)) = positiveInterval H := by
    simp [localProgression, positiveInterval, Int.modEq_one]
  rw [hprog] at h
  have hweight : (fun y : ℤ => (lambdaModulus 1 y : ℂ) *
        (selectorWeight V F 1 y - circleMean F)) =
      fun y => (ArithmeticFunction.vonMangoldt (y + 1).toNat : ℂ) *
        (F (V y : Circle) - circleMean F) := by
    funext y
    simp [lambdaModulus, selectorWeight]
  rw [hweight] at h
  refine h.2.trans (mul_le_mul_of_nonneg_left ?_ hC.le)
  exact Real.rpow_le_rpow_of_exponent_nonpos (by linarith) hlog_ge (neg_nonpos.mpr hA.le)

/-- The finite phase supremum respects multiplication by a scalar. -/
theorem phaseNorm_const_mul_le {s : ℕ} (hs : 0 < s) (I : Finset ℤ)
    (v : ℤ → ℂ) (z : ℂ) :
    phaseNorm s I (fun n => z * v n) ≤ ‖z‖ * phaseNorm s I v := by
  unfold phaseNorm
  refine csSup_le ⟨‖phaseAverage I (fun n => z * v n) 0‖, 0, by simpa using hs, rfl⟩ ?_
  rintro x ⟨φ, hφ, rfl⟩
  have hlin : phaseAverage I (fun n => z * v n) φ =
      z * phaseAverage I v φ := by
    simp only [phaseAverage, mul_assoc, ← Finset.mul_sum, ← mul_div_assoc]
  rw [hlin, norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_phaseAverage_le_phaseNorm v φ hφ) (norm_nonneg _)

theorem phaseNorm_nonneg_of_pos {s : ℕ} (hs : 0 < s) (I : Finset ℤ) (v : ℤ → ℂ) :
    0 ≤ phaseNorm s I v :=
  (norm_nonneg _).trans (norm_phaseAverage_le_phaseNorm v (0 : Polynomial ℝ) (by simpa using hs))

/-- An explicit common polynomial orbit window, uniform in averaging scale. -/
theorem exists_polynomial_orbit_window {ℓ d : ℕ} (P : Fin ℓ → Polynomial ℤ)
    (hdeg : ∀ i, (P i).natDegree ≤ d) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ H : ℕ, 0 < H →
      positiveInterval (H ^ d) ⊆ spatialInterval C (H ^ d) ∧
      ∀ m ∈ positiveInterval (H ^ d), ∀ n ∈ positiveInterval H, ∀ i,
        m + (P i).eval n ∈ spatialInterval C (H ^ d) := by
  let coeffBound (i : Fin ℓ) : ℝ := ∑ j ∈ Finset.range (d + 1), ‖((P i).coeff j : ℝ)‖
  let B : ℝ := ∑ i, coeffBound i
  have hB : 0 ≤ B := Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg (fun j _ => norm_nonneg _)
  refine ⟨1 + B, by linarith, ?_⟩
  intro H hH
  have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hpow : 0 ≤ (H : ℝ) ^ d := pow_nonneg (by positivity) _
  have hwindow (z : ℤ) (hz : ‖(z : ℝ)‖ ≤ (1 + B) * (H : ℝ)^d) :
      z ∈ spatialInterval (1 + B) (H ^ d) := by
    have hb := abs_le.mp (by simpa only [Real.norm_eq_abs] using hz)
    simp only [spatialInterval, Finset.mem_Icc, Int.ceil_le, Int.le_floor, Nat.cast_pow]
    exact ⟨by simpa only [neg_mul] using hb.1, hb.2⟩
  have hpos {m : ℤ} (hm : m ∈ positiveInterval (H ^ d)) :
      ‖(m : ℝ)‖ ≤ (H : ℝ) ^ d := by
    have hl := (Finset.mem_Icc.mp hm).1
    have hu := (Finset.mem_Icc.mp hm).2
    rw [Real.norm_eq_abs, abs_of_nonneg (by exact_mod_cast (show 0 ≤ m by omega)),
      ← Nat.cast_pow]
    exact_mod_cast hu
  refine ⟨fun m hm => hwindow m ((hpos hm).trans ?_), ?_⟩
  · conv_lhs => rw [← one_mul ((H : ℝ)^d)]
    exact mul_le_mul_of_nonneg_right (by linarith) hpow
  intro m hm n hn i
  have hnlow : 0 ≤ n := (show (0 : ℤ) ≤ 1 by norm_num).trans (Finset.mem_Icc.mp hn).1
  have hnhigh : n ≤ H := (Finset.mem_Icc.mp hn).2
  have hnabs : ‖(n : ℝ)‖ ≤ H := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by exact_mod_cast hnlow)]
    exact_mod_cast hnhigh
  have h_eval : ‖(((P i).eval n : ℤ) : ℝ)‖ ≤ coeffBound i * (H : ℝ)^d := by
    rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (hdeg i))]
    push_cast
    refine (norm_sum_le _ _).trans ?_
    unfold coeffBound
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j hj => ?_
    rw [norm_mul, norm_pow]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine (pow_le_pow_left₀ (norm_nonneg _) hnabs j).trans ?_
    exact pow_le_pow_right₀ hHr (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hj))
  have hi : coeffBound i ≤ B :=
    Finset.single_le_sum (f := coeffBound)
      (fun k _ => Finset.sum_nonneg fun j _ => norm_nonneg _) (Finset.mem_univ i)
  apply hwindow
  push_cast
  calc
    _ ≤ ‖(m : ℝ)‖ + ‖(((P i).eval n : ℤ) : ℝ)‖ := norm_add_le _ _
    _ ≤ (H : ℝ)^d + coeffBound i * (H : ℝ)^d := add_le_add (hpos hm) h_eval
    _ ≤ (H : ℝ)^d + B * (H : ℝ)^d := by
      exact add_le_add_left (mul_le_mul_of_nonneg_right hi hpow) _
    _ = (1 + B) * (H : ℝ)^d := by ring

theorem eventually_inv_le_log_rpow_neg (B : ℝ) :
    ∀ᶠ H : ℕ in atTop, (H : ℝ)⁻¹ ≤ (Real.log (H : ℝ)) ^ (-B) := by
  have h := ((isLittleO_log_rpow_rpow_atTop B (s := 1) zero_lt_one).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))).bound zero_lt_one
  have hlog : ∀ᶠ H : ℕ in atTop, (1 : ℝ) ≤ Real.log (H : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [h, hlog] with H hb hl
  have hl' : 0 < Real.log (H : ℝ) := by linarith
  have hc : Real.log (H : ℝ) ^ B ≤ (H : ℝ) := by
    simpa [Function.comp_def, Real.norm_of_nonneg (Real.rpow_nonneg hl'.le B)] using hb
  rw [Real.rpow_neg hl'.le]
  exact inv_anti₀ (Real.rpow_pos_of_pos hl' B) hc

theorem norm_mangoldt_weight_le {W : ℝ} (hW : 0 ≤ W) (w : ℤ → ℂ)
    (hw : ∀ n, ‖w n‖ ≤ W) {H : ℕ} (hH : 2 ≤ H)
    {n : ℤ} (hn : n ∈ positiveInterval H) :
    ‖(ArithmeticFunction.vonMangoldt (n + 1).toNat : ℂ) * w n‖ ≤
      (W + 1) * (2 * Real.log H + 1) := by
  have hHreal : (2 : ℝ) ≤ H := by exact_mod_cast hH
  obtain ⟨hn₁, hn₂⟩ := Finset.mem_Icc.mp hn
  have hlog : 0 ≤ Real.log (H : ℝ) := Real.log_nonneg (by linarith)
  have hcast : ((n + 1).toNat : ℝ) = (n : ℝ) + 1 := by
    exact_mod_cast Int.toNat_of_nonneg (show 0 ≤ n + 1 by omega)
  have hnreal : (n : ℝ) ≤ H := by exact_mod_cast hn₂
  have hnreal' : (1 : ℝ) ≤ n := by exact_mod_cast hn₁
  have hlog' : ArithmeticFunction.vonMangoldt (n + 1).toNat ≤ 2 * Real.log H := by
    apply ArithmeticFunction.vonMangoldt_le_log.trans
    have hlogpow : Real.log ((H : ℝ)^2) = 2 * Real.log H := by
      simp [Real.log_pow]
    rw [hcast, ← hlogpow]
    apply Real.log_le_log (by linarith)
    nlinarith [sq_nonneg ((H : ℝ) - 2)]
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  exact (mul_le_mul hlog' (hw n) (norm_nonneg _) (by positivity)).trans (by nlinarith)

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

private theorem norm_ergodicSequence_le_one {ℓ : ℕ} (T : ProbabilitySystem X μ)
    (P : Fin ℓ → Polynomial ℤ) (f : Fin ℓ → X → ℂ)
    (hf : ∀ i x, ‖f i x‖ ≤ 1) (n : ℤ) (x : X) :
    ‖ergodicSequence T P f n x‖ ≤ 1 := by
  simpa only [ergodicSequence, norm_prod, Finset.prod_const_one] using
    (Finset.prod_le_prod (s := Finset.univ) (g := fun _ : Fin ℓ => (1 : ℝ))
      (fun i _ => norm_nonneg (f i ((T.transform ^ (P i).eval n) x)))
      (fun i _ => hf i ((T.transform ^ (P i).eval n) x)))

private theorem weightedErgodicAverage_integrable_unit [IsFiniteMeasure μ] {ℓ : ℕ}
    (T : ProbabilitySystem X μ) (P : Fin ℓ → Polynomial ℤ) (f : Fin ℓ → X → ℂ)
    (hf : ∀ i x, ‖f i x‖ ≤ 1) (hfm : ∀ i, AEStronglyMeasurable (f i) μ)
    (v : ℤ → ℂ) (H : ℕ) : Integrable (weightedErgodicAverage T P f v H) μ := by
  unfold weightedErgodicAverage
  simp only [div_eq_mul_inv]
  apply Integrable.mul_const
  apply integrable_finset_sum
  intro n hn
  apply memLp_one_iff_integrable.mp
  apply MemLp.of_bound _ (‖v n‖)
  · apply ae_of_all
    intro x
    rw [norm_mul]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (norm_ergodicSequence_le_one T P f hf n x) (norm_nonneg (v n))
  · apply AEStronglyMeasurable.const_mul
    apply Finset.aestronglyMeasurable_prod
    intro i _
    exact (hfm i).comp_quasiMeasurePreserving (T.preserves ((P i).eval n)).quasiMeasurePreserving

private theorem weightedErgodicAverage_const_mul {ℓ : ℕ}
    (T : ProbabilitySystem X μ) (P : Fin ℓ → Polynomial ℤ) (f : Fin ℓ → X → ℂ)
    (v : ℤ → ℂ) (z : ℂ) (H : ℕ) (x : X) :
    weightedErgodicAverage T P f (fun n => z * v n) H x =
      z * weightedErgodicAverage T P f v H x := by
  simp only [weightedErgodicAverage, mul_assoc, ← Finset.mul_sum, ← mul_div_assoc]

private theorem norm_weightedErgodicAverage_le {ℓ : ℕ}
    (T : ProbabilitySystem X μ) (P : Fin ℓ → Polynomial ℤ) (f : Fin ℓ → X → ℂ)
    (hf : ∀ i x, ‖f i x‖ ≤ 1) (v : ℤ → ℂ) {H : ℕ} {D : ℝ} (hv : ∀ n ∈ positiveInterval H, ‖v n‖ ≤ D)
    (hD : 0 ≤ D) (x : X) : ‖weightedErgodicAverage T P f v H x‖ ≤ D := by
  by_cases hH : H = 0
  · simpa [weightedErgodicAverage, hH] using hD
  have hH' : (0 : ℝ) < H := by exact_mod_cast Nat.pos_of_ne_zero hH
  rw [weightedErgodicAverage, norm_div, Complex.norm_natCast, div_le_iff₀ hH']
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _ ∈ positiveInterval H, D := by
      refine Finset.sum_le_sum fun n hn => ?_
      rw [norm_mul]
      simpa only [mul_one] using
        mul_le_mul (hv n hn) (norm_ergodicSequence_le_one T P f hf n x) (norm_nonneg _) hD
    _ = D * (H : ℝ) := by simp [nsmul_eq_mul, mul_comm]

/-- Quantitative logarithmic decay for pointwise unit-bounded inputs. The
constant is chosen before the family of input functions. -/
theorem mangoldt_L1_log_decay_unit_of_primeLocalPhase
    (hTer : TeravainenFixedFamily) {ℓ d : ℕ} (hd : 0 < d)
    (P : Fin ℓ → Polynomial ℤ) (hP : ErgodicPolynomialFamily P)
    (hdeg : ∀ i, (P i).natDegree ≤ d) (htop : ∃ i, (P i).natDegree = d)
    (V : ℤ → ℝ) (F : Circle → ℂ) (hp : PrimeLocalPhase d V F)
    {A : ℝ} (hA : 0 < A)
    {W : ℝ} (hW : 0 ≤ W) (hw : ∀ n, ‖F (V n : Circle) - circleMean F‖ ≤ W) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type u} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
        (T : ProbabilitySystem X μ) (f : Fin ℓ → X → ℂ),
      (∀ i x, ‖f i x‖ ≤ 1) → (∀ i, AEStronglyMeasurable (f i) μ) →
      ∀ H : ℕ, 2 ≤ H →
      (∫ x, ‖mangoldtAverage T P f (fun n => F (V n : Circle) - circleMean F) H x‖ ∂μ) ≤
        C * (Real.log H)^(-A) := by
  let w : ℤ → ℂ := fun n => F (V n : Circle) - circleMean F
  let θ : ℤ → ℂ := fun n => (ArithmeticFunction.vonMangoldt (n + 1).toNat : ℂ) * w n
  let L (H : ℕ) : ℝ := (W + 1) * (2 * Real.log H + 1)
  let v (H : ℕ) (n : ℤ) : ℂ := (((L H)⁻¹ : ℝ) : ℂ) * θ n
  obtain ⟨Cw, hCw, hwindow⟩ := exists_polynomial_orbit_window P hdeg
  obtain ⟨K, C, hK, hC, horbit⟩ :=
    uniform_orbit_bound_of_teravainen.{u} hTer d hd P hP hdeg htop Cw hCw
  have hK₀ : 0 < K := by linarith
  let B : ℝ := K * (A + 1)
  have hB : 0 < B := mul_pos hK₀ (by linarith)
  obtain ⟨E, hE, hphase⟩ := phaseNorm_mangoldt_eventually_log_decay hd V F hp hB
  have hLone (H : ℕ) (hH : 2 ≤ H) : 1 ≤ L H := by
    have hn : (2 : ℝ) ≤ H := by exact_mod_cast hH
    unfold L
    have hh : 0 ≤ Real.log (H : ℝ) := Real.log_nonneg (by linarith)
    nlinarith [mul_nonneg hW hh]
  have hLpos (H : ℕ) (hH : 2 ≤ H) : 0 < L H := zero_lt_one.trans_le (hLone H hH)
  have hbnd (H : ℕ) (hH : 2 ≤ H) : ∀ n ∈ positiveInterval H, ‖θ n‖ ≤ L H :=
    fun _ hn => norm_mangoldt_weight_le hW w hw hH hn
  have hvunit (H : ℕ) (hH : 2 ≤ H) : OneBoundedOn (positiveInterval H) (v H) := by
    intro n hn
    simp only [v, norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr (hLpos H hH).le)]
    exact (mul_le_mul_of_nonneg_left (hbnd H hH n hn) (inv_nonneg.mpr (hLpos H hH).le)).trans
      (inv_mul_cancel₀ (hLpos H hH).ne').le
  have hphase' : ∀ᶠ H : ℕ in atTop, 2 ≤ H →
      phaseNorm (d + 1) (positiveInterval H) (v H) ≤ E * (Real.log H)^(-B) := by
    filter_upwards [hphase] with H hH hH₂
    refine (phaseNorm_const_mul_le (show 0 < d + 1 by omega) (positiveInterval H)
      θ (((L H)⁻¹ : ℝ) : ℂ)).trans ?_
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity : 0 ≤ (L H)⁻¹)]
    have hnorm := phaseNorm_nonneg_of_pos (show 0 < d + 1 by omega) (positiveInterval H) θ
    refine (mul_le_of_le_one_left hnorm (inv_le_one_of_one_le₀ (hLone H hH₂))).trans hH
  let D : ℝ := 3 * (W + 1) * C * (1 + E) ^ (1 / K)
  have hD : 0 < D := by dsimp [D]; positivity
  have hlog : ∀ᶠ H : ℕ in atTop, (1 : ℝ) ≤ Real.log (H : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  have hlarge : ∀ᶠ H : ℕ in atTop, 2 ≤ H →
      L H * (C * ((H : ℝ)⁻¹ + phaseNorm (d + 1) (positiveInterval H) (v H)) ^ (1 / K))
        ≤ D * (Real.log H)^(-A) := by
    filter_upwards [hphase', hlog, eventually_inv_le_log_rpow_neg B] with H hp' hlogH hInv hH
    have hLog : 0 < Real.log (H : ℝ) := by linarith
    have hLn : L H ≤ 3 * (W + 1) * Real.log H := by
      unfold L
      nlinarith [mul_nonneg (show 0 ≤ W + 1 by linarith)
        (show 0 ≤ Real.log (H : ℝ) - 1 by linarith)]
    have hu : (H : ℝ)⁻¹ + phaseNorm (d + 1) (positiveInterval H) (v H) ≤
        (1 + E) * (Real.log H)^(-B) := by
      rw [add_mul, one_mul]
      exact add_le_add hInv (hp' hH)
    have hun : 0 ≤ (H : ℝ)⁻¹ + phaseNorm (d + 1) (positiveInterval H) (v H) :=
      add_nonneg (by positivity) (phaseNorm_nonneg_of_pos (by omega) _ _)
    have hPow : ((1 + E) * (Real.log H)^(-B)) ^ (1 / K) =
        (1 + E)^(1 / K) * (Real.log H)^(-(A + 1)) := by
      have hexp : -B * (1 / K) = -(A + 1) := by
        dsimp [B]
        field_simp [hK₀.ne']
        ring
      rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hLog.le _),
        ← Real.rpow_mul hLog.le, hexp]
    have hlogmult : Real.log (H : ℝ) * (Real.log H)^(-(A + 1)) =
        (Real.log H)^(-A) := by
      nth_rw 1 [← Real.rpow_one (Real.log (H : ℝ))]
      rw [← Real.rpow_add hLog]
      congr 1
      ring
    calc
      _ ≤ L H * (C * (((1 + E) * (Real.log H)^(-B)) ^ (1 / K))) := by
        gcongr
      _ = L H * (C * ((1 + E)^(1 / K) * (Real.log H)^(-(A + 1)))) := by rw [hPow]
      _ ≤ (3 * (W + 1) * Real.log H) *
          (C * ((1 + E)^(1 / K) * (Real.log H)^(-(A + 1)))) :=
        mul_le_mul_of_nonneg_right hLn (by positivity)
      _ = D * (Real.log H)^(-A) := by
        unfold D
        rw [← hlogmult]
        ring
  obtain ⟨N, hN⟩ := eventually_atTop.mp hlarge
  let N₁ := max 2 N
  have hN₁ : 2 ≤ N₁ := le_max_left _ _
  have hN₁real : (2 : ℝ) ≤ N₁ := by exact_mod_cast hN₁
  have hlogN₁ : 0 < Real.log (N₁ : ℝ) := Real.log_pos (by linarith)
  let D₁ := L N₁ * (Real.log N₁)^A
  have hD₁ : 0 ≤ D₁ := mul_nonneg (hLpos _ hN₁).le (Real.rpow_nonneg hlogN₁.le _)
  refine ⟨D + D₁, add_pos_of_pos_of_nonneg hD hD₁, ?_⟩
  intro X _ μ _ T f hf hfm H hH
  have hscale (f : Fin ℓ → X → ℂ) (H : ℕ) (hH : 2 ≤ H) (x : X) :
      weightedErgodicAverage T P f θ H x = (L H : ℂ) *
        weightedErgodicAverage T P f (v H) H x := by
    rw [show (v H) = (fun n => (((L H)⁻¹ : ℝ) : ℂ) * θ n) from rfl,
      weightedErgodicAverage_const_mul, ← mul_assoc, ← Complex.ofReal_mul,
      mul_inv_cancel₀ (hLpos H hH).ne', Complex.ofReal_one, one_mul]
  have hHreal : (2 : ℝ) ≤ H := by exact_mod_cast hH
  have hLog : 0 < Real.log (H : ℝ) := Real.log_pos (by linarith)
  change (∫ x, ‖weightedErgodicAverage T P f θ H x‖ ∂μ) ≤ _
  by_cases hHN : N ≤ H
  · obtain ⟨hsub, hz⟩ := hwindow H (by omega)
    have hb := horbit T H (by omega) (v H) f (hvunit H hH) hf
      (weightedErgodicAverage_integrable_unit T P f hf hfm (v H) H) hsub hz
    have hsc : (∫ x, ‖weightedErgodicAverage T P f θ H x‖ ∂μ) =
        L H * ∫ x, ‖weightedErgodicAverage T P f (v H) H x‖ ∂μ := by
      simp_rw [hscale f H hH, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (hLpos H hH).le, integral_const_mul]
    rw [hsc]
    exact ((mul_le_mul_of_nonneg_left hb (hLpos H hH).le).trans (hN H hHN hH)).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hD₁) (Real.rpow_nonneg hLog.le _))
  · have hLe : H ≤ N₁ := (not_le.mp hHN).le.trans (le_max_right _ _)
    have hlogLe : Real.log H ≤ Real.log (N₁ : ℝ) :=
      Real.log_le_log (by linarith) (by exact_mod_cast hLe)
    have hint : (∫ x, ‖weightedErgodicAverage T P f θ H x‖ ∂μ) ≤ L H := by
      have hm := integral_mono_of_nonneg
        (ae_of_all μ (fun x => norm_nonneg (weightedErgodicAverage T P f θ H x)))
        (integrable_const (L H))
        (ae_of_all μ (norm_weightedErgodicAverage_le T P f hf θ (hbnd H hH) (hLpos H hH).le))
      simpa using hm
    calc
      _ ≤ L H := hint
      _ ≤ L N₁ := by unfold L; gcongr
      _ = D₁ * (Real.log (N₁ : ℝ))^(-A) := by
        unfold D₁
        rw [mul_assoc, ← Real.rpow_add hlogN₁, add_neg_cancel, Real.rpow_zero, mul_one]
      _ ≤ D₁ * (Real.log H)^(-A) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_nonpos hLog hlogLe
          (neg_nonpos.mpr hA.le)) hD₁
      _ ≤ (D + D₁) * (Real.log H)^(-A) :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hD.le) (Real.rpow_nonneg hLog.le _)

private theorem exists_unit_normalized {ℓ : ℕ} (f : Fin ℓ → X → ℂ)
    (hf : ∀ i, MemLp (f i) ∞ μ) :
    ∃ g : Fin ℓ → X → ℂ, (∀ i x, ‖g i x‖ ≤ 1) ∧
      (∀ i, AEStronglyMeasurable (g i) μ) ∧
      (∀ i, f i =ᵐ[μ] fun x => ((eLpNorm (f i) ∞ μ).toReal : ℂ) * g i x) := by
  classical
  let c (i : Fin ℓ) : ℝ := (eLpNorm (f i) ∞ μ).toReal
  let f' (i : Fin ℓ) (x : X) : ℂ := if ‖f i x‖ ≤ c i then f i x else 0
  let g (i : Fin ℓ) (x : X) : ℂ := (((c i)⁻¹ : ℝ) : ℂ) * f' i x
  have hc (i : Fin ℓ) : 0 ≤ c i := ENNReal.toReal_nonneg
  have hfae (i : Fin ℓ) : ∀ᵐ x ∂μ, ‖f i x‖ ≤ c i := by
    filter_upwards [ae_le_eLpNormEssSup (f := f i) (μ := μ)] with x hx
    rw [← eLpNorm_exponent_top] at hx
    simpa [c] using ENNReal.toReal_mono (hf i).2.ne hx
  refine ⟨g, ?_, ?_, ?_⟩
  · intro i x
    by_cases hz : c i = 0
    · simp [g, hz]
    have hcn : 0 < c i := lt_of_le_of_ne (hc i) (Ne.symm hz)
    by_cases h : ‖f i x‖ ≤ c i
    · simp only [g, f', if_pos h]
      rw [norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (inv_nonneg.mpr (hc i))]
      exact (mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (hc i))).trans
        (inv_mul_cancel₀ hcn.ne').le
    · simp [g, f', h]
  · intro i
    have h' : AEStronglyMeasurable (f' i) μ := by
      apply (hf i).aestronglyMeasurable.congr
      exact (hfae i).mono fun x hx => by simp [f', hx]
    exact h'.const_mul _
  · intro i
    filter_upwards [hfae i] with x hx
    change f i x = (c i : ℂ) * g i x
    by_cases hz : c i = 0
    · have hzero : f i x = 0 := by
        apply norm_eq_zero.mp
        exact le_antisymm (hx.trans_eq hz) (norm_nonneg _)
      simp [hz, hzero]
    · simp only [g, f', if_pos hx]
      rw [← mul_assoc, ← Complex.ofReal_mul,
        mul_inv_cancel₀ hz, Complex.ofReal_one, one_mul]

private theorem weightedErgodicAverage_ae_scale_inputs {ℓ : ℕ}
    (T : ProbabilitySystem X μ) (P : Fin ℓ → Polynomial ℤ) (f g : Fin ℓ → X → ℂ)
    (c : Fin ℓ → ℝ) (hfg : ∀ i, f i =ᵐ[μ] fun x => (c i : ℂ) * g i x)
    (θ : ℤ → ℂ) (H : ℕ) :
    weightedErgodicAverage T P f θ H =ᵐ[μ]
      fun x => (((∏ i, c i) : ℝ) : ℂ) * weightedErgodicAverage T P g θ H x := by
  have ht (i : Fin ℓ) (n : ℤ) :
      ∀ᵐ x ∂μ, f i ((T.transform ^ (P i).eval n) x) =
        (c i : ℂ) * g i ((T.transform ^ (P i).eval n) x) :=
    (T.preserves _).quasiMeasurePreserving.ae (hfg i)
  have h : ∀ᵐ x ∂μ, ∀ (i : Fin ℓ) (n : ℤ),
      f i ((T.transform ^ (P i).eval n) x) =
        (c i : ℂ) * g i ((T.transform ^ (P i).eval n) x) :=
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (ht i))
  filter_upwards [h] with x hx
  have he (n : ℤ) : ergodicSequence T P f n x =
      (((∏ i, c i) : ℝ) : ℂ) * ergodicSequence T P g n x := by
    unfold ergodicSequence
    simp_rw [hx]
    rw [Finset.prod_mul_distrib, Complex.ofReal_prod]
  simp only [weightedErgodicAverage, he]
  simp_rw [mul_left_comm (θ _), ← Finset.mul_sum, ← mul_div_assoc]

private theorem exists_max_ergodic_degree {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ)
    (hP : ErgodicPolynomialFamily P) :
    ∃ d : ℕ, 0 < d ∧ (∀ i, (P i).natDegree ≤ d) ∧ (∃ i, (P i).natDegree = d) := by
  let i : Fin ℓ := ⟨ℓ - 1, by have := hP.1; omega⟩
  refine ⟨(P i).natDegree, (hP.2.1 i).1, ?_, ⟨i, rfl⟩⟩
  intro j
  apply hP.2.2.monotone
  exact Fin.le_iff_val_le_val.mpr (by dsimp [i]; have := j.isLt; omega)

/-- The full logarithmic L¹ bound in Proposition 7.1. The coefficient is
uniform over the input family and multiplies its exact essential sup norms.
The unit-normalized proof above also supplies the finite initial range. -/
theorem mangoldt_L1_log_decay_of_primeLocalPhase
    (hTer : TeravainenFixedFamily) {ℓ d : ℕ} (hd : 0 < d)
    (P : Fin ℓ → Polynomial ℤ) (hP : ErgodicPolynomialFamily P)
    (hdeg : ∀ i, (P i).natDegree ≤ d) (htop : ∃ i, (P i).natDegree = d)
    (V : ℤ → ℝ) (F : Circle → ℂ) (hp : PrimeLocalPhase d V F)
    {A : ℝ} (hA : 0 < A)
    {W : ℝ} (hW : 0 ≤ W) (hw : ∀ n, ‖F (V n : Circle) - circleMean F‖ ≤ W) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type u} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
        (T : ProbabilitySystem X μ) (f : Fin ℓ → X → ℂ), (∀ i, MemLp (f i) ∞ μ) →
      ∀ H : ℕ, 2 ≤ H →
        let w := fun n : ℤ => F (V n : Circle) - circleMean F
        let M := mangoldtAverage T P f w H
        (eLpNorm M 1 μ).toReal = (∫ x, ‖M x‖ ∂μ) ∧
        (∫ x, ‖M x‖ ∂μ) ≤
          C * (Real.log H)^(-A) * ∏ i, (eLpNorm (f i) ∞ μ).toReal := by
  let w := fun n : ℤ => F (V n : Circle) - circleMean F
  let θ : ℤ → ℂ := fun n => (ArithmeticFunction.vonMangoldt (n + 1).toNat : ℂ) * w n
  obtain ⟨C, hC, hbound⟩ := mangoldt_L1_log_decay_unit_of_primeLocalPhase
    hTer hd P hP hdeg htop V F hp hA hW hw
  refine ⟨C, hC, ?_⟩
  intro X _ μ _ T f hf H hH
  let c (i : Fin ℓ) : ℝ := (eLpNorm (f i) ∞ μ).toReal
  let S : ℝ := ∏ i, c i
  have hS : 0 ≤ S := Finset.prod_nonneg (fun _ _ => ENNReal.toReal_nonneg)
  obtain ⟨g, hg, hgm, hfg⟩ := exists_unit_normalized f hf
  let Mf := mangoldtAverage T P f w H
  let Mg := mangoldtAverage T P g w H
  have he : Mf =ᵐ[μ] fun x => (S : ℂ) * Mg x :=
    weightedErgodicAverage_ae_scale_inputs T P f g c hfg θ H
  have hgi : Integrable Mg μ :=
    weightedErgodicAverage_integrable_unit T P g hg hgm θ H
  have hfi : Integrable Mf μ :=
    (hgi.const_mul (S : ℂ)).congr he.symm
  change (eLpNorm Mf 1 μ).toReal = (∫ x, ‖Mf x‖ ∂μ) ∧
    (∫ x, ‖Mf x‖ ∂μ) ≤ C * (Real.log H)^(-A) * S
  constructor
  · rw [eLpNorm_one_eq_lintegral_enorm, integral_norm_eq_lintegral_enorm hfi.aestronglyMeasurable]
  · calc
      _ = S * ∫ x, ‖Mg x‖ ∂μ := by
        rw [integral_congr_ae (he.mono (fun x hx => congrArg norm hx))]
        simp_rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hS, integral_const_mul]
      _ ≤ C * (Real.log H)^(-A) * S := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right (hbound T g hg hgm H hH) hS

private theorem exists_centered_selector_bound
    (V : ℤ → ℝ) (F : Circle → ℂ) (hF : Continuous F) :
    ∃ W : ℝ, 0 ≤ W ∧ ∀ n : ℤ, ‖F (V n : Circle) - circleMean F‖ ≤ W := by
  obtain ⟨W, hW⟩ := (isCompact_univ (X := Circle)).exists_bound_of_continuousOn
    ((hF.sub continuous_const : Continuous (fun x => F x - circleMean F)).continuousOn)
  exact ⟨max W 0, le_max_right _ _, fun n => (hW _ (Set.mem_univ _)).trans (le_max_left _ _)⟩

/-- All three claims of Proposition 7.1 conditional on the original
prime-weighted phase estimate from Proposition 6.2 and the named literature
inputs. The logarithmic bound holds with the exact product of essential sup
norms at every positive saving exponent. -/
theorem smoothErgodicComparison_of_primeLocalPhase [IsProbabilityMeasure μ]
    (hTer : TeravainenFixedFamily) (hPNT : PrimeNumberTheorem)
    {ℓ d : ℕ} (hd : 0 < d) (P : Fin ℓ → Polynomial ℤ) (hP : ErgodicPolynomialFamily P)
    (hdeg : ∀ i, (P i).natDegree ≤ d) (htop : ∃ i, (P i).natDegree = d)
    (V : ℤ → ℝ) (F : Circle → ℂ) (hF : Continuous F) (hp : PrimeLocalPhase d V F)
    (T : ProbabilitySystem X μ) (f : Fin ℓ → X → ℂ) (hf : ∀ i, MemLp (f i) ∞ μ) :
    SmoothErgodicComparison T P f V F := by
  obtain ⟨W, hW, hw⟩ := exists_centered_selector_bound V F hF
  let w := fun n : ℤ => F (V n : Circle) - circleMean F
  have hrate (A : ℝ) (hA : 0 < A) :=
    mangoldt_L1_log_decay_of_primeLocalPhase hTer hd P hP hdeg htop V F hp hA hW hw
  have hL1 (A : ℝ) (hA : 0 < A) :
      ∃ C : ℝ, 0 < C ∧ ∀ H : ℕ, 2 ≤ H →
        (eLpNorm (mangoldtAverage T P f w H) 1 μ).toReal ≤
          C * (Real.log H)^(-A) * ∏ i, (eLpNorm (f i) ∞ μ).toReal := by
    obtain ⟨C, hC, hb⟩ := hrate A hA
    refine ⟨C, hC, ?_⟩
    intro H hH
    rw [(hb T f hf H hH).1]
    exact (hb T f hf H hH).2
  obtain ⟨C, hC, hb⟩ := hrate 6 (by norm_num)
  let D := C * ∏ i, (eLpNorm (f i) ∞ μ).toReal
  have hD : 0 ≤ D := by unfold D; positivity
  have h6 (H : ℕ) (hH : 2 ≤ H) :
      (∫ x, ‖mangoldtAverage T P f w H x‖ ∂μ) ≤ D / (Real.log (H : ℝ))^6 := by
    have hH' : (2 : ℝ) ≤ H := by exact_mod_cast hH
    have hlog : 0 < Real.log (H : ℝ) := Real.log_pos (by linarith)
    calc
      _ ≤ C * (Real.log H)^(-(6 : ℝ)) * ∏ i, (eLpNorm (f i) ∞ μ).toReal :=
        (hb T f hf H hH).2
      _ = D / (Real.log (H : ℝ))^6 := by
        rw [Real.rpow_neg hlog.le,
          show Real.log (H : ℝ) ^ (6 : ℝ) = Real.log (H : ℝ) ^ (6 : ℕ) from
            Real.rpow_natCast _ 6, div_eq_mul_inv]
        unfold D
        ring
  exact ⟨hL1, ae_mangoldtAverage_tendsto_zero_of_log_decay T P f hf w hW hw hD h6,
    ae_primeAverage_tendsto_zero_of_mangoldt_log_decay hPNT T P f hf w hW hw hD h6⟩

/-- Prime-weighted phase control for each fixed smooth selector suffices for the
logarithmic L¹ decay used in the proof of Theorem 1.4. -/
theorem smoothErgodicLogDecay_of_primeLocalPhase [IsProbabilityMeasure μ]
    (hTer : TeravainenFixedFamily) {ℓ : ℕ}
    (P : Fin ℓ → Polynomial ℤ) (hP : ErgodicPolynomialFamily P)
    (V : ℤ → ℝ) (hp : ∀ d : ℕ, 0 < d → ∀ F : Circle → ℂ,
      (∃ K : ℝ≥0, LipschitzWith K F) → PrimeLocalPhase d V F)
    (T : ProbabilitySystem X μ) :
    SmoothErgodicLogDecay T P V := by
  intro f hf F hF
  obtain ⟨d, hd, hdeg, htop⟩ := exists_max_ergodic_degree P hP
  obtain ⟨K, hK⟩ := hF
  obtain ⟨W, hW, hw⟩ := exists_centered_selector_bound V F hK.continuous
  obtain ⟨C, hC, hb⟩ := mangoldt_L1_log_decay_of_primeLocalPhase
    hTer hd P hP hdeg htop V F (hp d hd F ⟨K, hK⟩) (A := 6) (by norm_num) hW hw
  let D := C * ∏ i, (eLpNorm (f i) ∞ μ).toReal
  refine ⟨D, by unfold D; positivity, ?_⟩
  intro H hH
  have hH' : (2 : ℝ) ≤ H := by exact_mod_cast hH
  have hlog : 0 < Real.log (H : ℝ) := Real.log_pos (by linarith)
  calc
    _ ≤ C * (Real.log H)^(-(6 : ℝ)) * ∏ i, (eLpNorm (f i) ∞ μ).toReal :=
      (hb T f hf H hH).2
    _ = D / (Real.log (H : ℝ))^6 := by
      rw [Real.rpow_neg hlog.le,
          show Real.log (H : ℝ) ^ (6 : ℝ) = Real.log (H : ℝ) ^ (6 : ℕ) from
            Real.rpow_natCast _ 6, div_eq_mul_inv]
      unfold D
      ring

/-- A conditional version of the main pointwise theorem. The upstream
premise is the original prime-weighted phase estimate of Proposition 6.2. -/
theorem primePointwiseFor_of_primeLocalPhase
    (hPNT : PrimeNumberTheorem) (hMWW : MirekWanWrightPointwise X)
    (hTer : TeravainenFixedFamily) (V : ℝ → ℝ → ℤ → ℝ)
    (hp : ∀ α β : ℝ, BadlyApproximable α → AdmissibleBeta β →
      ∀ d : ℕ, 0 < d → ∀ F : Circle → ℂ,
        (∃ K : ℝ≥0, LipschitzWith K F) → PrimeLocalPhase d (V α β) F) :
    PrimePointwiseFor X V := by
  intro μ _ T ℓ P hP f hf α β hα hβ J
  exact pointwise_of_smooth_log_decay hPNT hMWW T P hP f hf (V α β) J
    (smoothErgodicLogDecay_of_primeLocalPhase hTer P hP (V α β) (hp α β hα hβ) T)

end NilBohr
