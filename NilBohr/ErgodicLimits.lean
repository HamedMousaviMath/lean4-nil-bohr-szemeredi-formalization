import NilBohr.Convergence
import NilBohr.Ergodic
import NilBohr.PrimePowers

/-!
# Mangoldt, log-prime, and prime averages

This module checks the analytic deductions after the logarithmic (L^1)
bound in Proposition 7.1, and the conversion of the external
Mirek–Wan–Wright theorem to the unrestricted limit in Theorem 1.4.
-/

namespace NilBohr

open Filter MeasureTheory Polynomial
open scoped Topology BigOperators ENNReal

/-- The two standard forms of the prime number theorem used in the
logarithmic-weight removal argument. -/
structure PrimeNumberTheorem : Prop where
  count : Tendsto (fun n : ℕ => ((primesThrough n).card : ℝ) *
    Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 1)
  theta : Tendsto (fun n : ℕ => (∑ p ∈ primesThrough n, Real.log (p : ℝ)) /
    (n : ℝ)) atTop (𝓝 1)

private theorem primeAverage_eq_finsetAverage (a : ℕ → ℂ) (N : ℕ) :
    primeAverage a N = finsetAverage (primesThrough N) a := by
  simp only [primeAverage, finsetAverage, Complex.real_smul, Complex.ofReal_inv,
    Complex.ofReal_natCast, div_eq_inv_mul]

/-- The normalization implication with the exact prime average of
Theorem 1.4. Higher prime powers are removed by a checked estimate. -/
theorem tendsto_primeAverage_of_tendsto_mangoldt (hPNT : PrimeNumberTheorem)
    {a : ℕ → ℂ} {B : ℝ} {L : ℂ} (ha : ∀ n, ‖a n‖ ≤ B)
    (h : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ • ∑ n ∈ Finset.range (N + 1),
      ArithmeticFunction.vonMangoldt n • a n) atTop (𝓝 L)) :
    Tendsto (primeAverage a) atTop (𝓝 L) := by
  rw [show primeAverage a = (fun N => finsetAverage (primesThrough N) a) from
    funext (primeAverage_eq_finsetAverage a)]
  refine tendsto_finsetAverage_of_tendsto_logWeighted ha (fun n i hi => ?_)
    hPNT.count hPNT.theta (tendsto_logPrime_of_tendsto_mangoldt ha h)
  exact Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp hi).1)

/-- The same implication for the manuscript's (n+1) argument of the
Mangoldt weight. The rest of the summand is evaluated at (p=n+1). -/
theorem tendsto_primeAverage_of_tendsto_shifted_mangoldt (hPNT : PrimeNumberTheorem)
    {a : ℕ → ℂ} {B : ℝ} {L : ℂ} (ha : ∀ n, ‖a n‖ ≤ B)
    (h : Tendsto
      (prefixAverage (fun i => ArithmeticFunction.vonMangoldt (i + 2) • a (i + 2)))
      atTop (𝓝 L)) :
    Tendsto (primeAverage a) atTop (𝓝 L) :=
  tendsto_primeAverage_of_tendsto_mangoldt hPNT ha
    (tendsto_mangoldt_of_tendsto_shifted ha h)

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

private theorem sum_positiveInterval_eq_range {E : Type*} [AddCommMonoid E]
    (b : ℤ → E) (H : ℕ) :
    (∑ n ∈ positiveInterval H, b n) =
      ∑ i ∈ Finset.range H, b ((i : ℤ) + 1) := by
  symm
  apply Finset.sum_bij (fun (i : ℕ) _ => (i : ℤ) + 1)
  · intro i hi
    have hi' := Finset.mem_range.mp hi
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro i _ j _ hij
    omega
  · intro n hn
    obtain ⟨hn₁, hn₂⟩ := Finset.mem_Icc.mp hn
    refine ⟨(n - 1).toNat, Finset.mem_range.mpr ?_, ?_⟩ <;> omega
  · intro i hi
    rfl

/-- The finite sum with integer parameter (1le nle H) reindexed for
the prefix-average convergence lemma. -/
theorem mangoldtAverage_eq_shifted_prefixAverage (T : ProbabilitySystem X μ)
    {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ) (f : Fin ℓ → X → ℂ)
    (w : ℤ → ℂ) (H : ℕ) (x : X) :
    mangoldtAverage T P f w H x = prefixAverage
      (fun i => ArithmeticFunction.vonMangoldt (i + 2) •
        (w (((i + 2 : ℕ) : ℤ) - 1) *
          ergodicSequence T P f (((i + 2 : ℕ) : ℤ) - 1) x)) H := by
  unfold mangoldtAverage prefixAverage
  rw [sum_positiveInterval_eq_range]
  simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast, div_eq_inv_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have ht : ((i : ℤ) + 1 + 1).toNat = i + 2 := by omega
  have hh : ((i + 2 : ℕ) : ℤ) - 1 = (i : ℤ) + 1 := by omega
  rw [ht, hh, mul_assoc]

private theorem aestronglyMeasurable_ergodicSequence (T : ProbabilitySystem X μ)
    {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ) (f : Fin ℓ → X → ℂ)
    (hf : ∀ i, MemLp (f i) ∞ μ) (n : ℤ) :
    AEStronglyMeasurable (fun x => ergodicSequence T P f n x) μ := by
  apply Finset.aestronglyMeasurable_prod
  intro i hi
  exact (hf i).1.comp_quasiMeasurePreserving (T.preserves ((P i).eval n)).quasiMeasurePreserving

/-- Proposition 7.1's full-scale almost-everywhere deduction from its
logarithmic (L^1) estimate, stated for a fixed bounded centered
weight. The assumption is the original analytic estimate at (A=6). -/
theorem ae_mangoldtAverage_tendsto_zero_of_log_decay [IsFiniteMeasure μ]
    (T : ProbabilitySystem X μ) {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ)
    (f : Fin ℓ → X → ℂ) (hf : ∀ i, MemLp (f i) ∞ μ)
    (w : ℤ → ℂ) {W C : ℝ} (hW : 0 ≤ W) (hw : ∀ n, ‖w n‖ ≤ W) (hC : 0 ≤ C)
    (h_L1 : ∀ H ≥ 2, (∫ x, ‖mangoldtAverage T P f w H x‖ ∂μ)
        ≤ C / (Real.log (H : ℝ)) ^ 6) :
    ∀ᵐ x ∂μ, Tendsto (fun H => mangoldtAverage T P f w H x) atTop (𝓝 0) := by
  let u (i : ℕ) (x : X) : ℂ :=
    ArithmeticFunction.vonMangoldt (i + 2) •
      (w (((i + 2 : ℕ) : ℤ) - 1) * ergodicSequence T P f (((i + 2 : ℕ) : ℤ) - 1) x)
  obtain ⟨B, hB, hb⟩ := ae_ergodicSequence_bounded T P f hf
  have h_env : ∀ᵐ x ∂μ, ∀ N i, i < N → ‖u i x‖ ≤ (W * B) * Real.log ((N : ℝ) + 2) := by
    filter_upwards [hb] with x hx N i hi
    have hlog : ArithmeticFunction.vonMangoldt (i + 2) ≤ Real.log ((N : ℝ) + 2) := by
      apply ArithmeticFunction.vonMangoldt_le_log.trans
      apply Real.log_le_log (by positivity)
      push_cast
      exact add_le_add_right (by exact_mod_cast hi.le) 2
    simp only [u, Complex.real_smul, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    calc
      _ ≤ Real.log ((N : ℝ) + 2) * (W * B) := by
        refine mul_le_mul hlog (mul_le_mul (hw _) (hx _) (norm_nonneg _) hW)
          (by positivity) ?_
        exact Real.log_nonneg (by linarith [show (0 : ℝ) ≤ N by positivity])
      _ = _ := mul_comm _ _
  have h_int : ∀ N, Integrable (fun x => prefixAverage (fun i => u i x) N) μ := by
    intro N
    unfold prefixAverage
    apply Integrable.smul
    apply integrable_finset_sum
    intro i hi
    apply memLp_one_iff_integrable.mp
    apply MemLp.of_bound
        ((aestronglyMeasurable_ergodicSequence T P f hf _).const_mul _ |>.const_smul _)
        ((W * B) * Real.log ((N : ℝ) + 2))
    filter_upwards [h_env] with x hx
    exact hx N i (Finset.mem_range.mp hi)
  have h_eq (N : ℕ) (x : X) :
      mangoldtAverage T P f w N x = prefixAverage (fun i => u i x) N :=
    mangoldtAverage_eq_shifted_prefixAverage T P f w N x
  simp_rw [h_eq] at h_L1 ⊢
  exact ae_tendsto_zero_prefixAverage_of_log_decay hC (mul_nonneg hW hB) h_env h_int h_L1

/-- Starting from the smooth centered logarithmic (L^1) estimate,
Proposition 7.1's prime-normalized cancellation follows on one conull set. -/
theorem ae_primeAverage_tendsto_zero_of_mangoldt_log_decay [IsFiniteMeasure μ]
    (hPNT : PrimeNumberTheorem)
    (T : ProbabilitySystem X μ) {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ)
    (f : Fin ℓ → X → ℂ) (hf : ∀ i, MemLp (f i) ∞ μ)
    (w : ℤ → ℂ) {W C : ℝ} (hW : 0 ≤ W) (hw : ∀ n, ‖w n‖ ≤ W) (hC : 0 ≤ C)
    (h_L1 : ∀ H ≥ 2, (∫ x, ‖mangoldtAverage T P f w H x‖ ∂μ)
        ≤ C / (Real.log (H : ℝ)) ^ 6) :
    ∀ᵐ x ∂μ, Tendsto
      (primeAverage (fun p => w ((p : ℤ) - 1) * ergodicSequence T P f ((p : ℤ) - 1) x))
      atTop (𝓝 0) := by
  obtain ⟨B, _, hb⟩ := ae_ergodicSequence_bounded T P f hf
  filter_upwards [hb, ae_mangoldtAverage_tendsto_zero_of_log_decay T P f hf w hW hw hC h_L1]
    with x hx hlim
  have ha (p : ℕ) :
      ‖w ((p : ℤ) - 1) * ergodicSequence T P f ((p : ℤ) - 1) x‖ ≤ W * B := by
    rw [norm_mul]
    exact mul_le_mul (hw _) (hx _) (norm_nonneg _) hW
  simp_rw [mangoldtAverage_eq_shifted_prefixAverage] at hlim
  exact tendsto_primeAverage_of_tendsto_shifted_mangoldt hPNT ha hlim


/-- The specialization of Mirek–Wan–Wright [arXiv:2505.15549v2,
Theorem 1.1(ii)] to probability systems and the common exponent
(2ell). This external premise still concludes convergence of the
Mangoldt-weighted average. The polynomial constant terms are arbitrary. -/
def MirekWanWrightPointwise (X : Type*) [MeasurableSpace X] : Prop :=
  ∀ (μ : Measure X) [IsProbabilityMeasure μ] (T : ProbabilitySystem X μ)
    {ℓ : ℕ}, 0 < ℓ →
    ∀ (P : Fin ℓ → Polynomial ℤ), (∀ i, 0 < (P i).natDegree) →
    StrictMono (fun i => (P i).natDegree) →
    ∀ (f : Fin ℓ → X → ℂ), (∀ i, MemLp (f i) ((2 * ℓ : ℕ) : ℝ≥0∞) μ) →
    ∀ᵐ x ∂μ, ∃ L : ℂ, Tendsto (fun N : ℕ =>
      (N : ℝ)⁻¹ • ∑ n ∈ Finset.range (N + 1),
        ArithmeticFunction.vonMangoldt n • ergodicSequence T P f (n : ℤ) x)
      atTop (𝓝 L)

/-- Applying the external weighted pointwise theorem to
(P_i(t-1)) yields the unrestricted pointwise input in Theorem 1.4. -/
theorem ae_unrestrictedPrimeAverage_tendsto [IsProbabilityMeasure μ]
    (hPNT : PrimeNumberTheorem) (hMWW : MirekWanWrightPointwise X)
    (T : ProbabilitySystem X μ) {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ)
    (hP : ErgodicPolynomialFamily P)
    (f : Fin ℓ → X → ℂ) (hf : ∀ i, MemLp (f i) ∞ μ) :
    ∀ᵐ x ∂μ, ∃ L : ℂ,
      Tendsto (primeAverage (fun p => ergodicSequence T P f ((p : ℤ) - 1) x))
        atTop (𝓝 L) := by
  let Q (i : Fin ℓ) := (P i).comp (Polynomial.X - Polynomial.C 1)
  have h_degree (i : Fin ℓ) : (Q i).natDegree = (P i).natDegree := by
    change ((P i).comp (Polynomial.X - Polynomial.C (1 : ℤ))).natDegree = _
    rw [Polynomial.natDegree_comp, Polynomial.natDegree_X_sub_C, mul_one]
  have h_Qpos (i : Fin ℓ) : 0 < (Q i).natDegree := by
    rw [h_degree]
    exact (hP.2.1 i).1
  have h_Qmono : StrictMono (fun i => (Q i).natDegree) := by
    intro i j hij
    simp only [h_degree]
    exact hP.2.2 hij
  have h_e (n : ℕ) (x : X) :
      ergodicSequence T Q f (n : ℤ) x = ergodicSequence T P f ((n : ℤ) - 1) x := by
    simp [ergodicSequence, Q, Polynomial.eval_comp]
  obtain ⟨B, _, hb⟩ := ae_ergodicSequence_bounded T P f hf
  filter_upwards [hb, hMWW μ T hP.1 Q h_Qpos h_Qmono f
    (fun i => (hf i).mono_exponent le_top)] with x hx hL
  obtain ⟨L, hL⟩ := hL
  refine ⟨L, tendsto_primeAverage_of_tendsto_mangoldt hPNT (fun n => hx _) ?_⟩
  simpa only [h_e] using hL


/-- Moving the scalar mean inside the weight in Proposition 7.1. -/
theorem mangoldtAverage_sub_mul_eq_centered (T : ProbabilitySystem X μ)
    {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ) (f : Fin ℓ → X → ℂ)
    (w : ℤ → ℂ) (m : ℂ) (H : ℕ) (x : X) :
    mangoldtAverage T P f w H x - m * mangoldtAverage T P f (fun _ => 1) H x =
      mangoldtAverage T P f (fun n => w n - m) H x := by
  unfold mangoldtAverage
  rw [← mul_div_assoc, ← sub_div, Finset.mul_sum, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  ring

end NilBohr
