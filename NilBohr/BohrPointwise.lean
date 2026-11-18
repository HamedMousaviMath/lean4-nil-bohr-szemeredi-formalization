import NilBohr.Rotations
import NilBohr.ErgodicLimits

/-! Linear twists of polynomial prime averages and convergence under
approximation by fixed weights. -/

namespace NilBohr

open Filter MeasureTheory Polynomial
open scoped BigOperators Topology ENNReal

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- The prime frequency is applied to the shifted variable (p-1). -/
noncomputable def bohrPrimeMode (ω : ℝ) (p : ℕ) : ℂ :=
  phase (ω * ((p : ℝ) - 1))

/-- Multiplication by a deterministic prime weight, with the paper's common
prime-count normalizer. -/
noncomputable def weightedPrimeAverage (w a : ℕ → ℂ) (N : ℕ) : ℂ :=
  primeAverage (fun p => w p * a p) N

private theorem linear_eval (Q : Polynomial ℤ) (hQ : Q.natDegree = 1)
    (hzero : Q.coeff 0 = 0) :
    ∃ a : ℤ, a ≠ 0 ∧ ∀ n : ℤ, Q.eval n = a * n := by
  have ha : Q.coeff 1 ≠ 0 := by
    rw [← hQ, coeff_natDegree, leadingCoeff_ne_zero]
    intro hz
    simp [hz] at hQ
  refine ⟨Q.coeff 1, ha, fun n => ?_⟩
  have h := congrArg (eval n) (Q.as_sum_range' 2 (by omega))
  simpa [Finset.sum_range_succ, hzero] using h

private theorem circleCharacter_ne_zero (t : Circle) : circleCharacter t ≠ 0 := by
  rw [circleCharacter, fourier_apply]
  apply norm_ne_zero_iff.mp
  rw [_root_.Circle.norm_coe]
  exact one_ne_zero

/-- The introductory convergence of `B_N^ω` for each fixed real frequency.
The only pointwise input is Mirek–Wan–Wright on the enlarged probability
system. The second circle coordinate has trivial rotation. -/
theorem ae_bohrPrimeMode_tendsto [IsProbabilityMeasure μ]
    (hPNT : PrimeNumberTheorem) (hMWW : MirekWanWrightPointwise (X × (Circle × Circle)))
    (T : ProbabilitySystem X μ) {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ)
    (hP : ErgodicPolynomialFamily P) (f : Fin ℓ → X → ℂ)
    (hf : ∀ i, MemLp (f i) ∞ μ) (ω : ℝ) :
    ∀ᵐ x ∂μ, ∃ L : ℂ, Tendsto (weightedPrimeAverage (bohrPrimeMode ω)
      (fun p => ergodicSequence T P f ((p : ℤ) - 1) x)) atTop (𝓝 L) := by
  obtain ⟨d,Q,g,i₁,i₂,hQ,hd₁,_,hg,hgP⟩ := exists_quadratic_completion T P hP f hf
  obtain ⟨a,ha,heval⟩ := linear_eval (Q i₁) hd₁ (hQ.2.1 i₁).2
  let w : ℝ := ω / (a : ℝ)
  have hrot := ae_unrestrictedPrimeAverage_tendsto hPNT hMWW
    (circleRotationExtension T w 0) Q hQ (rotationInputs g i₁ i₂)
    (memLp_rotationInputs g hg i₁ i₂)
  filter_upwards [Measure.ae_ae_of_ae_prod hrot] with x hx
  obtain ⟨t, L, hL⟩ := hx.exists
  let c := circleCharacter t.1 * circleCharacter t.2
  have hc := mul_ne_zero (circleCharacter_ne_zero t.1) (circleCharacter_ne_zero t.2)
  change c ≠ 0 at hc
  let A := weightedPrimeAverage (bohrPrimeMode ω)
    (fun p => ergodicSequence T P f ((p : ℤ) - 1) x)
  have hpoint (p : ℕ) :
      ergodicSequence (circleRotationExtension T w 0)
        Q (rotationInputs g i₁ i₂) ((p : ℤ) - 1) (x,t) =
          c * (bohrPrimeMode ω p * ergodicSequence T P f ((p : ℤ) - 1) x) := by
    rw [ergodicSequence_circleRotationExtension, hgP, zero_mul, add_zero, heval]
    congr 2
    unfold bohrPrimeMode w
    push_cast
    have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
    congr 1
    field_simp
    ring
  have hA : Tendsto (fun N => c * A N) atTop (𝓝 L) := by
    apply hL.congr
    intro N
    simp only [A, weightedPrimeAverage, primeAverage, hpoint, ← Finset.mul_sum, mul_div_assoc]
  refine ⟨c⁻¹ * L, ?_⟩
  simpa only [← mul_assoc, inv_mul_cancel₀ hc, one_mul] using hA.const_mul c⁻¹

/-- Mean absolute approximation of deterministic weights is sufficient for
bounded test sequences. The simultaneous conull set for countably many
approximants is formed by the caller. -/
theorem weightedPrimeAverage_tendsto_of_approximation {w a : ℕ → ℂ}
    (B : ℝ) (hB : 0 ≤ B) (ha : ∀ p, ‖a p‖ ≤ B)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ v : ℕ → ℂ,
      (∃ L : ℂ, Tendsto (weightedPrimeAverage v a) atTop (𝓝 L)) ∧
      ∀ᶠ N in (atTop : Filter ℕ),
        (∑ p ∈ primesThrough N, ‖w p - v p‖) / ((primesThrough N).card : ℝ) < ε) :
    ∃ L : ℂ, Tendsto (weightedPrimeAverage w a) atTop (𝓝 L) := by
  apply cauchySeq_tendsto_of_complete
  apply Metric.cauchySeq_iff.mpr
  intro η hη
  let ε := η / (4 * (B + 1))
  have hε : 0 < ε := div_pos hη (by positivity)
  obtain ⟨v, ⟨L,hL⟩,happrox⟩ := happrox ε hε
  have happroxDist (N : ℕ) :
      dist (weightedPrimeAverage w a N) (weightedPrimeAverage v a N) ≤
        B * ((∑ p ∈ primesThrough N, ‖w p - v p‖) / ((primesThrough N).card : ℝ)) := by
    simp only [dist_eq_norm, weightedPrimeAverage, primeAverage, ← sub_div,
      ← Finset.sum_sub_distrib, ← sub_mul, norm_div, Complex.norm_natCast]
    rw [← mul_div_assoc, Finset.mul_sum]
    exact div_le_div_of_nonneg_right ((norm_sum_le _ _).trans
      (Finset.sum_le_sum fun p _ => by
        rw [norm_mul, mul_comm B]
        exact mul_le_mul_of_nonneg_left (ha p) (norm_nonneg _))) (by positivity)
  have hε' : B * ε ≤ η / 4 := by
    dsimp [ε]
    rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith
  have hev : ∀ᶠ N in (atTop : Filter ℕ),
      dist (weightedPrimeAverage w a N) L < η/2 := by
    filter_upwards [happrox, Metric.tendsto_nhds.mp hL (η/4) (by positivity)] with N hN hn
    have hdist := (happroxDist N).trans ((mul_le_mul_of_nonneg_left hN.le hB).trans hε')
    have htri := dist_triangle (weightedPrimeAverage w a N) (weightedPrimeAverage v a N) L
    linarith
  obtain ⟨N,hN⟩ := eventually_atTop.mp hev
  refine ⟨N, fun m hm n hn => ?_⟩
  have htri := dist_triangle (weightedPrimeAverage w a m) L (weightedPrimeAverage w a n)
  rw [dist_comm L] at htri
  linarith [hN m hm, hN n hn]

/-- A countable sequence of deterministic mean-absolute approximants
suffices to transfer almost-everywhere convergence to the target weight. -/
theorem ae_weightedPrimeAverage_of_approximation
    (T : ProbabilitySystem X μ) {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ)
    (f : Fin ℓ → X → ℂ) (hf : ∀ i, MemLp (f i) ∞ μ)
    {w : ℕ → ℂ} (v : ℕ → ℕ → ℂ) (δ : ℕ → ℝ)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hclose : ∀ j, ∀ᶠ N in (atTop : Filter ℕ),
      (∑ p ∈ primesThrough N, ‖w p - v j p‖) / ((primesThrough N).card : ℝ) ≤ δ j)
    (hlim : ∀ j, ∀ᵐ x ∂μ, ∃ L : ℂ, Tendsto (weightedPrimeAverage (v j)
      (fun p => ergodicSequence T P f ((p : ℤ) - 1) x)) atTop (𝓝 L)) :
    ∀ᵐ x ∂μ, ∃ L : ℂ, Tendsto (weightedPrimeAverage w
      (fun p => ergodicSequence T P f ((p : ℤ) - 1) x)) atTop (𝓝 L) := by
  obtain ⟨B,hB,hseq⟩ := ae_ergodicSequence_bounded T P f hf
  filter_upwards [hseq, ae_all_iff.mpr hlim] with x hx hlimx
  refine weightedPrimeAverage_tendsto_of_approximation B hB (fun p => hx _) (fun ε hε => ?_)
  obtain ⟨j,hj⟩ := (hδ.eventually (gt_mem_nhds hε)).exists
  exact ⟨v j, hlimx j, (hclose j).mono (fun N hN => hN.trans_lt hj)⟩

end NilBohr
