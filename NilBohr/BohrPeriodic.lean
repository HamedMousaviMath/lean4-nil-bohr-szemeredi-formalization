import NilBohr.BohrWeights
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Data.Nat.Totient

/-! Fixed periodic prime weights by exact finite Fourier inversion. -/

namespace NilBohr

open Filter MeasureTheory Polynomial
open scoped BigOperators Topology ENNReal ZMod

/-- A trigonometric polynomial extending a function on the residue classes,
with input shifted by one so its samples are at `p - 1`. -/
noncomputable def periodicBohrWeight {q : ℕ} [NeZero q] (w : ZMod q → ℂ) :
    C(Circle, ℂ) :=
  ⟨fun t => (q : ℂ)⁻¹ * ∑ k : ZMod q,
      fourier (T := 1) (k.val : ℤ) (t + ((1 / (q : ℝ) : ℝ) : Circle)) * ZMod.dft w k,
    continuous_const.mul (continuous_finset_sum _ fun k _ =>
      ((fourier (T := 1) (k.val : ℤ)).continuous.comp
        (continuous_id.add continuous_const)).mul continuous_const)⟩

theorem periodicBohrWeight_eq {q : ℕ} [NeZero q] (w : ZMod q → ℂ) (p : ℕ) :
    periodicBohrWeight w (((1 / (q : ℝ)) * ((p : ℝ) - 1) : ℝ) : Circle) =
      w (p : ZMod q) := by
  have hshift : ((1 / (q : ℝ)) * ((p : ℝ) - 1) : ℝ) + 1 / (q : ℝ) =
      (p : ℝ) / (q : ℝ) := by ring
  have hchar (k : ZMod q) :
      fourier (T := 1) (k.val : ℤ) (ZMod.toAddCircle (p : ZMod q)) =
        ZMod.stdAddChar (k * (p : ZMod q)) := by
    rw [fourier_apply, ZMod.stdAddChar_apply, ← map_zsmul, zsmul_eq_mul]
    simp [ZMod.toCircle, ZMod.natCast_zmod_val, AddCircle.toCircle_addChar]
  simp only [periodicBohrWeight, ContinuousMap.coe_mk, ← AddCircle.coe_add, hshift,
    ← ZMod.toAddCircle_natCast, hchar]
  simpa only [ZMod.invDFT_apply, smul_eq_mul] using
    congrFun ((ZMod.dft (N := q) (E := ℂ)).symm_apply_apply w) (p : ZMod q)

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Every fixed periodic multiplier has a pointwise limit with prime-count
normalization. This uses no prime number theorem in progressions. -/
theorem ae_periodicPrimeAverage_tendsto [IsProbabilityMeasure μ]
    (hPNT : PrimeNumberTheorem) (hMWW : MirekWanWrightPointwise (X × (Circle × Circle)))
    (T : ProbabilitySystem X μ) {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ)
    (hP : ErgodicPolynomialFamily P) (f : Fin ℓ → X → ℂ)
    (hf : ∀ i, MemLp (f i) ∞ μ) {q : ℕ} [NeZero q] (w : ZMod q → ℂ) :
    ∀ᵐ x ∂μ, ∃ L : ℂ, Tendsto
      (weightedPrimeAverage (fun p => w (p : ZMod q))
        (fun p => ergodicSequence T P f ((p : ℤ) - 1) x)) atTop (𝓝 L) := by
  let F : C(BohrTorus 1, ℂ) :=
    ⟨fun t => periodicBohrWeight w (t 0), (periodicBohrWeight w).continuous.comp (continuous_apply 0)⟩
  simpa only [F, ContinuousMap.coe_mk, bohrPrimePoint, periodicBohrWeight_eq] using
    ae_continuousBohrPrimeAverage_tendsto hPNT hMWW T P hP f hf
      (fun _ : Fin 1 => 1 / (q : ℝ)) F

/-- The primes selected by a fixed predicate, including equalities modulo
a fixed modulus and finite simultaneous Bohr conditions. -/
noncomputable def primesSatisfyingThrough (s : ℕ → Prop) (N : ℕ) : Finset ℕ := by
  classical
  exact (primesThrough N).filter s

noncomputable def predicatePrimeDensity (s : ℕ → Prop) (N : ℕ) : ℝ :=
  ((primesSatisfyingThrough s N).card : ℝ) / (primesThrough N).card

noncomputable def predicatePrimeAverage (s : ℕ → Prop) (a : ℕ → ℂ) (N : ℕ) : ℂ :=
  (∑ p ∈ primesSatisfyingThrough s N, a p) / ((primesSatisfyingThrough s N).card : ℂ)

noncomputable def primePredicateWeight (s : ℕ → Prop) (p : ℕ) : ℂ := by
  classical
  exact if s p then 1 else 0

theorem weightedPrimeAverage_predicate_eq (s : ℕ → Prop) (a : ℕ → ℂ) (N : ℕ) :
    weightedPrimeAverage (primePredicateWeight s) a N =
      (∑ p ∈ primesSatisfyingThrough s N, a p) / ((primesThrough N).card : ℂ) := by
  classical
  unfold weightedPrimeAverage primeAverage primesSatisfyingThrough
  rw [Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : s p <;> simp [primePredicateWeight, hp]

theorem predicatePrimeDensity_eq_weighted_one (s : ℕ → Prop) (N : ℕ) :
    (predicatePrimeDensity s N : ℂ) =
      weightedPrimeAverage (primePredicateWeight s) (fun _ => 1) N := by
  rw [weightedPrimeAverage_predicate_eq]
  simp [predicatePrimeDensity]

theorem predicatePrimeAverage_eq_div_density (s : ℕ → Prop) (a : ℕ → ℂ) (N : ℕ) :
    predicatePrimeAverage s a N =
      weightedPrimeAverage (primePredicateWeight s) a N / (predicatePrimeDensity s N : ℂ) := by
  rw [weightedPrimeAverage_predicate_eq]
  by_cases h : (primesThrough N).card = 0
  · have hsub : primesSatisfyingThrough s N ⊆ primesThrough N := by
      classical
      exact Finset.filter_subset _ _
    have hs := Nat.eq_zero_of_le_zero (h ▸ Finset.card_le_card hsub)
    simp [predicatePrimeAverage, predicatePrimeDensity, h, hs]
  · have hc : ((primesThrough N).card : ℂ) ≠ 0 := by exact_mod_cast h
    simp [predicatePrimeAverage, predicatePrimeDensity, div_div_div_cancel_right₀ hc]

/-- Normalization by the number of selected primes, once their relative
density has a positive limit. -/
theorem ae_predicatePrimeAverage_tendsto {s : ℕ → Prop} {d : ℝ}
    (hd : 0 < d) (hD : Tendsto (predicatePrimeDensity s) atTop (𝓝 d))
    (a : X → ℕ → ℂ)
    (h : ∀ᵐ x ∂μ, ∃ L : ℂ, Tendsto (weightedPrimeAverage (primePredicateWeight s) (a x))
      atTop (𝓝 L)) :
    ∀ᵐ x ∂μ, ∃ L : ℂ, Tendsto (predicatePrimeAverage s (a x)) atTop (𝓝 L) := by
  filter_upwards [h] with x hx
  obtain ⟨L,hL⟩ := hx
  have hD' := (Complex.continuous_ofReal.tendsto d).comp hD
  have hd' : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd.ne'
  exact ⟨L / (d : ℂ), (hL.div hD' hd').congr
    (fun N => (predicatePrimeAverage_eq_div_density s (a x) N).symm)⟩

/-- The fixed-modulus prime number theorem in reduced classes, in its count
form at the scale `N / log N`. There is no uniformity in the modulus. -/
def PrimeNumberTheoremInProgressions : Prop :=
  ∀ (q a : ℕ), 0 < q → Nat.Coprime a q →
    Tendsto (fun N : ℕ => ((primesSatisfyingThrough (fun p => p ≡ a [MOD q]) N).card : ℝ) *
      Real.log (N : ℝ) / (N : ℝ)) atTop (𝓝 ((q.totient : ℝ)⁻¹))

theorem primeCongruenceDensity_tendsto (hPNT : PrimeNumberTheorem)
    (hAP : PrimeNumberTheoremInProgressions) {q a : ℕ} (hq : 0 < q) (ha : a.Coprime q) :
    Tendsto (predicatePrimeDensity (fun p => p ≡ a [MOD q])) atTop (𝓝 ((q.totient : ℝ)⁻¹)) := by
  have h := (hAP q a hq ha).div hPNT.count one_ne_zero
  simp only [div_one] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  have hN' : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hN'
  have hN₀ : (N : ℝ) ≠ 0 := by positivity
  simp only [Pi.div_apply, predicatePrimeDensity]
  rw [div_div_div_cancel_right₀ hN₀, mul_div_mul_right _ _ hlog.ne']

/-- Fixed congruence restrictions at the common prime-count normalization,
for any residue class and positive modulus. -/
theorem ae_primeAverage_congruence_tendsto [IsProbabilityMeasure μ]
    (hPNT : PrimeNumberTheorem) (hMWW : MirekWanWrightPointwise (X × (Circle × Circle)))
    (T : ProbabilitySystem X μ) {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ)
    (hP : ErgodicPolynomialFamily P) (f : Fin ℓ → X → ℂ)
    (hf : ∀ i, MemLp (f i) ∞ μ) (q a : ℕ) (hq : 0 < q) :
    ∀ᵐ x ∂μ, ∃ L : ℂ, Tendsto
      (weightedPrimeAverage (primePredicateWeight (fun p => p ≡ a [MOD q]))
        (fun p => ergodicSequence T P f ((p : ℤ) - 1) x)) atTop (𝓝 L) := by
  classical
  letI : NeZero q := ⟨hq.ne'⟩
  let w (z : ZMod q) : ℂ := if z = (a : ZMod q) then 1 else 0
  have he : (fun p : ℕ => w (p : ZMod q)) =
      primePredicateWeight (fun p => p ≡ a [MOD q]) := by
    funext p
    by_cases hp : p ≡ a [MOD q]
    · simp [w, ZMod.eq_iff_modEq_nat, primePredicateWeight, hp]
    · simp [w, ZMod.eq_iff_modEq_nat, primePredicateWeight, hp]
  rw [← he]
  exact ae_periodicPrimeAverage_tendsto hPNT hMWW T P hP f hf w

/-- Fixed reduced congruence restrictions with selected-prime count
normalization. -/
theorem ae_primeAverage_reduced_congruence_tendsto [IsProbabilityMeasure μ]
    (hPNT : PrimeNumberTheorem) (hAP : PrimeNumberTheoremInProgressions)
    (hMWW : MirekWanWrightPointwise (X × (Circle × Circle)))
    (T : ProbabilitySystem X μ) {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ)
    (hP : ErgodicPolynomialFamily P) (f : Fin ℓ → X → ℂ)
    (hf : ∀ i, MemLp (f i) ∞ μ) {q a : ℕ} (hq : 0 < q) (ha : a.Coprime q) :
    ∀ᵐ x ∂μ, ∃ L : ℂ, Tendsto
      (predicatePrimeAverage (fun p => p ≡ a [MOD q])
        (fun p => ergodicSequence T P f ((p : ℤ) - 1) x)) atTop (𝓝 L) :=
  ae_predicatePrimeAverage_tendsto
    (inv_pos.mpr (Nat.cast_pos.mpr (Nat.totient_pos.mpr hq)))
    (primeCongruenceDensity_tendsto hPNT hAP hq ha) _
    (ae_primeAverage_congruence_tendsto hPNT hMWW T P hP f hf q a hq)

end NilBohr
