import NilBohr.LiteratureAssembly
import Mathlib.Data.Finset.Sort

/-! Proposition 7.1 in the stated order-independent formulation. -/

open MeasureTheory Polynomial
open scoped BigOperators ENNReal NNReal

namespace NilBohr

universe u

/-- A list of distinct positive-degree polynomials can be ordered by degree
through a permutation of its original indices. -/
theorem exists_ordered_ergodic_polynomial_family {ℓ : ℕ} (hℓ : 0 < ℓ)
    (P : Fin ℓ → Polynomial ℤ)
    (hP : ∀ i, 0 < (P i).natDegree ∧ (P i).coeff 0 = 0)
    (hDistinct : Function.Injective (fun i => (P i).natDegree)) :
    ∃ σ : Equiv.Perm (Fin ℓ), ErgodicPolynomialFamily (P ∘ σ) := by
  classical
  let degree (i : Fin ℓ) := (P i).natDegree
  let degrees : Finset ℕ := Finset.univ.image degree
  have hCard : degrees.card = ℓ := by
    simp only [degrees, Finset.card_image_of_injective _ (show Function.Injective degree from hDistinct), Finset.card_univ,
      Fintype.card_fin]
  let d (i : Fin ℓ) : degrees := ⟨degree i, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  have hBij : Function.Bijective d := by
    constructor
    · intro i j h
      exact hDistinct (congrArg Subtype.val h)
    · intro k
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp k.property
      exact ⟨i, Subtype.ext hi⟩
  let e := Equiv.ofBijective d hBij
  let increasing := degrees.orderIsoOfFin hCard
  let σ := increasing.toEquiv.trans e.symm
  have hDegree (i : Fin ℓ) : (P (σ i)).natDegree = (increasing i : ℕ) := by
    change ((e (σ i) : degrees) : ℕ) = (increasing i : ℕ)
    simp [σ]
  refine ⟨σ, hℓ, fun i => hP (σ i), ?_⟩
  intro i j hij
  simpa only [Function.comp_apply, hDegree] using
    (increasing.strictMono hij : increasing i < increasing j)

private theorem ergodicSequence_permute {X : Type u} [MeasurableSpace X] {μ : Measure X}
    (T : ProbabilitySystem X μ) {ℓ : ℕ} (σ : Equiv.Perm (Fin ℓ))
    (P : Fin ℓ → Polynomial ℤ) (f : Fin ℓ → X → ℂ) :
    ergodicSequence T (P ∘ σ) (f ∘ σ) = ergodicSequence T P f := by
  funext n x
  exact Equiv.prod_comp σ (fun i => f i ((T.transform ^ (P i).eval n) x))

private theorem mangoldtAverage_permute {X : Type u} [MeasurableSpace X] {μ : Measure X}
    (T : ProbabilitySystem X μ) {ℓ : ℕ} (σ : Equiv.Perm (Fin ℓ))
    (P : Fin ℓ → Polynomial ℤ) (f : Fin ℓ → X → ℂ) (w : ℤ → ℂ) (H : ℕ) :
    mangoldtAverage T (P ∘ σ) (f ∘ σ) w H = mangoldtAverage T P f w H := by
  unfold mangoldtAverage
  rw [ergodicSequence_permute T σ P f]

private theorem prod_eLpNorm_permute {X : Type u} [MeasurableSpace X] {μ : Measure X}
    {ℓ : ℕ} (σ : Equiv.Perm (Fin ℓ)) (f : Fin ℓ → X → ℂ) :
    (∏ i, (eLpNorm ((f ∘ σ) i) ∞ μ).toReal) = ∏ i, (eLpNorm (f i) ∞ μ).toReal :=
  Equiv.prod_comp σ (fun i => (eLpNorm (f i) ∞ μ).toReal)

/-- Proposition 7.1 for distinct positive degrees in any order. The $L^1$
constant is selected before the probability system, inputs and scale. The
pointwise conclusion includes both the Mangoldt and ordinary prime limits. -/
theorem smoothErgodicComparison_of_prime_model_distinct_degrees
    {c₀ : ℝ} (hc₀ : 0 < c₀) (hc₁ : c₀ < 1 / 11)
    (hBanks : BanksRealZeroBound) (hAmbient : KMTTAmbientPrimeModel c₀)
    (hMertens : MertensIntervalProductBound) (hSieve : FundamentalSieveLemma)
    (hGT : GreenTaoQuantitativeLeibman) (hTer : TeravainenFixedFamily)
    {α β : ℝ} (hα : BadlyApproximable α) (hβ : AdmissibleBeta β)
    {ℓ : ℕ} (hℓ : 0 < ℓ) (P : Fin ℓ → Polynomial ℤ)
    (hP : ∀ i, 0 < (P i).natDegree ∧ (P i).coeff 0 = 0)
    (hDistinct : Function.Injective (fun i => (P i).natDegree))
    (F : Circle → ℂ) {κ : ℝ≥0} (hF : LipschitzWith κ F) :
    (∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type u} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
        (T : ProbabilitySystem X μ) (f : Fin ℓ → X → ℂ), (∀ i, MemLp (f i) ∞ μ) →
        ∀ H : ℕ, 2 ≤ H →
          let w := fun n : ℤ => F (heisenbergPhase α β n : Circle) - circleMean F
          (eLpNorm (mangoldtAverage T P f w H) 1 μ).toReal ≤
            C * (Real.log H)^(-A) * ∏ i, (eLpNorm (f i) ∞ μ).toReal) ∧
    ∀ {X : Type u} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
      (T : ProbabilitySystem X μ) (f : Fin ℓ → X → ℂ), (∀ i, MemLp (f i) ∞ μ) →
        SmoothErgodicComparison T P f (heisenbergPhase α β) F := by
  obtain ⟨σ, hOrdered⟩ := exists_ordered_ergodic_polynomial_family hℓ P hP hDistinct
  let Q := P ∘ σ
  let last : Fin ℓ := ⟨ℓ - 1, by omega⟩
  let d := (Q last).natDegree
  have hd : 0 < d := (hOrdered.2.1 last).1
  have hDeg (i : Fin ℓ) : (Q i).natDegree ≤ d :=
    hOrdered.2.2.monotone (by change i.val ≤ ℓ - 1; have := i.isLt; omega)
  have hTop : ∃ i, (Q i).natDegree = d := ⟨last, rfl⟩
  let V := heisenbergPhase α β
  let hLit := PrimePhaseLiteratureInputs.of_analytic_inputs hBanks hAmbient hMertens hSieve hGT
  have hPhase : PrimeLocalPhase d V F :=
    heisenbergPrimeLocalPhase_of_literature hc₀ hc₁ hLit α β hα hβ d hd F ⟨κ, hF⟩
  have hPNT := primeNumberTheorem_of_prime_model hc₀ hc₁ hBanks hAmbient hMertens hSieve
  constructor
  · intro A hA
    obtain ⟨W, hW⟩ := (isCompact_univ (X := Circle)).exists_bound_of_continuousOn
      ((hF.continuous.sub continuous_const :
        Continuous (fun x => F x - circleMean F)).continuousOn)
    obtain ⟨C, hC, hBound⟩ := mangoldt_L1_log_decay_of_primeLocalPhase hTer hd Q hOrdered
      hDeg hTop V F hPhase hA (W := max W 0) (le_max_right _ _)
      (fun n => (hW _ (Set.mem_univ _)).trans (le_max_left _ _))
    refine ⟨C, hC, ?_⟩
    intro X _ μ _ T f hf H hH
    obtain ⟨hNorm, hRate⟩ := hBound T (f ∘ σ) (fun i => hf (σ i)) H hH
    simpa only [Q, V, mangoldtAverage_permute, prod_eLpNorm_permute] using
      hNorm.trans_le hRate
  · intro X _ μ _ T f hf
    have h := smoothErgodicComparison_of_primeLocalPhase hTer hPNT hd Q hOrdered hDeg hTop
      V F hF.continuous hPhase T (f ∘ σ) (fun i => hf (σ i))
    simpa only [SmoothErgodicComparison, Q, V, mangoldtAverage_permute,
      ergodicSequence_permute, prod_eLpNorm_permute] using h

end NilBohr
