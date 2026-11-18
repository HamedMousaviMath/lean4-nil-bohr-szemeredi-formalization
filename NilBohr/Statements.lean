import NilBohr.Ergodic
import NilBohr.Density

/-! Statement interfaces for the continuing proof. Propositions in this file
are mathematical targets. Defining a target does not prove or assume it. -/

open Filter MeasureTheory Polynomial
open scoped BigOperators ENNReal

namespace NilBohr

def Smooth (q w : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ q → p ≤ w


noncomputable def cramerCutoff (c₀ : ℝ) (N : ℕ) : ℕ :=
  ⌈Real.exp ((Real.log N) ^ c₀)⌉₊

def RelativeModulus (c₀ cRel : ℝ) (w₀ N q w : ℕ) : Prop :=
  w₀ ≤ w ∧ 0 < q ∧ (w : ℝ) ≤ (Real.log (cramerCutoff c₀ N)) ^ cRel ∧
    8 * (∏ p ∈ primesThrough w, p) ∣ q ∧ Smooth q w ∧ Real.log q ≤ (w : ℝ)^2

noncomputable def selectorWeight (V : ℤ → ℝ) (F : Circle → ℂ) (q : ℕ) (y : ℤ) : ℂ :=
  F ((V ((q : ℤ) * y) : ℝ) : Circle)

/-- Theorem 3.2 for a fixed choice of the Cramér cutoff exponent. -/
def RelativeSelectorComparison (c₀ C : ℝ) (d ℓ : ℕ) (V : ℤ → ℝ)
    (F : Circle → ℂ) : Prop :=
  ∃ (cRel η A : ℝ) (w₀ N₀ : ℕ), 0 < cRel ∧ 0 < η ∧ 0 < A ∧ 16 ≤ w₀ ∧
    ∀ (N q w : ℕ), N₀ ≤ N → RelativeModulus c₀ cRel w₀ N q w →
      let M := parameterLength N q d
      ∀ (P : Fin (ℓ + 1) → Polynomial ℤ), FixedPolynomialFamily P →
      (P (Fin.last ℓ)).natDegree = d → (∀ i, i ≠ 0 → HasCoefficients C q (P i)) →
      ∀ f : Fin (ℓ + 1) → ℤ → ℂ,
        (∀ i, OneBoundedOn (positiveInterval N) (f i)) →
        (∀ i, SupportedOn (positiveInterval N) (f i)) →
        ‖countingForm N M (positiveInterval N) P
            (fun y => (lambdaModulus q y : ℂ) * selectorWeight V F q y) f -
          circleMean F * countingForm N M (positiveInterval N) P (fun _ => 1) f‖
            ≤ A * (w : ℝ) ^ (-η)

/-- Proposition 6.2, at the stated parameter range and fixed data. Natural B
suffices, since the progression exponent is an integer. -/
def PrimeLocalPhase (d : ℕ) (V : ℤ → ℝ) (F : Circle → ℂ) : Prop :=
  ∀ (A K L : ℝ) (B : ℕ), 0 < A → 0 < K → 0 < L →
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ (N q : ℕ), N₀ ≤ N →
      1 ≤ q → (q : ℝ) ≤ (Real.log N)^L →
      let M := parameterLength N q d
      ∀ (l r u : ℤ) (b : ℕ), b ≤ B →
        Finset.Icc l r ⊆ positiveInterval M →
        (M : ℝ) * (Real.log N)^(-K) ≤ ((Finset.Icc l r).card : ℝ) →
        let P := localProgression l r u (q^b)
        P.Nonempty ∧
          phaseNorm (d + 1) P (fun y =>
            (lambdaModulus q y : ℂ) * (selectorWeight V F q y - circleMean F)) ≤
            C * (Real.log N)^(-A)

/-- All three claims of Proposition 7.1 for a fixed family, system and inputs. -/
def SmoothErgodicComparison {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (T : ProbabilitySystem X μ) {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ)
    (f : Fin ℓ → X → ℂ) (V : ℤ → ℝ) (F : Circle → ℂ) : Prop :=
  let w := fun n : ℤ => F (V n : Circle) - circleMean F
  (∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ H : ℕ, 2 ≤ H →
    (eLpNorm (mangoldtAverage T P f w H) 1 μ).toReal ≤ C * (Real.log H)^(-A) *
        ∏ i, (eLpNorm (f i) ∞ μ).toReal) ∧
  (∀ᵐ x ∂μ, Tendsto (fun H => mangoldtAverage T P f w H x) atTop (nhds 0)) ∧
  (∀ᵐ x ∂μ, Tendsto (fun H => primeAverage
    (fun p => w ((p : ℤ) - 1) * ergodicSequence T P f ((p : ℤ) - 1) x) H)
      atTop (nhds 0))

end NilBohr
