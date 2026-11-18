import Mathlib
import NilBohr.Arithmetic

/-! Conventions for the paper's weighted counts and recurrence statements. -/

open scoped BigOperators
open Filter Polynomial

namespace NilBohr

abbrev Circle := AddCircle (1 : ℝ)

noncomputable def phase (t : ℝ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))

/-- An oriented open arc of length strictly between zero and one, including arcs
which cross the endpoint of a fundamental interval. -/
structure OpenArc where
  start : ℝ
  length : ℝ
  length_pos : 0 < length
  length_lt_one : length < 1

def OpenArc.carrier (J : OpenArc) : Set Circle :=
  (fun t : ℝ => (t : Circle)) '' Set.Ioo J.start (J.start + J.length)

def OpenArc.Contains (J : OpenArc) (t : ℝ) : Prop := (t : Circle) ∈ J.carrier

noncomputable def OpenArc.indicator (J : OpenArc) (t : ℝ) : ℝ := by
  classical
  exact if J.Contains t then 1 else 0

/-- Equivalent to strict positivity of the infimum in equation (5). -/
def BadlyApproximable (α : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ m : ℕ, 0 < m → c ≤ (m : ℝ) * ‖(((m : ℝ) * α : ℝ) : Circle)‖

noncomputable def denominatorScale (r : ℕ) : ℝ :=
  Real.exp (Real.exp (Real.sqrt (Real.log (r : ℝ))))

def AdmissibleBeta (β : ℝ) : Prop :=
  0 < β ∧ β < 1 ∧
  ∃ a r : ℕ → ℕ,
    StrictMono r ∧
    StrictMono (fun j => (a j : ℝ) / (r j : ℝ)) ∧
    (∀ j, (r j).Prime ∧ 0 < a j ∧ a j < r j) ∧
    ∃ c C D : ℝ, 0 < c ∧ 0 < C ∧ 0 < D ∧
      ∀ j, c * denominatorScale (r j) ≤ (r (j + 1) : ℝ) ∧
        (r (j + 1) : ℝ) ≤ C * denominatorScale (r j) ∧
        0 < β - (a j : ℝ) / (r j : ℝ) ∧
        β - (a j : ℝ) / (r j : ℝ) ≤ D / (r (j + 1) : ℝ)

def positiveInterval (N : ℕ) : Finset ℤ := Finset.Icc 1 (N : ℤ)

noncomputable def spatialInterval (C : ℝ) (N : ℕ) : Finset ℤ :=
  Finset.Icc ⌈-C * (N : ℝ)⌉ ⌊C * (N : ℝ)⌋

noncomputable def setDensity (A : Finset ℤ) (N : ℕ) : ℝ := (A.card : ℝ) / N

def FixedPolynomialFamily {ℓ : ℕ} (P : Fin (ℓ + 1) → Polynomial ℤ) : Prop :=
  0 < ℓ ∧ P 0 = 0 ∧ (∀ i, (P i).coeff 0 = 0) ∧
    StrictMono (fun i => (P i).natDegree)

def HasCoefficients (C : ℝ) (q : ℕ) (P : Polynomial ℤ) : Prop :=
  1 ≤ C ∧ 0 < q ∧ 0 < P.natDegree ∧ P.coeff 0 = 0 ∧
  (∀ j : ℕ, 1 ≤ j → j < P.natDegree →
    |(P.coeff j : ℝ)| ≤ C * |(P.leadingCoeff : ℝ)|) ∧
  ∃ a : ℤ, 0 < |(a : ℝ)| ∧ |(a : ℝ)| ≤ C ∧
    P.leadingCoeff = a * (q : ℤ) ^ (P.natDegree - 1)

/-- Rescaling an integral family of fixed coefficients supplies the `(C,q)`
coefficient bounds required by the density increment. -/
theorem HasCoefficients.rescale {C : ℝ} {q : ℕ} {P : Polynomial ℤ}
    (hP : HasCoefficients C 1 P) (hq : 0 < q) :
    HasCoefficients C q (rescalePolynomial (q : ℤ) P) := by
  rcases hP with ⟨hC, _, hdegree, _, hsmall, a, ha, hCa, hlead⟩
  let Q := rescalePolynomial (q : ℤ) P
  have hqZ : (q : ℤ) ≠ 0 := by omega
  have hqR : 1 ≤ (q : ℝ) := by exact_mod_cast hq
  have hQ : Q.natDegree = P.natDegree := natDegree_rescalePolynomial _ _ hqZ
  have hcoef (j : ℕ) (hj : 1 ≤ j) : Q.coeff j = P.coeff j * (q : ℤ)^(j-1) := by
    cases j with
    | zero => omega
    | succ j => simpa [Q] using coeff_succ_rescalePolynomial (q : ℤ) P j
  have hQlead : Q.leadingCoeff = P.leadingCoeff * (q : ℤ)^(P.natDegree-1) := by
    rw [← Polynomial.coeff_natDegree, hQ, hcoef _ hdegree, Polynomial.coeff_natDegree]
  have hleadR : (Q.leadingCoeff : ℝ) = (P.leadingCoeff : ℝ) * (q : ℝ)^(P.natDegree-1) := by
    exact_mod_cast hQlead
  change HasCoefficients C q Q
  refine ⟨hC, hq, by simpa only [hQ] using hdegree, coeff_zero_rescalePolynomial _ P,
    ?_, a, ha, hCa, ?_⟩
  · intro j hj hsmallDegree
    rw [hQ] at hsmallDegree
    have hcoefR : (Q.coeff j : ℝ) = (P.coeff j : ℝ) * (q : ℝ)^(j-1) := by
      exact_mod_cast hcoef j hj
    rw [hcoefR, hleadR, abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (q : ℝ)^(j-1)),
      abs_of_nonneg (by positivity : 0 ≤ (q : ℝ)^(P.natDegree-1))]
    calc
      |(P.coeff j : ℝ)| * (q : ℝ)^(j-1) ≤
          (C * |(P.leadingCoeff : ℝ)|) * (q : ℝ)^(j-1) := by
        gcongr
        exact hsmall j hj hsmallDegree
      _ ≤ (C * |(P.leadingCoeff : ℝ)|) * (q : ℝ)^(P.natDegree-1) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hqR (by omega))
          (mul_nonneg (by linarith) (abs_nonneg _))
      _ = C * (|(P.leadingCoeff : ℝ)| * (q : ℝ)^(P.natDegree-1)) := by ring
  · simp only [Nat.cast_one, one_pow, mul_one] at hlead
    rw [hQlead, hQ, hlead]

noncomputable def parameterLength (N q d : ℕ) : ℕ :=
  ⌊((N : ℝ) / (q : ℝ) ^ (d - 1)) ^ ((d : ℝ)⁻¹)⌋₊

def selectedPrime (V : ℤ → ℝ) (J : OpenArc) (p : ℕ) : Prop :=
  p.Prime ∧ J.Contains (V ((p : ℤ) - 1))

/-- Integer spatial coordinates preserve negative shifts without truncation. -/
def ContainsConfiguration {ℓ : ℕ} (A : Finset ℤ) (P : Fin (ℓ + 1) → Polynomial ℤ)
    (selector : ℕ → Prop) : Prop :=
  ∃ (x : ℤ) (p : ℕ), p.Prime ∧ selector p ∧
    (∀ i, x + (P i).eval ((p : ℤ) - 1) ∈ A) ∧
    Function.Injective (fun i => x + (P i).eval ((p : ℤ) - 1))

def RecurrenceConclusion {ℓ : ℕ} (P : Fin (ℓ + 1) → Polynomial ℤ)
    (selector : ℕ → Prop) : Prop :=
  ∃ κ : ℝ, 0 < κ ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ A : Finset ℤ, A ⊆ positiveInterval N →
      (N : ℝ) * (Real.log N) ^ (-κ) ≤ (A.card : ℝ) →
      ContainsConfiguration A P selector

/-- This proposition specifies Theorem 1.2. -/
def HeisenbergRecurrence : Prop :=
  ∀ {ℓ : ℕ} (P : Fin (ℓ + 1) → Polynomial ℤ), FixedPolynomialFamily P →
    ∀ (α β : ℝ), BadlyApproximable α → AdmissibleBeta β → ∀ J : OpenArc,
      RecurrenceConclusion P (fun p => J.Contains (heisenbergPhase α β ((p : ℤ) - 1)))

/-- Corollary 1.3, with the same quantifiers and the bracket selector. -/
def BracketRecurrence : Prop :=
  ∀ {ℓ : ℕ} (P : Fin (ℓ + 1) → Polynomial ℤ), FixedPolynomialFamily P →
    ∀ (α β : ℝ), BadlyApproximable α → AdmissibleBeta β → ∀ J : OpenArc,
      RecurrenceConclusion P (fun p => J.Contains (bracketPhase α β ((p : ℤ) - 1)))

/-- The spatial window only truncates the base coordinate. If the first
input vanishes outside the window and its shift is zero, the omitted terms vanish. -/
noncomputable def countingForm {k : ℕ} (N M : ℕ) (X : Finset ℤ)
    (P : Fin k → Polynomial ℤ) (v : ℤ → ℂ) (f : Fin k → ℤ → ℂ) : ℂ :=
  (∑ x ∈ X, ∑ y ∈ positiveInterval M, v y * ∏ i, f i (x + (P i).eval y)) /
    ((N : ℂ) * (M : ℂ))

noncomputable def lambdaModulus (q : ℕ) (y : ℤ) : ℝ :=
  (q.totient : ℝ) / q * ArithmeticFunction.vonMangoldt ((q : ℤ) * y + 1).toNat

noncomputable def phaseAverage (I : Finset ℤ) (v : ℤ → ℂ) (φ : Polynomial ℝ) : ℂ :=
  (∑ y ∈ I, v y * phase (-(φ.eval (y : ℝ)))) / (I.card : ℂ)

noncomputable def phaseNorm (s : ℕ) (I : Finset ℤ) (v : ℤ → ℂ) : ℝ :=
  sSup {a : ℝ | ∃ φ : Polynomial ℝ, φ.natDegree < s ∧ a = ‖phaseAverage I v φ‖}

def localProgression (a b u : ℤ) (m : ℕ) : Finset ℤ :=
  (Finset.Icc a b).filter (fun y => Int.ModEq (m : ℤ) y u)

noncomputable def localPhaseNorm (d M q B : ℕ) (A₁ A₂ ρ : ℝ) (v : ℤ → ℂ) : ℝ :=
  sSup {a : ℝ | ∃ (l r u : ℤ) (b : ℕ), b ≤ B ∧
    Finset.Icc l r ⊆ positiveInterval M ∧
    (M : ℝ) * (q : ℝ) ^ (-A₁) * ρ ^ A₂ ≤ ((Finset.Icc l r).card : ℝ) ∧
    (localProgression l r u (q ^ b)).Nonempty ∧
    a = phaseNorm (d + 1) (localProgression l r u (q ^ b)) v}

def OneBoundedOn (I : Finset ℤ) (f : ℤ → ℂ) : Prop :=
  ∀ x ∈ I, ‖f x‖ ≤ 1

def SupportedOn (I : Finset ℤ) (f : ℤ → ℂ) : Prop :=
  ∀ x ∉ I, f x = 0

/-- The assertion of Theorem 4.2, including its two-input refinement. -/
def LocalGeneralizedVonNeumann : Prop :=
  ∀ (C : ℝ) (d ℓ : ℕ), 1 ≤ C → 0 < ℓ →
    ∃ (η A₁ A₂ K : ℝ) (B : ℕ), 0 < η ∧ 0 < A₁ ∧ 0 < A₂ ∧ 0 < K ∧
    ∀ (N q : ℕ), 3 ≤ N → 0 < q → (q : ℝ) ≤ Real.exp ((Real.log N) ^ (1 / 10 : ℝ)) →
      let M := parameterLength N q d
      0 < M →
      ∀ (P : Fin (ℓ + 1) → Polynomial ℤ), FixedPolynomialFamily P →
      (P (Fin.last ℓ)).natDegree = d → (∀ i, i ≠ 0 → HasCoefficients C q (P i)) →
      ∀ (v : ℤ → ℂ) (f : Fin (ℓ + 1) → ℤ → ℂ),
      OneBoundedOn (positiveInterval M) v →
      (∀ i, OneBoundedOn (spatialInterval C N) (f i)) →
      (∀ i, SupportedOn (spatialInterval C N) (f i)) →
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 / 2 →
        ‖countingForm N M (spatialInterval C N) P v f‖ ≤
          K * ((N : ℝ) ^ (-η) + ρ +
            (if ℓ = 1 then phaseNorm (d + 1) (positiveInterval M) v
              else localPhaseNorm d M q B A₁ A₂ ρ v) ^ η)

end NilBohr
