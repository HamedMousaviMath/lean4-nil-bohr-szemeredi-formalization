import NilBohr.Statements
import NilBohr.Selector
import NilBohr.Transference

/-! Explicit interfaces to cited results. This file declares propositions,
not axioms. See docs/ASSUMPTIONS.md for each translation boundary. -/

open Polynomial MeasureTheory
open scoped BigOperators

namespace NilBohr

/-- Teräväinen, arXiv:2401.03174v2, Theorem 4.1, specialized to positive
degrees and zero constant terms as in Section 7 of the manuscript. -/
def TeravainenFixedFamily : Prop :=
  ∀ d : ℕ, 0 < d → ∃ K : ℝ, 1 ≤ K ∧
  ∀ {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ), ErgodicPolynomialFamily P →
    (∀ i, (P i).natDegree ≤ d) → (∃ i, (P i).natDegree = d) →
    ∀ C : ℝ, 1 ≤ C → ∃ A : ℝ, 0 < A ∧
    ∀ (H : ℕ), 0 < H → ∀ (v : ℤ → ℂ) (f : Fin (ℓ + 1) → ℤ → ℂ),
      OneBoundedOn (positiveInterval H) v →
      (∀ i, OneBoundedOn (spatialInterval C (H^d)) (f i)) →
      (∀ i, SupportedOn (spatialInterval C (H^d)) (f i)) →
      ‖countingForm (H^d) H (spatialInterval C (H^d)) (Fin.cases 0 P) v f‖ ≤
        A * ((H : ℝ)⁻¹ + phaseNorm (d + 1) (positiveInterval H) v) ^ (1 / K)

/-- KMTT Proposition 3.3 allows arbitrary weights and finite support sets
with independent spatial and parameter scales. -/
def KMTTWeightedGowers : Prop :=
  ∀ (d ℓ : ℕ) (C : ℝ), 1 ≤ C →
    ∃ (S : ℕ) (A : ℝ), 2 ≤ S ∧ 0 < A ∧
    ∀ (N M : ℕ), 0 < N → 0 < M →
      ∀ (P : Fin ℓ → Polynomial ℤ), (∀ i, (P i).natDegree ≤ d) →
      ∀ (v : ℤ → ℂ) (f : Fin (ℓ + 1) → ℤ → ℂ) (support : Fin (ℓ + 1) → Finset ℤ),
        (∀ i, ((support i).card : ℝ) ≤ C * N) →
        (∀ i, OneBoundedOn (support i) (f i)) →
        (∀ i, SupportedOn (support i) (f i)) →
        ‖countingForm N M (support 0) (Fin.cases 0 P) v f‖ ≤
          A * normalizedGowers S 1 (M : ℤ) v

/-- KMTT Lemma 3.4 at fixed numerical parameters. The auxiliary modulus
and power are shared by all shifted inputs. -/
def KMTTLocalInverseEstimate (C : ℝ) (d ℓ b₀ : ℕ) (a A b B : ℝ) : Prop :=
  ∀ (N M q : ℕ), 0 < N → 0 < q → 0 < M → M ≤ parameterLength N q d →
    ∀ P : Fin (ℓ + 1) → Polynomial ℤ, FixedPolynomialFamily P →
      (P (Fin.last ℓ)).natDegree = d → (∀ i, i ≠ 0 → HasCoefficients C q (P i)) →
    ∀ f : Fin (ℓ + 1) → ℤ → ℂ,
      (∀ i, OneBoundedOn (positiveInterval N) (f i)) →
      (∀ i, SupportedOn (positiveInterval N) (f i)) →
    ∀ ρ : ℝ, 0 < ρ → ρ < 1 / 2 →
      ρ ≤ ‖countingForm N M (positiveInterval N) P (fun _ => 1) f‖ →
      (M : ℝ) ≤ A * ((q : ℝ) / ρ)^B ∨
        ∃ (q' b' : ℕ), 0 < q' ∧ 1 ≤ b' ∧ b' ≤ b₀ ∧ (q' : ℝ) ≤ A * ρ^(-B) ∧
        ∀ i, i ≠ 0 → ∃ φ : ℤ → ℂ, (∀ x, ‖φ x‖ ≤ 1) ∧
          a * ρ^b * (N : ℝ) ≤ ‖∑ x ∈ positiveInterval N, f i x * φ x‖ ∧
          ∀ x t : ℤ, ‖φ (x + (q' : ℤ) * (q : ℤ)^b' * t) - φ x‖ ≤
            A * ((q : ℝ) / ρ)^B * (M : ℝ) ^ (-((P i).natDegree : ℝ)) * |(t : ℝ)|

/-- The unweighted inverse estimate with a specified bound on the power
of the base modulus. -/
def KMTTLocalInverseWithExponent (C : ℝ) (d ℓ b₀ : ℕ) : Prop :=
  ∃ a A b B : ℝ, 0 < a ∧ 0 < A ∧ 0 < b ∧ 0 < B ∧
    KMTTLocalInverseEstimate C d ℓ b₀ a A b B

/-- KMTT Lemma 3.4 in the paper's unweighted normalization. This form
allows the upper bound on the power of the base modulus to be selected
after the coefficient constant and family length. -/
def KMTTLocalInverse : Prop :=
  ∀ (C : ℝ) (d ℓ : ℕ), 1 ≤ C → 0 < ℓ →
    ∃ (a A b B : ℝ) (b₀ : ℕ), 0 < a ∧ 0 < A ∧ 0 < b ∧ 0 < B ∧
      KMTTLocalInverseEstimate C d ℓ b₀ a A b B

/-- The degree-only bound on the power of the base modulus in KMTT
Lemma 3.4. The other constants may be selected after fixing the
coefficient constant and family length. -/
def KMTTLocalInverseDegreeUniform : Prop :=
  ∀ d : ℕ, ∃ b₀ : ℕ, ∀ (C : ℝ) (ℓ : ℕ), 1 ≤ C → 0 < ℓ →
    KMTTLocalInverseWithExponent C d ℓ b₀

theorem KMTTLocalInverseDegreeUniform.toLocalInverse
    (hInv : KMTTLocalInverseDegreeUniform) : KMTTLocalInverse := by
  intro C d ℓ hC hℓ
  obtain ⟨b₀, hInv⟩ := hInv d
  obtain ⟨a, A, b, B, ha, hA, hb, hB, hEst⟩ := hInv C ℓ hC hℓ
  exact ⟨a, A, b, B, b₀, ha, hA, hb, hB, hEst⟩

universe u

/-- Transfer the fixed-family discrete estimate uniformly over probability
systems. The constant and exponent come from the discrete estimate before
a system or a family of inputs is chosen. -/
theorem uniform_orbit_bound_of_teravainen
    (hTer : TeravainenFixedFamily) (d : ℕ) (hd : 0 < d)
    {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ) (hP : ErgodicPolynomialFamily P)
    (hdeg : ∀ i, (P i).natDegree ≤ d) (htop : ∃ i, (P i).natDegree = d)
    (C : ℝ) (hC : 1 ≤ C) :
    ∃ K A : ℝ, 1 ≤ K ∧ 0 < A ∧
    ∀ {X : Type u} [MeasurableSpace X] {μ : MeasureTheory.Measure X}
      [MeasureTheory.IsProbabilityMeasure μ] (T : ProbabilitySystem X μ) (H : ℕ), 0 < H →
      ∀ (v : ℤ → ℂ) (f : Fin ℓ → X → ℂ),
      OneBoundedOn (positiveInterval H) v →
      (∀ i x, ‖f i x‖ ≤ 1) →
      MeasureTheory.Integrable (weightedErgodicAverage T P f v H) μ →
      (positiveInterval (H^d)) ⊆ spatialInterval C (H^d) →
      (∀ m ∈ positiveInterval (H^d), ∀ n ∈ positiveInterval H, ∀ i,
        m + (P i).eval n ∈ spatialInterval C (H^d)) →
      (∫ x, ‖weightedErgodicAverage T P f v H x‖ ∂μ) ≤
        A * ((H : ℝ)⁻¹ + phaseNorm (d + 1) (positiveInterval H) v) ^ (1 / K) := by
  obtain ⟨K, hK, hKmt⟩ := hTer d hd
  obtain ⟨A, hA, hEst⟩ := hKmt P hP hdeg htop C hC
  refine ⟨K, A, hK, hA, ?_⟩
  intro X _ μ _ T H hH v f hv hf hInt hsub hz
  let N := H^d
  let Z := spatialInterval C N
  let B := A * ((H : ℝ)⁻¹ + phaseNorm (d + 1) (positiveInterval H) v) ^ (1 / K)
  apply integral_norm_weightedErgodicAverage_le_of_orbit_bound T P f v
    (N := N) (pow_pos hH _) Z hz hInt B
  intro g hg z
  let F : Fin (ℓ + 1) → ℤ → ℂ := Fin.cases
    (fun m => if m ∈ positiveInterval N then g ((T.transform ^ m) z) else 0)
    (fun i m => if m ∈ Z then f i ((T.transform ^ m) z) else 0)
  have hF : ∀ i, OneBoundedOn Z (F i) := by
    intro i
    induction i using Fin.cases with
    | zero =>
      intro m _
      simp only [F, Fin.cases_zero]
      split <;> simp [hg]
    | succ i =>
      intro m hm
      simpa only [F, Fin.cases_succ, if_pos hm] using hf i ((T.transform ^ m) z)
  have hSupport : ∀ i, SupportedOn Z (F i) := by
    intro i
    induction i using Fin.cases with
    | zero =>
      intro m hm
      simp [F, show m ∉ positiveInterval N from fun h => hm (hsub h)]
    | succ i =>
      intro m hm
      simp [F, hm]
  have hBase : SupportedOn (positiveInterval N) (F 0) := by
    intro m hm
    simp [F, hm]
  have hEq : countingForm N H (positiveInterval N) (Fin.cases 0 P) v
      (orbitInputs T f g Z z) =
      countingForm N H (positiveInterval N) (Fin.cases 0 P) v F := by
    unfold countingForm
    congr 1
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro n hn
    congr 1
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
    simp [orbitInputs, F, hm]
  rw [hEq, countingForm_mono_window N H hsub (Fin.cases 0 P) rfl v F hBase]
  exact hEst H hH v F hv hF hSupport

/-- Transfer the fixed-family discrete estimate at H to the ergodic L¹
average. The hypotheses state the common spatial window needed at this H. -/
theorem orbit_bound_of_teravainen
    {X : Type*} [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    [MeasureTheory.IsProbabilityMeasure μ]
    (hTer : TeravainenFixedFamily) (d : ℕ) (hd : 0 < d)
    {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ) (hP : ErgodicPolynomialFamily P)
    (hdeg : ∀ i, (P i).natDegree ≤ d) (htop : ∃ i, (P i).natDegree = d)
    (C : ℝ) (hC : 1 ≤ C) :
    ∃ K A : ℝ, 1 ≤ K ∧ 0 < A ∧
    ∀ (T : ProbabilitySystem X μ) (H : ℕ), 0 < H →
      ∀ (v : ℤ → ℂ) (f : Fin ℓ → X → ℂ),
      OneBoundedOn (positiveInterval H) v →
      (∀ i x, ‖f i x‖ ≤ 1) →
      MeasureTheory.Integrable (weightedErgodicAverage T P f v H) μ →
      (positiveInterval (H^d)) ⊆ spatialInterval C (H^d) →
      (∀ m ∈ positiveInterval (H^d), ∀ n ∈ positiveInterval H, ∀ i,
        m + (P i).eval n ∈ spatialInterval C (H^d)) →
      (∫ x, ‖weightedErgodicAverage T P f v H x‖ ∂μ) ≤
        A * ((H : ℝ)⁻¹ + phaseNorm (d + 1) (positiveInterval H) v) ^ (1 / K) := by
  obtain ⟨K, A, hK, hA, h⟩ := uniform_orbit_bound_of_teravainen hTer d hd P hP hdeg htop C hC
  exact ⟨K, A, hK, hA, @h X ‹MeasurableSpace X› μ ‹IsProbabilityMeasure μ›⟩

/-- Banks, arXiv:2610.15483v1, Theorem 1.1, for conductors at least three.
Real-valuedness is imposed on the complete character on ZMod r. -/
def BanksRealZeroBound : Prop :=
  ∀ (r : ℕ) [NeZero r], 3 ≤ r → ∀ χ : DirichletCharacter ℂ r,
    χ.IsPrimitive → (∀ x : ZMod r, (χ x).im = 0) →
    ∀ β : ℝ, 0 < β → β < 1 → χ.LFunction (β : ℂ) = 0 →
      (3 / 1000 : ℝ) ≤ (1 - β) * Real.log r

/-- The threshold comparison in Proposition 4.1 and Proposition 6.2.
The possible exceptional conductor is at most the model cutoff. -/
theorem exclude_exceptional_model_zero
    (hBanks : BanksRealZeroBound) {r Q : ℕ} [NeZero r] (hr : 3 ≤ r) (hrQ : r ≤ Q)
    (χ : DirichletCharacter ℂ r) (hprim : χ.IsPrimitive)
    (hreal : ∀ x : ZMod r, (χ x).im = 0)
    {β : ℝ} (hβ : 0 < β) (hβ' : β < 1) (hzero : χ.LFunction (β : ℂ) = 0) :
    ¬ ((1 - β) * Real.log Q ≤ (1 / 1000 : ℝ)) := by
  have hlog : Real.log (r : ℝ) ≤ Real.log (Q : ℝ) :=
    Real.log_le_log (by exact_mod_cast (show 0 < r by omega)) (by exact_mod_cast hrQ)
  have hb := hBanks r hr χ hprim hreal β hβ hβ' hzero
  have h := mul_le_mul_of_nonneg_left hlog (sub_nonneg.mpr hβ'.le)
  intro hbad
  linarith

/-- The atom-average operator of a finite local factor. On the support
partition this is the mean on the unique containing atom. -/
noncomputable def localFactorProjection (factor : Finset (Finset ℤ)) (f : ℤ → ℂ)
    (x : ℤ) : ℂ :=
  ∑ A ∈ factor, if x ∈ A then (∑ z ∈ A, f z) / (A.card : ℂ) else 0

/-- KMTT Lemma 5.3. The partition, common modulus, resolutions and
count-approximation output are made explicit to expose the application. -/
def KMTTLocalWeakRegularity : Prop :=
  ∀ (C : ℝ) (d ℓ : ℕ), 1 ≤ C → 0 < ℓ →
    ∃ (A₀ A₁ D₁ c₁ D₂ : ℝ) (B₀ : ℕ),
      0 < A₀ ∧ 0 < A₁ ∧ 0 < D₁ ∧ 0 < c₁ ∧ 0 < D₂ ∧
    ∀ (N M q : ℕ), 0 < N → 0 < q → 0 < M → M ≤ parameterLength N q d →
    ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → initialModulus ⌈ε^(-A₀)⌉₊ ∣ q →
    ∀ P : Fin (ℓ + 1) → Polynomial ℤ, FixedPolynomialFamily P →
      (P (Fin.last ℓ)).natDegree = d → (∀ i, i ≠ 0 → HasCoefficients C q (P i)) →
    ∀ f : Fin (ℓ + 1) → ℤ → ℂ,
      (∀ i, OneBoundedOn (positiveInterval N) (f i)) →
      (∀ i, SupportedOn (positiveInterval N) (f i)) →
      (M : ℝ) ≤ A₁ * ((q : ℝ) / ε)^D₁ ∨
        ∃ (B : ℕ) (R : Fin (ℓ + 1) → ℕ) (factor : Fin (ℓ + 1) → Finset (Finset ℤ)),
          1 ≤ B ∧ B ≤ B₀ ∧
          (∀ i, let ν := if i = 0 then (P 1).natDegree else (P i).natDegree
            0 < R i ∧ c₁ * ((q : ℝ) / ε)^(-D₂) * (M : ℝ)^ν ≤ (R i : ℝ)) ∧
          (∀ i x, x ∈ positiveInterval N ↔ ∃! A, A ∈ factor i ∧ x ∈ A) ∧
          (∀ i A, A ∈ factor i → A ⊆ positiveInterval N ∧ R i ≤ A.card ∧ A.card ≤ 2 * R i ∧
            ∃ a : ℤ, A = (positiveInterval A.card).image (fun u => a + (q : ℤ)^B * u)) ∧
          ‖countingForm N M (positiveInterval N) P (fun _ => 1)
              (fun i => localFactorProjection (factor i) (f i)) -
            countingForm N M (positiveInterval N) P (fun _ => 1) f‖ ≤ ε

end NilBohr
