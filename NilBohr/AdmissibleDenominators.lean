import NilBohr.Definitions

namespace NilBohr

/-- The denominator sequence must come from the given admissible slope.
This keeps the sequence in the test estimate aligned with the one whose
growth and coprimality are used. -/
def AdmissibleBetaDenominators (β : ℝ) (r : ℕ → ℕ) : Prop :=
  StrictMono r ∧ ∃ a : ℕ → ℕ, StrictMono (fun j => (a j : ℝ) / (r j : ℝ)) ∧
    (∀ j, (r j).Prime ∧ 0 < a j ∧ a j < r j) ∧
    ∃ c C D : ℝ, 0 < c ∧ 0 < C ∧ 0 < D ∧
      ∀ j, c * denominatorScale (r j) ≤ (r (j + 1) : ℝ) ∧
        (r (j + 1) : ℝ) ≤ C * denominatorScale (r j) ∧
        0 < β - (a j : ℝ) / (r j : ℝ) ∧
        β - (a j : ℝ) / (r j : ℝ) ≤ D / (r (j + 1) : ℝ)

/-- Fixing the denominator witness preserves the ambient admissibility assumption. -/
theorem admissibleBeta_iff_exists_denominators (β : ℝ) :
    AdmissibleBeta β ↔ 0 < β ∧ β < 1 ∧ ∃ r, AdmissibleBetaDenominators β r := by
  constructor
  · rintro ⟨hlo, hhi, a, r, hr, ha⟩
    exact ⟨hlo, hhi, r, hr, a, ha⟩
  · rintro ⟨hlo, hhi, r, hr, a, ha⟩
    exact ⟨hlo, hhi, a, r, hr, ha⟩

end NilBohr
