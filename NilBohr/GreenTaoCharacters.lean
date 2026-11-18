import NilBohr.GreenTaoCoordinateIndex
import NilBohr.GreenTaoBinomial

/-! The integer-coordinate horizontal characters and their real polynomial
representatives on the two concrete orbits. -/

open Polynomial

namespace NilBohr

theorem leibmanScalarCharacter {η : HeisenbergGroup →* Multiplicative Circle} {k : Fin 3 → ℤ}
    (h : HasLeibmanCharacterCoordinates heisenbergMalcevFinCoordinates η k) :
    k 2 = 0 ∧ ∀ g, η g =
      Multiplicative.ofAdd (((k 0 : ℝ) * g.x + (k 1 : ℝ) * g.y : ℝ) : Circle) := by
  have hcoord (g : HeisenbergGroup) : η g = Multiplicative.ofAdd
      (((k 0 : ℝ)*g.x + (k 1 : ℝ)*g.y + (k 2 : ℝ)*(g.z - g.x*g.y) : ℝ) : Circle) := by
    simpa [Fin.sum_univ_three, heisenbergMalcevFinCoordinates, add_assoc] using h g
  have hz := HeisenbergGroup.character_central_coefficient_eq_zero η (k 0) (k 1) (k 2) hcoord
  exact ⟨hz, fun g => by simpa [hz] using hcoord g⟩

theorem leibmanProductCharacter {d : ℕ} (hd : 0 < d)
    {η : (HeisenbergGroup × Multiplicative ℝ) →* Multiplicative Circle} {k : Fin 4 → ℤ}
    (h : HasLeibmanCharacterCoordinates (heisenbergProductMalcevFinCoordinates d) η k) :
    let zidx : Fin 4 := if d = 1 then 3 else 2
    let uidx : Fin 4 := if d = 1 then 2 else 3
    k zidx = 0 ∧ ∀ g : HeisenbergGroup × Multiplicative ℝ,
      η g = Multiplicative.ofAdd (((k 0 : ℝ)*g.1.x + (k 1 : ℝ)*g.1.y +
        (k uidx : ℝ)*Multiplicative.toAdd g.2 : ℝ) : Circle) := by
  dsimp only
  let zidx : Fin 4 := if d = 1 then 3 else 2
  let uidx : Fin 4 := if d = 1 then 2 else 3
  have hcoord (g : HeisenbergGroup × Multiplicative ℝ) :
      η g = Multiplicative.ofAdd (((k 0 : ℝ)*g.1.x + (k 1 : ℝ)*g.1.y +
        (k zidx : ℝ)*(g.1.z-g.1.x*g.1.y) + (k uidx : ℝ)*Multiplicative.toAdd g.2 : ℝ) :
          Circle) := by
    have hform := h g
    by_cases h₁ : d = 1
    · simpa [Fin.sum_univ_four, heisenbergProductMalcevFinCoordinates,
        heisenbergProductMalcevCoordinates, h₁, zidx, uidx, add_comm, add_left_comm,
        add_assoc] using hform
    · simpa [Fin.sum_univ_four, heisenbergProductMalcevFinCoordinates,
        heisenbergProductMalcevCoordinates, h₁, hd.ne', zidx, uidx, add_assoc] using hform
  let η₀ := η.comp (MonoidHom.inl HeisenbergGroup (Multiplicative ℝ))
  have h₀ (g : HeisenbergGroup) : η₀ g =
      Multiplicative.ofAdd (((k 0 : ℝ)*g.x + (k 1 : ℝ)*g.y +
        (k zidx : ℝ)*(g.z-g.x*g.y) : ℝ) : Circle) := by
    simpa [η₀] using hcoord (g, 1)
  have hz := HeisenbergGroup.character_central_coefficient_eq_zero η₀ (k 0) (k 1) _ h₀
  exact ⟨hz, fun g => by simpa [hz] using hcoord g⟩

theorem leibmanProductCharacter_nonzero {d : ℕ}
    {k : Fin 4 → ℤ} (hz : k (if d = 1 then 3 else 2) = 0)
    (hk : ∃ j, k j ≠ 0) : k 0 ≠ 0 ∨ k 1 ≠ 0 ∨ k (if d = 1 then 2 else 3) ≠ 0 := by
  by_contra! h
  obtain ⟨j, hj⟩ := hk
  obtain ⟨h₀, h₁, hu⟩ := h
  apply hj
  by_cases hd : d = 1 <;> fin_cases j
  all_goals first
    | simpa [hd] using h₀
    | simpa [hd] using h₁
    | simpa [hd] using hz
    | simpa [hd] using hu

/-- The constant and linear horizontal terms may be combined with the
ordinary polynomial phase without increasing its prescribed degree. -/
theorem exists_mixedBinomialPhase {d : ℕ} (hd : 0 < d) {p : Polynomial ℝ}
    (hp : p.natDegree ≤ d) (c m : ℝ) :
    ∃ b₀ : ℝ, ∃ b : ℕ → ℝ, ∀ t : ℕ,
      c*(t : ℝ) + m*p.eval (t : ℝ) = b₀ + realBinomialPhase d b t := by
  let q : Polynomial ℝ := C c * X + C m * p
  have hq : q.natDegree ≤ d := by
    apply (natDegree_add_le _ _).trans
    apply max_le
    · exact (natDegree_mul_le.trans (by simp)).trans hd
    · exact natDegree_mul_le.trans (by simpa using hp)
  obtain ⟨b₀, b, h⟩ := exists_binomialPhase_expansion d q hq
  exact ⟨b₀, b, fun t => by simpa [q] using h t⟩

end NilBohr
