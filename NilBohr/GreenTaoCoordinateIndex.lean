import NilBohr.GreenTaoModel
import Mathlib.Analysis.Normed.Group.Constructions

namespace NilBohr

noncomputable section

/-- Second-kind coordinates in the ordered axes (X,Y,Z). -/
def heisenbergMalcevFinCoordinates : HeisenbergGroup ≃ (Fin 3 → ℝ) where
  toFun g := ![g.x, g.y, g.z - g.x * g.y]
  invFun v := ⟨v 0, v 1, v 2 + v 0 * v 1⟩
  left_inv g := by ext <;> simp
  right_inv v := by funext i; fin_cases i <;> simp

/-- The second-kind coordinates place the added axis first in degree zero,
before Z in degree one, and after Z in degree two. -/
def heisenbergProductMalcevFinCoordinates (d : ℕ) :
    (HeisenbergGroup × Multiplicative ℝ) ≃ (Fin 4 → ℝ) where
  toFun g :=
    let p := heisenbergProductMalcevCoordinates d g
    ![p.1, p.2.1, p.2.2.1, p.2.2.2]
  invFun v :=
    if d = 1 then
      (⟨v 0, v 1, v 3 + v 0 * v 1⟩, Multiplicative.ofAdd (v 2))
    else if d = 0 then
      (⟨v 1, v 2, v 3 + v 1 * v 2⟩, Multiplicative.ofAdd (v 0))
    else
      (⟨v 0, v 1, v 2 + v 0 * v 1⟩, Multiplicative.ofAdd (v 3))
  left_inv := by
    intro g
    by_cases h : d = 1 <;> by_cases h0 : d = 0 <;>
      simp [heisenbergProductMalcevCoordinates, h, h0, HeisenbergGroup.malcevCoordinates]
  right_inv := by
    intro v
    funext i
    by_cases h : d = 1 <;> by_cases h0 : d = 0 <;> fin_cases i <;>
      simp [heisenbergProductMalcevCoordinates, h, h0, HeisenbergGroup.malcevCoordinates]

theorem norm_heisenbergMalcevFinCoordinates (g : HeisenbergGroup) :
    ‖heisenbergMalcevFinCoordinates g‖ =
      heisenbergMalcevNorm (HeisenbergGroup.coordinates g) := by
  rw [← HeisenbergGroup.malcevCoordinates_norm]
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonempty]
    intro i
    fin_cases i <;>
      simp [heisenbergMalcevFinCoordinates, HeisenbergGroup.malcevCoordinates, Real.norm_eq_abs,
        le_max_left, le_max_right, le_trans]
  · rw [max_le_iff, max_le_iff]
    exact ⟨norm_le_pi_norm (heisenbergMalcevFinCoordinates g) 0,
      norm_le_pi_norm (heisenbergMalcevFinCoordinates g) 1,
      norm_le_pi_norm (heisenbergMalcevFinCoordinates g) 2⟩

theorem norm_heisenbergProductMalcevFinCoordinates (d : ℕ)
    (g : HeisenbergGroup × Multiplicative ℝ) :
    ‖heisenbergProductMalcevFinCoordinates d g‖ =
      max (heisenbergMalcevNorm (HeisenbergGroup.coordinates g.1))
        |Multiplicative.toAdd g.2| := by
  rw [← heisenbergProductMalcevCoordinates_norm]
  let p := heisenbergProductMalcevCoordinates d g
  change ‖![p.1, p.2.1, p.2.2.1, p.2.2.2]‖ =
    max |p.1| (max |p.2.1| (max |p.2.2.1| |p.2.2.2|))
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonempty]
    intro i
    fin_cases i <;> simp [Real.norm_eq_abs, le_max_left, le_max_right, le_trans]
  · rw [max_le_iff, max_le_iff, max_le_iff]
    let v : Fin 4 → ℝ := ![p.1, p.2.1, p.2.2.1, p.2.2.2]
    exact ⟨norm_le_pi_norm v 0, norm_le_pi_norm v 1, norm_le_pi_norm v 2,
      norm_le_pi_norm v 3⟩

end

end NilBohr
