import NilBohr.GreenTaoModel
import Mathlib.GroupTheory.Nilpotent

namespace NilBohr.HeisenbergGroup

theorem upperCentralSeries_two : upperCentralSeries HeisenbergGroup 2 = ⊤ := by
  apply eq_top_iff.mpr
  intro g _
  apply (mem_upperCentralSeries_succ_iff (n := 1)).mpr
  intro h
  apply (mem_upperCentralSeries_succ_iff (n := 0)).mpr
  intro k
  change (g * h * g⁻¹ * h⁻¹) * k * (g * h * g⁻¹ * h⁻¹)⁻¹ * k⁻¹ ∈
    (⊥ : Subgroup HeisenbergGroup)
  rw [(commute_centralAxis k (commutator_mem_centralAxis g h)).symm.eq]
  apply Subgroup.mem_bot.mpr
  group

instance : Group.IsNilpotent HeisenbergGroup := ⟨2, upperCentralSeries_two⟩

theorem nilpotencyClass_eq_two : Group.nilpotencyClass HeisenbergGroup = 2 := by
  have hle := upperCentralSeries_eq_top_iff_nilpotencyClass_le.mp upperCentralSeries_two
  have hnot : ¬Group.nilpotencyClass HeisenbergGroup ≤ 1 := by
    intro h
    have ht := upperCentralSeries_eq_top_iff_nilpotencyClass_le.mpr h
    let x : HeisenbergGroup := ⟨1, 0, 0⟩
    let y : HeisenbergGroup := ⟨0, 1, 0⟩
    have hx : x ∈ upperCentralSeries HeisenbergGroup 1 := by rw [ht]; trivial
    have hc := (mem_upperCentralSeries_succ_iff (n := 0)).mp hx y
    change x * y * x⁻¹ * y⁻¹ ∈ (⊥ : Subgroup HeisenbergGroup) at hc
    have hxyz := congrArg HeisenbergGroup.z (Subgroup.mem_bot.mp hc)
    rw [commutator_coordinates] at hxyz
    norm_num [x, y] at hxyz
  omega

theorem lowerCentralSeries_one_eq_centralAxis :
    lowerCentralSeries HeisenbergGroup 1 = centralAxis := by
  apply le_antisymm
  · rw [lowerCentralSeries_succ]
    apply (Subgroup.closure_le _).mpr
    rintro g ⟨x, _, y, _, rfl⟩
    exact commutator_mem_centralAxis _ _
  · intro g hg
    apply (mem_lowerCentralSeries_succ_iff 0 g).mpr
    apply Subgroup.subset_closure
    refine ⟨⟨1, 0, 0⟩, Subgroup.mem_top _, ⟨0, g.z, 0⟩, Subgroup.mem_top _, ?_⟩
    rw [commutator_coordinates]
    obtain ⟨hx, hy⟩ := hg
    ext <;> simp [hx, hy]

/-- Adding an abelian factor preserves the two-step nilpotency class. -/
theorem nilpotencyClass_prod_commGroup (A : Type*) [CommGroup A] :
    Group.nilpotencyClass (HeisenbergGroup × A) = 2 := by
  rw [nilpotencyClass_prod, nilpotencyClass_eq_two, max_eq_left]
  exact (CommGroup.nilpotencyClass_le_one (G := A)).trans (by decide)

end NilBohr.HeisenbergGroup
