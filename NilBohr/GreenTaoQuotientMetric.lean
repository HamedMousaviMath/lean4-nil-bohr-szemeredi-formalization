import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic.Linarith

/-! A right-invariant metric on a topological group gives the quotient
metric on its right cosets by a closed subgroup. -/

namespace NilBohr

open Set
open scoped Topology

noncomputable section

variable {G : Type*} [Group G] [MetricSpace G]
variable (Γ : Subgroup G)

/-- The infimum of right-lattice translates of the group distance. -/
def rightQuotientPointDistance (x y : G) : ℝ :=
  sInf (range fun γ : Γ => dist x (y * γ))

private theorem rightQuotient_range_nonempty (x y : G) :
    (range fun γ : Γ => dist x (y * γ)).Nonempty := range_nonempty _

private theorem rightQuotient_range_bddBelow (x y : G) :
    BddBelow (range fun γ : Γ => dist x (y * γ)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨γ, rfl⟩
  exact dist_nonneg

theorem rightQuotientPointDistance_nonneg (x y : G) :
    0 ≤ rightQuotientPointDistance Γ x y := by
  apply le_csInf (rightQuotient_range_nonempty Γ x y)
  rintro _ ⟨γ, rfl⟩
  exact dist_nonneg

theorem rightQuotientPointDistance_le_translate (x y : G) (γ : Γ) :
    rightQuotientPointDistance Γ x y ≤ dist x (y * γ) :=
  csInf_le (rightQuotient_range_bddBelow Γ x y) ⟨γ, rfl⟩

theorem rightQuotientPointDistance_le_dist (x y : G) :
    rightQuotientPointDistance Γ x y ≤ dist x y := by
  simpa using rightQuotientPointDistance_le_translate Γ x y 1

theorem rightQuotientPointDistance_self (x : G) :
    rightQuotientPointDistance Γ x x = 0 := by
  apply le_antisymm _ (rightQuotientPointDistance_nonneg Γ x x)
  simpa using rightQuotientPointDistance_le_dist Γ x x

theorem rightQuotientPointDistance_exists_lt {x y : G} {ε : ℝ}
    (h : rightQuotientPointDistance Γ x y < ε) : ∃ γ : Γ, dist x (y * γ) < ε := by
  obtain ⟨v, ⟨γ, rfl⟩, hv⟩ := exists_lt_of_csInf_lt (rightQuotient_range_nonempty Γ x y) h
  exact ⟨γ, hv⟩

variable (hr : ∀ x y z : G, dist (x*z) (y*z) = dist x y)

include hr in
theorem rightQuotientPointDistance_comm (x y : G) :
    rightQuotientPointDistance Γ x y = rightQuotientPointDistance Γ y x := by
  have H (x y : G) : rightQuotientPointDistance Γ x y ≤ rightQuotientPointDistance Γ y x := by
    apply le_csInf (rightQuotient_range_nonempty Γ y x)
    rintro _ ⟨γ, rfl⟩
    calc
      _ ≤ dist x (y * ↑γ⁻¹) := rightQuotientPointDistance_le_translate Γ x y γ⁻¹
      _ = dist (x * γ) y := by
        rw [← hr x (y * ↑γ⁻¹) γ]
        simp [mul_assoc]
      _ = _ := dist_comm _ _
  exact le_antisymm (H x y) (H y x)

theorem rightQuotientPointDistance_translate_right (x y : G) (δ : Γ) :
    rightQuotientPointDistance Γ x (y * δ) = rightQuotientPointDistance Γ x y := by
  have H (y : G) (δ : Γ) :
      rightQuotientPointDistance Γ x y ≤ rightQuotientPointDistance Γ x (y * δ) := by
    apply le_csInf (rightQuotient_range_nonempty Γ x (y*δ))
    rintro _ ⟨γ, rfl⟩
    simpa [mul_assoc] using rightQuotientPointDistance_le_translate Γ x y (δ * γ)
  exact le_antisymm (by simpa [mul_assoc] using H (y*δ) δ⁻¹) (H y δ)

include hr in
theorem rightQuotientPointDistance_triangle (x y z : G) :
    rightQuotientPointDistance Γ x z ≤
      rightQuotientPointDistance Γ x y + rightQuotientPointDistance Γ y z := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨γ, hγ⟩ := rightQuotientPointDistance_exists_lt Γ
    (lt_add_of_pos_right (rightQuotientPointDistance Γ x y) (half_pos hε))
  obtain ⟨δ, hδ⟩ := rightQuotientPointDistance_exists_lt Γ
    (lt_add_of_pos_right (rightQuotientPointDistance Γ y z) (half_pos hε))
  calc
    _ ≤ dist x (z * ↑(δ * γ)) := rightQuotientPointDistance_le_translate Γ x z (δ * γ)
    _ ≤ dist x (y * γ) + dist y (z * δ) := by
      rw [← hr y (z*δ) γ]
      simpa only [Subgroup.coe_mul, ← mul_assoc] using
        dist_triangle x (y*γ) ((z*δ)*γ)
    _ ≤ _ := by linarith

/-- The right-coset distance induced by a right-invariant metric. -/
def rightQuotientDistance : (G ⧸ Γ) → (G ⧸ Γ) → ℝ :=
  fun x y => Quotient.liftOn₂ x y (rightQuotientPointDistance Γ) (by
    intro x y x' y' hx hy
    have hx' : x⁻¹ * x' ∈ Γ := QuotientGroup.leftRel_apply.mp hx
    have hy' : y⁻¹ * y' ∈ Γ := QuotientGroup.leftRel_apply.mp hy
    have hX : x * (⟨x⁻¹*x', hx'⟩ : Γ) = x' := by simp
    have hY : y * (⟨y⁻¹*y', hy'⟩ : Γ) = y' := by simp
    calc
      rightQuotientPointDistance Γ x y =
          rightQuotientPointDistance Γ x y' := by
        rw [← hY, rightQuotientPointDistance_translate_right]
      _ = rightQuotientPointDistance Γ x' y' := by
        rw [rightQuotientPointDistance_comm Γ hr x y',
          rightQuotientPointDistance_comm Γ hr x' y', ← hX,
          rightQuotientPointDistance_translate_right])

@[simp] theorem rightQuotientDistance_mk (x y : G) :
    rightQuotientDistance Γ hr (x : G ⧸ Γ) (y : G ⧸ Γ) =
      rightQuotientPointDistance Γ x y := rfl

theorem rightQuotientDistance_self (x : G ⧸ Γ) :
    rightQuotientDistance Γ hr x x = 0 :=
  Quotient.inductionOn x (rightQuotientPointDistance_self Γ)

theorem rightQuotientDistance_comm (x y : G ⧸ Γ) :
    rightQuotientDistance Γ hr x y = rightQuotientDistance Γ hr y x :=
  Quotient.inductionOn₂ x y (rightQuotientPointDistance_comm Γ hr)

theorem rightQuotientDistance_triangle (x y z : G ⧸ Γ) :
    rightQuotientDistance Γ hr x z ≤
      rightQuotientDistance Γ hr x y + rightQuotientDistance Γ hr y z :=
  Quotient.inductionOn₃ x y z (rightQuotientPointDistance_triangle Γ hr)

variable [IsTopologicalGroup G]

theorem rightQuotientDistance_eq_zero (hc : IsClosed (Γ : Set G)) (x y : G ⧸ Γ)
    (hxy : rightQuotientDistance Γ hr x y = 0) : x = y := by
  induction x, y using Quotient.inductionOn₂ with
  | _ x y =>
    have hS : IsClosed (range fun γ : Γ => y * γ) := by
      have hset : (range fun γ : Γ => y * γ) =
          (fun z : G => y⁻¹*z) ⁻¹' (Γ : Set G) := by
        ext z
        constructor
        · rintro ⟨γ, rfl⟩
          simp [← mul_assoc]
        · intro hz
          exact ⟨⟨y⁻¹*z, hz⟩, by simp⟩
      rw [hset]
      exact hc.preimage (continuous_const.mul continuous_id)
    have hx : x ∈ closure (range fun γ : Γ => y * γ) := by
      rw [Metric.mem_closure_iff]
      intro ε hε
      obtain ⟨γ, hγ⟩ := rightQuotientPointDistance_exists_lt Γ (x := x) (y := y)
        (by rwa [← rightQuotientDistance_mk Γ hr, hxy])
      exact ⟨y*γ, ⟨γ, rfl⟩, hγ⟩
    rw [hS.closure_eq] at hx
    rcases hx with ⟨γ, rfl⟩
    symm
    exact QuotientGroup.eq.mpr (by simp [← mul_assoc])

omit [IsTopologicalGroup G] in
theorem rightQuotientDistance_isOpen (s : Set (G ⧸ Γ)) :
    IsOpen s ↔ ∀ x ∈ s, ∃ (ε : ℝ), 0 < ε ∧ ∀ y, rightQuotientDistance Γ hr x y < ε → y ∈ s := by
  rw [← (QuotientGroup.isQuotientMap_mk Γ).isOpen_preimage, Metric.isOpen_iff]
  constructor
  · intro hs x hx
    induction x using Quotient.inductionOn with
    | _ x =>
      obtain ⟨ε, hε, hB⟩ := hs x hx
      refine ⟨ε, hε, ?_⟩
      intro y hy
      induction y using Quotient.inductionOn with
      | _ y =>
        obtain ⟨γ, hγ⟩ := rightQuotientPointDistance_exists_lt Γ hy
        have hm : QuotientGroup.mk (y * (γ : G)) = (y : G ⧸ Γ) := by
          symm
          exact QuotientGroup.eq.mpr (by simp [← mul_assoc])
        change (y : G ⧸ Γ) ∈ s
        rw [← hm]
        exact hB (by simpa only [Metric.mem_ball, dist_comm] using hγ)
  · intro hs x hx
    obtain ⟨ε, hε, hB⟩ := hs (x : G ⧸ Γ) hx
    refine ⟨ε, hε, ?_⟩
    intro y hy
    exact hB (y : G ⧸ Γ) ((rightQuotientPointDistance_le_dist Γ x y).trans_lt
      (by simpa only [Metric.mem_ball, dist_comm] using hy))

/-- A metric on the right-coset quotient with the ordinary quotient
topology as its definitionally underlying topology. -/
def rightInvariantQuotientMetric (hc : IsClosed (Γ : Set G)) : MetricSpace (G ⧸ Γ) :=
  MetricSpace.ofDistTopology (rightQuotientDistance Γ hr)
    (rightQuotientDistance_self Γ hr) (rightQuotientDistance_comm Γ hr)
    (rightQuotientDistance_triangle Γ hr) (rightQuotientDistance_isOpen Γ hr)
    (fun x y => rightQuotientDistance_eq_zero Γ hr hc x y)

end

end NilBohr
