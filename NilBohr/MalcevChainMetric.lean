import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Tactic.Linarith

namespace NilBohr

open BigOperators
open scoped Finset

noncomputable section

/-- Lengths of finite chains between prescribed endpoints. -/
def chainLengths {A : Type*} (edge : A → A → ℝ) (g h : A) : Set ℝ :=
  {L | ∃ (n : ℕ) (x : ℕ → A), x 0 = g ∧ x n = h ∧
    L = ∑ i ∈ Finset.range n, edge (x i) (x (i + 1))}

/-- The infimum of finite chain lengths. -/
def chainDistance {A : Type*} (edge : A → A → ℝ) (g h : A) : ℝ :=
  sInf (chainLengths edge g h)

section Chains

variable {A B : Type*} {edge : A → A → ℝ}

theorem edge_mem_chainLengths (g h : A) : edge g h ∈ chainLengths edge g h := by
  classical
  refine ⟨1, fun i => if i = 0 then g else h, by simp, by simp, by simp⟩

theorem chainLengths_nonempty (edge : A → A → ℝ) (g h : A) :
    (chainLengths edge g h).Nonempty :=
  ⟨_, edge_mem_chainLengths g h⟩

theorem chainLengths_bddBelow (h0 : ∀ a b, 0 ≤ edge a b) (g h : A) :
    BddBelow (chainLengths edge g h) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨n, x, -, -, rfl⟩
  exact Finset.sum_nonneg fun i _ => h0 _ _

theorem chainDistance_nonneg (h0 : ∀ a b, 0 ≤ edge a b) (g h : A) :
    0 ≤ chainDistance edge g h :=
  le_csInf (chainLengths_nonempty edge g h) (by
    rintro _ ⟨n, x, -, -, rfl⟩
    exact Finset.sum_nonneg fun i _ => h0 _ _)

theorem chainDistance_le_length (h0 : ∀ a b, 0 ≤ edge a b) {g h : A} {L : ℝ}
    (hL : L ∈ chainLengths edge g h) : chainDistance edge g h ≤ L :=
  csInf_le (chainLengths_bddBelow h0 g h) hL

theorem chainDistance_le_edge (h0 : ∀ a b, 0 ≤ edge a b) (g h : A) :
    chainDistance edge g h ≤ edge g h :=
  chainDistance_le_length h0 (edge_mem_chainLengths g h)

theorem chainDistance_self (h0 : ∀ a b, 0 ≤ edge a b) (g : A) :
    chainDistance edge g g = 0 := by
  apply le_antisymm _ (chainDistance_nonneg h0 g g)
  apply chainDistance_le_length h0
  exact ⟨0, fun _ => g, rfl, rfl, by simp⟩

theorem chainDistance_exists_length_lt {g h : A} {ε : ℝ}
    (he : chainDistance edge g h < ε) :
    ∃ L ∈ chainLengths edge g h, L < ε :=
  exists_lt_of_csInf_lt (chainLengths_nonempty edge g h) he

theorem chainDistance_comm (hs : ∀ a b, edge a b = edge b a) (g h : A) :
    chainDistance edge g h = chainDistance edge h g := by
  unfold chainDistance
  congr 1
  suffices H : ∀ g h : A, chainLengths edge g h ⊆ chainLengths edge h g from
    Set.Subset.antisymm (H g h) (H h g)
  rintro g h L ⟨n, x, hx0, hxn, rfl⟩
  refine ⟨n, fun i => x (n-i), by simpa, by simpa, ?_⟩
  conv_lhs => rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  dsimp only
  rw [show n - 1 - i + 1 = n-i by omega, show n-(i+1) = n-1-i by omega]
  exact hs _ _

theorem chainDistance_triangle (h0 : ∀ a b, 0 ≤ edge a b) (g h k : A) :
    chainDistance edge g k ≤ chainDistance edge g h + chainDistance edge h k := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨L, ⟨m, x, hx0, hxm, rfl⟩, hL⟩ :=
    chainDistance_exists_length_lt (g := g) (h := h) (edge := edge)
      (lt_add_of_pos_right _ (half_pos hε))
  obtain ⟨M, ⟨n, y, hy0, hyn, rfl⟩, hM⟩ :=
    chainDistance_exists_length_lt (g := h) (h := k) (edge := edge)
      (lt_add_of_pos_right _ (half_pos hε))
  let v (i : ℕ) := if i ≤ m then x i else y (i-m)
  have hvLeft (i : ℕ) (hi : i ≤ m) : v i = x i := by simp [v, hi]
  have hvRight (i : ℕ) (hi : m ≤ i) : v i = y (i-m) := by
    by_cases hii : i ≤ m
    · have : i = m := by omega
      subst i
      rw [hvLeft m le_rfl, Nat.sub_self, hxm, hy0]
    · simp [v, hii]
  have hsum :
      (∑ i ∈ Finset.range (m+n), edge (v i) (v (i+1))) =
      (∑ i ∈ Finset.range m, edge (x i) (x (i+1))) +
      (∑ i ∈ Finset.range n, edge (y i) (y (i+1))) := by
    rw [Finset.sum_range_add]
    congr 1
    · refine Finset.sum_congr rfl fun i hi => ?_
      rw [hvLeft i (by have := Finset.mem_range.mp hi; omega),
        hvLeft (i+1) (by have := Finset.mem_range.mp hi; omega)]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [hvRight (m+i) (by omega), hvRight (m+i+1) (by omega)]
      congr 2 <;> omega
  have hD := chainDistance_le_length h0
    (g := g) (h := k) ⟨m+n, v, (hvLeft 0 (Nat.zero_le _)).trans hx0,
      by rw [hvRight (m+n) (by omega), Nat.add_sub_cancel_left, hyn], hsum.symm⟩
  linarith

theorem chainDistance_map_le (f : A → B) {edge' : B → B → ℝ}
    (h0 : ∀ a b, 0 ≤ edge' a b) (hedge : ∀ a b, edge' (f a) (f b) ≤ edge a b)
    (g h : A) : chainDistance edge' (f g) (f h) ≤ chainDistance edge g h := by
  apply le_csInf (chainLengths_nonempty edge g h)
  rintro _ ⟨n, x, hx0, hxn, rfl⟩
  refine (chainDistance_le_length h0 ⟨n, f ∘ x, by simp [hx0], by simp [hxn], rfl⟩).trans ?_
  exact Finset.sum_le_sum fun i _ => hedge _ _

end Chains

section Malcev

variable {G : Type*} [Group G] {m : ℕ}

/-- The symmetric weight of a link in Green–Tao's group metric. -/
def malcevEdge (ψ : G → Fin m → ℝ) (g h : G) : ℝ :=
  min ‖ψ (g * h⁻¹)‖ ‖ψ (h * g⁻¹)‖

theorem malcevEdge_nonneg (ψ : G → Fin m → ℝ) (g h : G) :
    0 ≤ malcevEdge ψ g h :=
  le_min (norm_nonneg _) (norm_nonneg _)

theorem malcevEdge_comm (ψ : G → Fin m → ℝ) (g h : G) :
    malcevEdge ψ g h = malcevEdge ψ h g :=
  min_comm _ _

@[simp] theorem malcevEdge_right (ψ : G → Fin m → ℝ) (g h z : G) :
    malcevEdge ψ (g*z) (h*z) = malcevEdge ψ g h := by
  simp [malcevEdge, mul_assoc]

/-- Group distance given by the chain formula in Green–Tao, Definition 2.2. -/
def malcevGroupChainDistance (ψ : G → Fin m → ℝ) (g h : G) : ℝ :=
  chainDistance (malcevEdge ψ) g h

theorem malcevGroupChainDistance_right (ψ : G → Fin m → ℝ) (g h z : G) :
    malcevGroupChainDistance ψ (g*z) (h*z) = malcevGroupChainDistance ψ g h := by
  apply le_antisymm
  · exact chainDistance_map_le (· * z) (malcevEdge_nonneg ψ) (by simp) g h
  · have H := chainDistance_map_le (edge := malcevEdge ψ) (· * z⁻¹) (malcevEdge_nonneg ψ)
      (by simp) (g*z) (h*z)
    simpa [mul_assoc, malcevGroupChainDistance] using H

theorem malcevGroupChainDistance_le_directed (ψ : G → Fin m → ℝ) (g h : G) :
    malcevGroupChainDistance ψ g h ≤ ‖ψ (g * h⁻¹)‖ :=
  (chainDistance_le_edge (malcevEdge_nonneg ψ) g h).trans (min_le_left _ _)

/-- Any metric dominated by the directed coordinate size is bounded by
the chain distance. The proof uses only symmetry and the triangle inequality. -/
theorem le_malcevGroupChainDistance (ψ : G → Fin m → ℝ) (D : G → G → ℝ)
    (hself : ∀ g, D g g = 0) (hcomm : ∀ g h, D g h = D h g)
    (htri : ∀ g h k, D g k ≤ D g h + D h k)
    (hle : ∀ g h, D g h ≤ ‖ψ (g * h⁻¹)‖) (g h : G) :
    D g h ≤ malcevGroupChainDistance ψ g h := by
  apply le_csInf (chainLengths_nonempty (malcevEdge ψ) g h)
  rintro _ ⟨n, x, hx, hy, rfl⟩
  rw [← hx, ← hy]
  clear hx hy
  induction n with
  | zero => simp [hself]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    refine (htri _ _ _).trans (add_le_add ih ?_)
    exact le_min (hle _ _) ((hcomm _ _).le.trans (hle _ _))

/-- Quotient distance on two right-coset representatives. Right invariance
absorbs the first representative's lattice element into the second. -/
def malcevQuotientChainDistance (Γ : Subgroup G) (ψ : G → Fin m → ℝ) (g h : G) : ℝ :=
  sInf (Set.range fun γ : Γ => malcevGroupChainDistance ψ g (h * γ))

/-- The right-invariant one-translate formula equals the two-translate
infimum over lattice elements in Green–Tao, Definition 2.2. -/
theorem malcevQuotientChainDistance_eq_two_translates (Γ : Subgroup G)
    (ψ : G → Fin m → ℝ) (g h : G) :
    malcevQuotientChainDistance Γ ψ g h =
      sInf (Set.range fun γ : Γ × Γ => malcevGroupChainDistance ψ (g * γ.1) (h * γ.2)) := by
  unfold malcevQuotientChainDistance
  congr 1
  ext L
  constructor
  · rintro ⟨γ, rfl⟩
    exact ⟨(1, γ), by simp⟩
  · rintro ⟨⟨γ, δ⟩, rfl⟩
    refine ⟨δ * γ⁻¹, ?_⟩
    dsimp only
    have H := malcevGroupChainDistance_right ψ (g * (γ : G)) (h * (δ : G)) (γ : G)⁻¹
    simpa [mul_assoc] using H

end Malcev

end

end NilBohr
