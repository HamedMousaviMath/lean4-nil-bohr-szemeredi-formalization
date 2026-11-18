import NilBohr.LocalBlocks
import NilBohr.LocalTestReduction

/-! Partition `[M]` into intervals of length `H` and one short tail, and
bound the cost of discarding spatial boundary strips. -/

open Polynomial
open scoped BigOperators

namespace NilBohr

abbrev parameterBlockLow (H j : ℕ) : ℤ := ((j * H : ℕ) : ℤ) + 1
abbrev parameterBlockHigh (H j : ℕ) : ℤ := (((j + 1) * H : ℕ) : ℤ)

/-- The complete block numbered by `j`, starting with block zero. -/
def fullParameterBlock (H j : ℕ) : Finset ℤ :=
  Finset.Icc (parameterBlockLow H j) (parameterBlockHigh H j)

/-- The final, possibly empty, incomplete parameter block. -/
def parameterTail (M H : ℕ) : Finset ℤ :=
  Finset.Icc (parameterBlockLow H (M / H)) (M : ℤ)

@[simp] theorem fullParameterBlock_card (H j : ℕ) : (fullParameterBlock H j).card = H := by
  unfold fullParameterBlock
  rw [Int.card_Icc]
  change (((((j + 1) * H : ℕ) : ℤ) + 1 - (((j * H : ℕ) : ℤ) + 1)).toNat) = H
  rw [show (((j + 1) * H : ℕ) : ℤ) = (((j * H : ℕ) : ℤ) + (H : ℤ)) by
    exact_mod_cast Nat.succ_mul j H]
  have h : ((j * H : ℕ) : ℤ) + (H : ℤ) + 1 - (((j * H : ℕ) : ℤ) + 1) = (H : ℤ) := by ring
  rw [h, Int.toNat_natCast]

@[simp] theorem parameterTail_card (M H : ℕ) : (parameterTail M H).card = M % H := by
  have h := Nat.mod_add_div M H
  have h' : ((M % H : ℕ) : ℤ) + (((M / H) * H : ℕ) : ℤ) = (M : ℤ) := by
    exact_mod_cast (mul_comm H (M / H) ▸ h)
  unfold parameterTail
  rw [Int.card_Icc]
  change ((M : ℤ) + 1 - (((M / H * H : ℕ) : ℤ) + 1)).toNat = M % H
  rw [show (M : ℤ) + 1 - (((M / H * H : ℕ) : ℤ) + 1) = ((M % H : ℕ) : ℤ) by omega,
    Int.toNat_natCast]

theorem fullParameterBlock_subset {M H j : ℕ} (hj : j ∈ Finset.range (M / H)) :
    fullParameterBlock H j ⊆ positiveInterval M := by
  intro y hy
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hy
  change ((j * H : ℕ) : ℤ) + 1 ≤ y at hlo
  have hj' : (j + 1) * H ≤ (M / H) * H :=
    Nat.mul_le_mul_right H (Nat.succ_le_of_lt (Finset.mem_range.mp hj))
  have hM : (M / H) * H ≤ M := Nat.div_mul_le_self _ _
  refine Finset.mem_Icc.mpr ⟨by change (1 : ℤ) ≤ y; omega, hhi.trans ?_⟩
  exact_mod_cast hj'.trans hM

theorem parameterTail_subset (M H : ℕ) : parameterTail M H ⊆ positiveInterval M := by
  intro y hy
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hy
  change ((M / H * H : ℕ) : ℤ) + 1 ≤ y at hlo
  exact Finset.mem_Icc.mpr ⟨by change (1 : ℤ) ≤ y; omega, hhi⟩

theorem fullParameterBlock_abs_sub_le {H j : ℕ} {y z : ℤ}
    (hy : y ∈ fullParameterBlock H j) (hz : z ∈ fullParameterBlock H j) :
    |y - z| ≤ (H : ℤ) := by
  obtain ⟨hyl, hyh⟩ := Finset.mem_Icc.mp hy
  obtain ⟨hzl, hzh⟩ := Finset.mem_Icc.mp hz
  have h : (parameterBlockHigh H j : ℤ) = (((j * H : ℕ) : ℤ) + (H : ℤ)) := by
    exact_mod_cast Nat.succ_mul j H
  change ((j * H : ℕ) : ℤ) + 1 ≤ y at hyl
  change ((j * H : ℕ) : ℤ) + 1 ≤ z at hzl
  change y ≤ parameterBlockHigh H j at hyh
  change z ≤ parameterBlockHigh H j at hzh
  rw [h] at hyh hzh
  exact abs_le.mpr ⟨by omega, by omega⟩

private theorem sum_fullParameterBlocks {A : Type*} [AddCommMonoid A]
    (H b : ℕ) (f : ℤ → A) :
    (∑ y ∈ positiveInterval (b * H), f y) =
      ∑ j ∈ Finset.range b, ∑ y ∈ fullParameterBlock H j, f y := by
  induction b with
  | zero => simp [positiveInterval]
  | succ b ih =>
      rw [Finset.sum_range_succ, ← ih, ← Finset.sum_union]
      · congr 1
        ext y
        simp only [positiveInterval, fullParameterBlock, Finset.mem_union, Finset.mem_Icc]
        have hmax : (b * H : ℕ) ≤ (b + 1) * H := Nat.mul_le_mul_right _ (by omega)
        have hmaxZ : (((b * H : ℕ) : ℤ)) ≤ (((b + 1) * H : ℕ) : ℤ) := by exact_mod_cast hmax
        change (1 ≤ y ∧ y ≤ (((b + 1) * H : ℕ) : ℤ)) ↔
          (1 ≤ y ∧ y ≤ ((b * H : ℕ) : ℤ)) ∨
            ((((b * H : ℕ) : ℤ) + 1 ≤ y) ∧ y ≤ (((b + 1) * H : ℕ) : ℤ))
        omega
      · apply Finset.disjoint_left.mpr
        intro y h₁ h₂
        have h₁' := (Finset.mem_Icc.mp h₁).2
        have h₂' := (Finset.mem_Icc.mp h₂).1
        change y ≤ ((b * H : ℕ) : ℤ) at h₁'
        change ((b * H : ℕ) : ℤ) + 1 ≤ y at h₂'
        omega

/-- The exact finite sum decomposition. The tail length is `M % H`. -/
theorem sum_positiveInterval_blocks_add_tail {A : Type*} [AddCommMonoid A]
    (M H : ℕ) (f : ℤ → A) :
    (∑ y ∈ positiveInterval M, f y) =
      (∑ j ∈ Finset.range (M / H), ∑ y ∈ fullParameterBlock H j, f y) +
        ∑ y ∈ parameterTail M H, f y := by
  rw [← sum_fullParameterBlocks, ← Finset.sum_union]
  · congr 1
    ext y
    simp only [positiveInterval, parameterTail, Finset.mem_union, Finset.mem_Icc]
    have hmax : (((M / H * H : ℕ) : ℤ)) ≤ (M : ℤ) := by
      exact_mod_cast Nat.div_mul_le_self M H
    change (1 ≤ y ∧ y ≤ (M : ℤ)) ↔ (1 ≤ y ∧ y ≤ ((M / H * H : ℕ) : ℤ)) ∨
      ((((M / H * H : ℕ) : ℤ) + 1 ≤ y) ∧ y ≤ (M : ℤ))
    omega
  · apply Finset.disjoint_left.mpr
    intro y h₁ h₂
    have hu := (Finset.mem_Icc.mp h₁).2
    have hl := (Finset.mem_Icc.mp h₂).1
    change y ≤ ((M / H * H : ℕ) : ℤ) at hu
    change ((M / H * H : ℕ) : ℤ) + 1 ≤ y at hl
    omega

/-- For a bounded summand, the normalized cost of deleting the short
parameter tail and at most `N * D` spatial positions per full block is
at most `(X.card / N) * (H / M) + D`. -/
theorem norm_partition_delete_le {N M H : ℕ} (hN : 0 < N) (hM : 0 < M) (hH : 0 < H)
    (X : Finset ℤ) (bad : ℕ → Finset ℤ) (f : ℤ → ℤ → ℂ) {D E : ℝ} (hD : 0 ≤ D)
    (hBadSub : ∀ j ∈ Finset.range (M / H), bad j ⊆ X)
    (hBadCard : ∀ j ∈ Finset.range (M / H), ((bad j).card : ℝ) ≤ (N : ℝ) * D)
    (hf : ∀ x ∈ X, ∀ y ∈ positiveInterval M, ‖f x y‖ ≤ 1)
    (hretain : ‖(∑ j ∈ Finset.range (M / H), ∑ x ∈ X \ bad j,
       ∑ y ∈ fullParameterBlock H j, f x y) / ((N : ℂ) * (M : ℂ))‖ ≤ E) :
    ‖(∑ x ∈ X, ∑ y ∈ positiveInterval M, f x y) / ((N : ℂ) * (M : ℂ))‖ ≤
      E + (X.card : ℝ) / (N : ℝ) * ((H : ℝ) / (M : ℝ)) + D := by
  let S := Finset.range (M / H)
  let B (j : ℕ) (x : ℤ) := ∑ y ∈ fullParameterBlock H j, f x y
  let L := ∑ j ∈ S, ∑ x ∈ X \ bad j, B j x
  let R := ∑ j ∈ S, ∑ x ∈ bad j, B j x
  let T := ∑ x ∈ X, ∑ y ∈ parameterTail M H, f x y
  have hsplit : (∑ x ∈ X, ∑ y ∈ positiveInterval M, f x y) = L + R + T := by
    calc
      _ = ∑ x ∈ X, ((∑ j ∈ S, B j x) + (∑ y ∈ parameterTail M H, f x y)) := by
        exact Finset.sum_congr rfl (fun x _ => sum_positiveInterval_blocks_add_tail M H (f x))
      _ = (∑ j ∈ S, ∑ x ∈ X, B j x) + T := by
        rw [Finset.sum_add_distrib, Finset.sum_comm]
      _ = L + R + T := by
        congr 1
        unfold L R
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        exact (Finset.sum_sdiff (hBadSub j hj) (f := B j)).symm
  have hTailBound : ‖T‖ ≤ (X.card : ℝ) * (H : ℝ) := by
    refine (norm_sum_le _ _).trans ?_
    have hn : ∀ x ∈ X, ‖∑ y ∈ parameterTail M H, f x y‖ ≤ (H : ℝ) := by
      intro x hx
      refine (norm_sum_le _ _).trans ((Finset.sum_le_sum (g := fun _ => (1 : ℝ))
        (fun y hy => hf x hx y (parameterTail_subset M H hy))).trans ?_)
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one, parameterTail_card]
      exact_mod_cast (Nat.mod_lt M hH).le
    exact (Finset.sum_le_sum hn).trans_eq (by simp [nsmul_eq_mul])
  have hRBound : ‖R‖ ≤ (N : ℝ) * (M : ℝ) * D := by
    have hBlock (j : ℕ) (hj : j ∈ S) (x : ℤ) (hx : x ∈ X) : ‖B j x‖ ≤ (H : ℝ) := by
      unfold B
      refine (norm_sum_le _ _).trans ((Finset.sum_le_sum (g := fun _ => (1 : ℝ))
        (fun y hy => hf x hx y (fullParameterBlock_subset hj hy))).trans_eq ?_)
      simp [nsmul_eq_mul]
    have hInner (j : ℕ) (hj : j ∈ S) : ‖∑ x ∈ bad j, B j x‖ ≤ (N : ℝ) * D * (H : ℝ) := by
      refine (norm_sum_le _ _).trans ((Finset.sum_le_sum (g := fun _ => (H : ℝ))
        (fun x hx => hBlock j hj x (hBadSub j hj hx))).trans ?_)
      simp only [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (hBadCard j hj) (by positivity)
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hInner).trans ?_)
    simp only [Finset.sum_const, nsmul_eq_mul, S, Finset.card_range]
    have hq : ((M / H : ℕ) : ℝ) * (H : ℝ) ≤ (M : ℝ) := by
      exact_mod_cast Nat.div_mul_le_self M H
    calc
      _ = (((M / H : ℕ) : ℝ) * (H : ℝ)) * ((N : ℝ) * D) := by ring
      _ ≤ (M : ℝ) * ((N : ℝ) * D) := mul_le_mul_of_nonneg_right hq (by positivity)
      _ = _ := by ring
  let n : ℂ := (N : ℂ) * (M : ℂ)
  have hTN : ‖T / n‖ ≤ (X.card : ℝ) / (N : ℝ) * ((H : ℝ) / (M : ℝ)) := by
    dsimp only [n]
    rw [norm_div, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
    apply (div_le_iff₀ (by positivity)).mpr
    convert hTailBound using 1
    field_simp
  have hRN : ‖R / n‖ ≤ D := by
    dsimp only [n]
    rw [norm_div, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
    apply (div_le_iff₀ (by positivity)).mpr
    simpa only [mul_comm D] using hRBound
  change ‖(∑ x ∈ X, ∑ y ∈ positiveInterval M, f x y) / n‖ ≤ _
  rw [hsplit, add_div, add_div]
  have hL : ‖L / n‖ ≤ E := hretain
  exact ((norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)).trans (by linarith)

/-- The first point of every complete block is retained among its parameters. -/
theorem parameterBlockLow_mem {H : ℕ} (hH : 0 < H) (j : ℕ) :
    parameterBlockLow H j ∈ fullParameterBlock H j := by
  apply Finset.mem_Icc.mpr
  refine ⟨le_rfl, ?_⟩
  change (((j * H : ℕ) : ℤ) + 1) ≤ (((j + 1) * H : ℕ) : ℤ)
  rw [show (((j + 1) * H : ℕ) : ℤ) = (((j * H : ℕ) : ℤ) + (H : ℤ)) by
    exact_mod_cast Nat.succ_mul j H]
  exact add_le_add_left (by exact_mod_cast hH) _

private theorem blockWindow_of_eq_ediv {w z j : ℤ} (hw : 0 < w)
    (h : (z - 1) / w = j - 1) : (j-1) * w < z ∧ z ≤ j * w := by
  have hdiv := Int.emod_add_ediv (z - 1) w
  rw [h] at hdiv
  have hlo := Int.emod_nonneg (z - 1) hw.ne'
  have hhi := Int.emod_lt_of_pos (z - 1) hw
  constructor
  · rw [mul_comm]
    omega
  · rw [show j * w = w * (j - 1) + w by ring]
    omega

/-- The full phase-substituted count is bounded by the supremum of the local
phase tests and the two explicit losses from the parameter tail and boundary
strips. The displacement bounds can be supplied by
`abs_eval_sub_le_on_short_interval`. -/
theorem norm_full_parameter_count_le_local_tests {N M H k : ℕ} {C : ℝ}
    (hN : 0 < N) (hM : 0 < M) (hH : 0 < H) (hC : 0 ≤ C)
    (X U : Finset ℤ) (hX : X ⊆ spatialInterval C N)
    (P : Fin k → Polynomial ℤ) (d L : ℕ) (hL : 0 < L) (hdeg : ∀ i, (P i).natDegree ≤ d)
    (v f₀ : ℤ → ℂ) (hv : OneBoundedOn (positiveInterval M) v) (hf₀ : OneBoundedOn X f₀)
    (V : Fin k → ℕ) (hV : ∀ i, 0 < V i) (hVN : ∀ i, L * V i ≤ N)
    (b γ : Fin k → (ℤ × ℤ) → ℝ) (R : Fin k → ℝ) (hR : ∀ i, 1 ≤ R i)
    (hmove : ∀ j ∈ Finset.range (M / H), ∀ y ∈ fullParameterBlock H j, ∀ i,
      |(((P i).eval y : ℤ) : ℝ) - (((P i).eval (parameterBlockLow H j) : ℤ) : ℝ)| ≤ R i)
    (hshift : ∀ x ∈ X, ∀ y ∈ positiveInterval M, ∀ i, x + (P i).eval y ∈ U)
    (E : ℝ) (hE : 0 ≤ E)
    (hTest : ∀ j ∈ Finset.range (M / H), ∀ a : ℤ,
      (localProgression (parameterBlockLow H j) (parameterBlockHigh H j) a L).Nonempty →
      phaseNorm (d+1) (localProgression (parameterBlockLow H j) (parameterBlockHigh H j) a L) v ≤ E) :
    ‖(∑ x ∈ X, ∑ y ∈ positiveInterval M, f₀ x * (v y *
      ∏ i, supportedBlockPhase U L (V i) (b i) (γ i) (x + (P i).eval y))) /
      ((N : ℂ) * (M : ℂ))‖ ≤
      (X.card : ℝ) / (N : ℝ) * E + (X.card : ℝ) / (N : ℝ) * ((H : ℝ) / (M : ℝ)) +
        ∑ i : Fin k, (5 * (2 * C + 4)) * R i / ((L * V i : ℕ) : ℝ) := by
  let S := Finset.range (M / H)
  let w (i : Fin k) := L * V i
  let s (j : ℕ) (i : Fin k) := (P i).eval (parameterBlockLow H j)
  let bad (j : ℕ) := Finset.univ.biUnion (fun i => boundaryNeighborhood X (w i) ⌈R i⌉₊ (s j i))
  let good (j : ℕ) := X \ bad j
  let D : ℝ := ∑ i : Fin k, (5 * (2 * C + 4)) * R i / (w i : ℝ)
  have hD : 0 ≤ D := by
    unfold D
    apply Finset.sum_nonneg
    intro i _
    have := hR i
    positivity
  have hw (i : Fin k) : 0 < w i := Nat.mul_pos hL (hV i)
  have hBadSub (j : ℕ) (_hj : j ∈ S) : bad j ⊆ X := by
    intro x hx
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hx
    exact (mem_boundaryNeighborhood.mp hi).1
  have hBadCard (j : ℕ) (_hj : j ∈ S) : ((bad j).card : ℝ) ≤ (N : ℝ) * D := by
    refine (card_union_boundaryNeighborhood_spatial_bound Finset.univ hC hX w R (s j)
      (fun i _ => hw i) (fun i _ => hVN i) (fun i _ => hR i)).trans_eq ?_
    dsimp only [D]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  let f (x y : ℤ) := f₀ x * (v y *
    ∏ i, supportedBlockPhase U L (V i) (b i) (γ i) (x + (P i).eval y))
  have hf (x : ℤ) (hx : x ∈ X) (y : ℤ) (hy : y ∈ positiveInterval M) : ‖f x y‖ ≤ 1 := by
    unfold f
    simp only [norm_mul, norm_prod]
    have hprod : (∏ i, ‖supportedBlockPhase U L (V i) (b i) (γ i) (x + (P i).eval y)‖) ≤ 1 := by
      simpa only [Finset.prod_const_one] using (Finset.prod_le_prod (s := Finset.univ)
        (f := fun i : Fin k => ‖supportedBlockPhase U L (V i) (b i) (γ i) (x + (P i).eval y)‖)
        (g := fun _ => (1 : ℝ)) (fun i _ => norm_nonneg _)
        (fun i _ => norm_supportedBlockPhase_le U L (V i) (b i) (γ i) _))
    calc
      _ ≤ 1 * (1 * (1 : ℝ)) := by
        exact mul_le_mul (hf₀ x hx) (mul_le_mul (hv y hy) hprod (by positivity) zero_le_one)
          (by positivity) zero_le_one
      _ = _ := by norm_num
  have hlength : (∑ j ∈ S, (Finset.Icc (parameterBlockLow H j) (parameterBlockHigh H j)).card) ≤ M := by
    change (∑ j ∈ S, (fullParameterBlock H j).card) ≤ M
    simp only [fullParameterBlock_card, S, Finset.sum_const, nsmul_eq_mul, Finset.card_range]
    exact Nat.div_mul_le_self M H
  have hBlocks (j : ℕ) (hj : j ∈ S) (x : ℤ) (hx : x ∈ good j) :
      ∃ J : Fin k → ℤ, ∀ y ∈ Finset.Icc (parameterBlockLow H j) (parameterBlockHigh H j), ∀ i,
        (J i - 1) * ((L : ℤ) * V i) < x + (P i).eval y ∧
          x + (P i).eval y ≤ J i * ((L : ℤ) * V i) ∧ x + (P i).eval y ∈ U := by
    obtain ⟨hxX, hxGood⟩ := Finset.mem_sdiff.mp hx
    refine ⟨fun i => (x + s j i - 1) / (w i : ℤ) + 1, ?_⟩
    intro y hy i
    have hgood : x ∉ boundaryNeighborhood X (w i) ⌈R i⌉₊ (s j i) :=
      fun hbad => hxGood (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hbad⟩)
    have hfar := boundaryAway_of_not_mem hxX (Nat.le_ceil (R i)) hgood
    have hyMove : |((x + (P i).eval y : ℤ) : ℝ) - ((x + s j i : ℤ) : ℝ)| ≤ R i := by
      push_cast
      simpa only [s, add_sub_add_left_eq_sub] using hmove j hj y hy i
    have hwZ : (0 : ℤ) < (w i : ℤ) := by exact_mod_cast hw i
    have hidx := blockIndex_eq_of_away_from_boundaries hwZ hyMove hfar
    have hb := blockWindow_of_eq_ediv hwZ (j := (x + s j i - 1) / (w i : ℤ) + 1)
      (by simpa only [add_sub_cancel_right] using hidx)
    have hu := hshift x hxX y (fullParameterBlock_subset hj hy) i
    exact ⟨by simpa [w] using hb.1, by simpa [w] using hb.2, hu⟩
  have htestretain := norm_retained_count_le hN hM S X U good
    (parameterBlockLow H) (parameterBlockHigh H) P d L hL hdeg v f₀ V hV b γ E hE
    (fun j _ x hx => (Finset.mem_sdiff.mp hx).1) hf₀ hlength hBlocks hTest
  have hr : ‖(∑ j ∈ S, ∑ x ∈ X \ bad j, ∑ y ∈ fullParameterBlock H j, f x y) /
      ((N : ℂ) * (M : ℂ))‖ ≤ (X.card : ℝ) / N * E := by
    simpa only [good, fullParameterBlock, Finset.mul_sum, f] using htestretain
  exact norm_partition_delete_le hN hM hH X bad f hD hBadSub hBadCard hf hr

/-- The same partition bound in the manuscript's counting-form notation,
with the anchor kept separate from the replaced shifted inputs. -/
theorem norm_countingForm_le_local_tests_after_replacement {N M H k : ℕ} {C : ℝ}
    (hN : 0 < N) (hM : 0 < M) (hH : 0 < H) (hC : 0 ≤ C)
    (X U : Finset ℤ) (hX : X ⊆ spatialInterval C N)
    (P : Fin (k+1) → Polynomial ℤ) (hP₀ : P 0 = 0)
    (d L : ℕ) (hL : 0 < L) (hdeg : ∀ i : Fin k, (P i.succ).natDegree ≤ d)
    (v : ℤ → ℂ) (g : Fin (k+1) → ℤ → ℂ)
    (hv : OneBoundedOn (positiveInterval M) v) (hf₀ : OneBoundedOn X (g 0))
    (V : Fin k → ℕ) (hV : ∀ i, 0 < V i) (hVN : ∀ i, L * V i ≤ N)
    (b γ : Fin k → (ℤ × ℤ) → ℝ) (R : Fin k → ℝ) (hR : ∀ i, 1 ≤ R i)
    (hg : ∀ i : Fin k, g i.succ = supportedBlockPhase U L (V i) (b i) (γ i))
    (hmove : ∀ j ∈ Finset.range (M / H), ∀ y ∈ fullParameterBlock H j, ∀ i : Fin k,
      |(((P i.succ).eval y : ℤ) : ℝ) - (((P i.succ).eval (parameterBlockLow H j) : ℤ) : ℝ)| ≤ R i)
    (hshift : ∀ x ∈ X, ∀ y ∈ positiveInterval M, ∀ i : Fin k, x + (P i.succ).eval y ∈ U)
    (E : ℝ) (hE : 0 ≤ E)
    (hTest : ∀ j ∈ Finset.range (M / H), ∀ a : ℤ,
      (localProgression (parameterBlockLow H j) (parameterBlockHigh H j) a L).Nonempty →
      phaseNorm (d+1) (localProgression (parameterBlockLow H j) (parameterBlockHigh H j) a L) v ≤ E) :
    ‖countingForm N M X P v g‖ ≤
      (X.card : ℝ) / (N : ℝ) * E + (X.card : ℝ) / (N : ℝ) * ((H : ℝ) / (M : ℝ)) +
        ∑ i : Fin k, (5 * (2 * C + 4)) * R i / ((L * V i : ℕ) : ℝ) := by
  have h := norm_full_parameter_count_le_local_tests hN hM hH hC X U hX (fun i => P i.succ)
    d L hL hdeg v (g 0) hv hf₀ V hV hVN b γ R hR hmove hshift E hE hTest
  unfold countingForm
  simp_rw [Fin.prod_univ_succ, hP₀, eval_zero, add_zero, hg, ← mul_assoc, mul_comm (v _), mul_assoc]
  simpa only [mul_assoc] using h

end NilBohr
