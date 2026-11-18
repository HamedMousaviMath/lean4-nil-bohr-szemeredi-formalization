import NilBohr.DensityRegularity
import NilBohr.RemarkLocalFactors
import NilBohr.DifferenceWitnesses
import NilBohr.WeakRegularityReanchor

/-! Deterministic local factors for the KMTT weak regularity argument. -/

open scoped BigOperators
open Polynomial

namespace NilBohr

/-- A partition of one-based spatial points into progressions of prescribed
step and length between the resolution and twice the resolution. -/
structure ProgressionPartition (X : Finset ℤ) (step resolution : ℕ) where
  atoms : Finset (Finset ℤ)
  mem_iff : ∀ x, x ∈ X ↔ ∃ A ∈ atoms, x ∈ A
  unique_atom : ∀ {A B x}, A ∈ atoms → B ∈ atoms → x ∈ A → x ∈ B → A = B
  block : ∀ A ∈ atoms, resolution ≤ A.card ∧ A.card ≤ 2 * resolution ∧
    ∃ a : ℤ, A = (positiveInterval A.card).image (fun t => a + (step : ℤ) * t)

private theorem ProgressionPartition.subset {X : Finset ℤ} {s r : ℕ}
    (p : ProgressionPartition X s r) {A : Finset ℤ} (hA : A ∈ p.atoms) : A ⊆ X :=
  fun _ hx => (p.mem_iff _).mpr ⟨A, hA, hx⟩

private theorem ProgressionPartition.existsUnique_mem {X : Finset ℤ} {s r : ℕ}
    (p : ProgressionPartition X s r) (x : ℤ) :
    x ∈ X ↔ ∃! A, A ∈ p.atoms ∧ x ∈ A := by
  constructor
  · intro hx
    obtain ⟨A, hA, hxA⟩ := (p.mem_iff x).mp hx
    exact ⟨A, ⟨hA, hxA⟩, fun B hB => p.unique_atom hB.1 hA hB.2 hxA⟩
  · rintro ⟨A, hA, _⟩
    exact (p.mem_iff x).mpr ⟨A, hA.1, hA.2⟩

/-- Map the interval blocks into ambient coordinates by an injective affine map. -/
private def ProgressionPartition.affine {X : Finset ℤ} {s r k : ℕ}
    (p : ProgressionPartition X s r) (a : ℤ) (hk : 0 < k) :
    ProgressionPartition (X.image (fun t => a + (k : ℤ) * t)) (k * s) r := by
  let g : ℤ → ℤ := fun t => a + (k : ℤ) * t
  have hg : Function.Injective g := by
    have hk' : (k : ℤ) ≠ 0 := by exact_mod_cast hk.ne'
    intro u v h
    exact mul_left_cancel₀ hk' (add_left_cancel h)
  refine ⟨p.atoms.image (fun A => A.image g), ?_, ?_, ?_⟩
  · intro x
    constructor
    · rintro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨A, hA, hyA⟩ := (p.mem_iff y).mp hy
      exact ⟨A.image g, Finset.mem_image.mpr ⟨A, hA, rfl⟩, Finset.mem_image.mpr ⟨y, hyA, rfl⟩⟩
    · rintro ⟨_, hA, hxA⟩
      obtain ⟨A', hA', rfl⟩ := Finset.mem_image.mp hA
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hxA
      exact Finset.mem_image.mpr ⟨y, p.subset hA' hy, rfl⟩
  · intro A B x hA hB hxA hxB
    obtain ⟨A', hA', rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨B', hB', rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hxA
    obtain ⟨v, hv, he⟩ := Finset.mem_image.mp hxB
    rw [hg he] at hv
    rw [p.unique_atom hA' hB' hu hv]
  · intro A hA
    obtain ⟨A', hA', rfl⟩ := Finset.mem_image.mp hA
    rw [Finset.card_image_of_injective _ hg]
    obtain ⟨hlo, hhi, b, hb⟩ := p.block A' hA'
    refine ⟨hlo, hhi, g b, ?_⟩
    conv_lhs => rw [hb, Finset.image_image]
    congr 1
    funext t
    dsimp [g]
    push_cast
    ring

/-- Combine adjacent or separated partitions when their ambient sets are disjoint. -/
private def ProgressionPartition.union {X Y : Finset ℤ} {s r : ℕ}
    (p : ProgressionPartition X s r) (q : ProgressionPartition Y s r) (hd : Disjoint X Y) :
    ProgressionPartition (X ∪ Y) s r := by
  refine ⟨p.atoms ∪ q.atoms, ?_, ?_, ?_⟩
  · intro x
    simp only [Finset.mem_union, p.mem_iff, q.mem_iff]
    aesop
  · intro A B x hA hB hxA hxB
    rcases Finset.mem_union.mp hA with hA | hA <;>
      rcases Finset.mem_union.mp hB with hB | hB
    · exact p.unique_atom hA hB hxA hxB
    · exact False.elim ((Finset.disjoint_left.mp hd) (p.subset hA hxA) (q.subset hB hxB))
    · exact False.elim ((Finset.disjoint_left.mp hd) (p.subset hB hxB) (q.subset hA hxA))
    · exact q.unique_atom hA hB hxA hxB
  · intro A hA
    rcases Finset.mem_union.mp hA with hA | hA
    · exact p.block A hA
    · exact q.block A hA

private def ProgressionPartition.empty (s r : ℕ) :
    ProgressionPartition ∅ s r where
  atoms := ∅
  mem_iff x := by simp
  unique_atom h _ _ _ := by simp at h
  block A h := by simp at h

private def ProgressionPartition.single {X : Finset ℤ} {s r : ℕ}
    (h : r ≤ X.card ∧ X.card ≤ 2 * r ∧
      ∃ a : ℤ, X = (positiveInterval X.card).image (fun t => a + (s : ℤ) * t)) :
    ProgressionPartition X s r := by
  refine ⟨{X}, ?_, ?_, ?_⟩
  · simp
  · intro A B x hA hB _ _
    simp only [Finset.mem_singleton] at hA hB
    exact hA.trans hB.symm
  · intro A hA
    rwa [Finset.mem_singleton.mp hA]

/-- Partition a consecutive interval into blocks with a merged last block. -/
private theorem consecutive_blocks {R : ℕ} (hR : 0 < R) :
    ∀ L : ℕ, R ≤ L → Nonempty (ProgressionPartition (positiveInterval L) 1 R) := by
  intro L
  induction L using Nat.strong_induction_on with
  | h L ih =>
    intro hL
    by_cases hsmall : L ≤ 2 * R
    · refine ⟨ProgressionPartition.single ⟨by simpa using hL, by simpa using hsmall, 0, ?_⟩⟩
      simp
    · obtain ⟨first⟩ := ih R (by omega) (le_refl R)
      obtain ⟨rest⟩ := ih (L - R) (by omega) (by omega)
      let rest' := rest.affine (R : ℤ) (show 0 < (1 : ℕ) by decide)
      have hd : Disjoint (positiveInterval R)
          ((positiveInterval (L - R)).image (fun t => (R : ℤ) + (1 : ℤ) * t)) := by
        apply Finset.disjoint_left.mpr
        intro x hx hxr
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hxr
        unfold positiveInterval at hx hy
        have hx' := Finset.mem_Icc.mp hx
        have hy' := Finset.mem_Icc.mp hy
        omega
      have hwhole : positiveInterval R ∪
          (positiveInterval (L - R)).image (fun t => (R : ℤ) + (1 : ℤ) * t) = positiveInterval L := by
        ext x
        simp only [Finset.mem_union, Finset.mem_image, positiveInterval, Finset.mem_Icc, one_mul]
        constructor
        · rintro (h | ⟨y, h, rfl⟩) <;> omega
        · intro hx
          by_cases hb : x ≤ (R : ℤ)
          · exact Or.inl ⟨hx.1, hb⟩
          · exact Or.inr ⟨x - (R : ℤ), ⟨by omega, by omega⟩, by omega⟩
      rw [← hwhole]
      exact ⟨first.union rest' hd⟩


/-- A large interval is partitioned into short progressions of fixed step.
The conditional size hypothesis permits singletons independently of the
available interval length. -/
theorem fixedStep_progression_partition {N L R : ℕ} (hL : 0 < L) (hR : 0 < R)
    (hlen : R = 1 ∨ (R : ℝ) + 1 ≤ (N : ℝ) / L) :
    Nonempty (ProgressionPartition (positiveInterval N) L R) := by
  classical
  let key (z : ℤ) : ℤ := (z - 1) % (L : ℤ)
  let I := positiveInterval N
  let S := I.image key
  let slice (r : ℤ) := I.filter (fun z => key z = r)
  have hp (r : S) : Nonempty (ProgressionPartition (slice r.val) L R) := by
    obtain ⟨a, n, hn, hsize, hrepr⟩ := residue_slice_as_progression hL r.val r.prop
    have hRn : R ≤ n := by
      rcases hlen with he | he
      · omega
      · exact_mod_cast (show (R : ℝ) ≤ (n : ℝ) by linarith)
    obtain ⟨p⟩ := consecutive_blocks hR n hRn
    have he : slice r.val = (positiveInterval n).image (fun t => a + (L : ℤ) * t) := by
      ext z
      simp only [slice, I, key, Finset.mem_filter, Finset.mem_image]
      exact hrepr z
    rw [he]
    simpa only [mul_one] using (show Nonempty (ProgressionPartition _ _ _) from ⟨p.affine a hL⟩)
  let p : (r : S) → ProgressionPartition (slice r.val) L R := fun r => (hp r).some
  refine ⟨⟨S.attach.biUnion (fun r => (p r).atoms), ?_, ?_, ?_⟩⟩
  · intro z
    constructor
    · intro hz
      let r : S := ⟨key z, Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩
      obtain ⟨A, hA, hzA⟩ := ((p r).mem_iff z).mp (Finset.mem_filter.mpr ⟨hz, rfl⟩)
      exact ⟨A, Finset.mem_biUnion.mpr ⟨r, Finset.mem_attach _ _, hA⟩, hzA⟩
    · rintro ⟨A, hA, hzA⟩
      obtain ⟨r, _, hAr⟩ := Finset.mem_biUnion.mp hA
      exact (Finset.mem_filter.mp ((p r).subset hAr hzA)).1
  · intro A B z hA hB hzA hzB
    obtain ⟨r, _, hAr⟩ := Finset.mem_biUnion.mp hA
    obtain ⟨s, _, hBs⟩ := Finset.mem_biUnion.mp hB
    have hrs : r = s := Subtype.ext
      ((Finset.mem_filter.mp ((p r).subset hAr hzA)).2.symm.trans
        (Finset.mem_filter.mp ((p s).subset hBs hzB)).2)
    subst s
    exact (p r).unique_atom hAr hBs hzA hzB
  · intro A hA
    obtain ⟨r, _, hAr⟩ := Finset.mem_biUnion.mp hA
    exact (p r).block A hAr

private theorem ProgressionPartition.projection_eq {X : Finset ℤ} {s r : ℕ}
    (p : ProgressionPartition X s r) (f : ℤ → ℂ) {A : Finset ℤ} (hA : A ∈ p.atoms)
    {x : ℤ} (hx : x ∈ A) :
    localFactorProjection p.atoms f x = (∑ z ∈ A, f z) / (A.card : ℂ) := by
  classical
  rw [localFactorProjection, Finset.sum_eq_single_of_mem A hA]
  · simp [hx]
  · intro B hB hBA
    exact if_neg (fun hzB => hBA (p.unique_atom hB hA hzB hx))

private theorem ProgressionPartition.projection_supported {X : Finset ℤ} {s r : ℕ}
    (p : ProgressionPartition X s r) (f : ℤ → ℂ) :
    SupportedOn X (localFactorProjection p.atoms f) := by
  classical
  intro x hx
  unfold localFactorProjection
  exact Finset.sum_eq_zero (fun A hA => if_neg (fun hz => hx (p.subset hA hz)))

private theorem ProgressionPartition.projection_bounded {X : Finset ℤ} {s r : ℕ}
    (p : ProgressionPartition X s r) {f : ℤ → ℂ} (hf : ∀ x, ‖f x‖ ≤ 1) (x : ℤ) :
    ‖localFactorProjection p.atoms f x‖ ≤ 1 := by
  by_cases hx : x ∈ X
  · obtain ⟨A, hA, hxA⟩ := (p.mem_iff x).mp hx
    have hpos : (0 : ℝ) < (A.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr (show A.Nonempty from ⟨x, hxA⟩)
    rw [p.projection_eq f hA hxA, norm_div, Complex.norm_natCast, div_le_iff₀ hpos, one_mul]
    refine (norm_sum_le _ _).trans ?_
    simpa using Finset.sum_le_sum (s := A) (fun z _ => hf z)
  · simp [p.projection_supported f x hx]

private theorem ProgressionPartition.residual_sum_zero {X : Finset ℤ} {s r : ℕ}
    (p : ProgressionPartition X s r) (f : ℤ → ℂ) {A : Finset ℤ} (hA : A ∈ p.atoms) :
    ∑ x ∈ A, (f x - localFactorProjection p.atoms f x) = 0 := by
  classical
  by_cases hne : A.Nonempty
  · have hpos : (A.card : ℂ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hne).ne'
    rw [Finset.sum_sub_distrib, sub_eq_zero]
    trans ∑ _x ∈ A, (∑ t ∈ A, f t) / (A.card : ℂ)
    · simp [nsmul_eq_mul, div_eq_inv_mul, ← mul_assoc, hpos]
    · exact Finset.sum_congr rfl (fun _ hx => (p.projection_eq f hA hx).symm)
  · simp [Finset.not_nonempty_iff_eq_empty.mp hne]

private theorem ProgressionPartition.sum_atoms {α : Type*} [AddCommMonoid α]
    {X : Finset ℤ} {L R : ℕ} (p : ProgressionPartition X L R) (F : ℤ → α) :
    ∑ x ∈ X, F x = ∑ A ∈ p.atoms, ∑ x ∈ A, F x := by
  classical
  have hX : p.atoms.biUnion id = X := by
    ext x
    simpa only [Finset.mem_biUnion, id_eq] using (p.mem_iff x).symm
  calc
    ∑ x ∈ X, F x = ∑ x ∈ p.atoms.biUnion id, F x := congrArg (fun Y => ∑ x ∈ Y, F x) hX.symm
    _ = _ := by
      rw [Finset.sum_biUnion]
      · rfl
      · intro A hA B hB hne
        exact Finset.disjoint_left.mpr (fun _ hxA hxB => hne (p.unique_atom hA hB hxA hxB))

/-- The atom means cancel against the constant part of a test function.
The residual is divided by two so that it is itself 1-bounded. -/
theorem ProgressionPartition.norm_residual_correlation_le {X : Finset ℤ} {L R : ℕ}
    (p : ProgressionPartition X L R) {f φ : ℤ → ℂ} {D : ℝ}
    (hf : ∀ x, ‖f x‖ ≤ 1) (hD : 0 ≤ D)
    (hLip : ∀ x t : ℤ, ‖φ (x + (L : ℤ) * t) - φ x‖ ≤ D * |(t : ℝ)|) :
    ‖∑ x ∈ X, ((f x - localFactorProjection p.atoms f x) / 2) * φ x‖ ≤
      (X.card : ℝ) * (D * (2 * (R : ℝ))) := by
  let g (x : ℤ) := (f x - localFactorProjection p.atoms f x) / 2
  have hg : ∀ x, ‖g x‖ ≤ 1 := by
    intro x
    dsimp only [g]
    rw [norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num, div_le_iff₀ (by norm_num), one_mul]
    exact (norm_sub_le _ _).trans (by linarith [hf x, p.projection_bounded hf x])
  have hAtom (A : Finset ℤ) (hA : A ∈ p.atoms) :
      ‖∑ x ∈ A, g x * φ x‖ ≤ ∑ _x ∈ A, D * (2 * (R : ℝ)) := by
    obtain ⟨_, hsize, a, hrepr⟩ := p.block A hA
    have hzero : ∑ x ∈ A, g x = 0 := by
      simp only [g, ← Finset.sum_div, p.residual_sum_zero f hA, zero_div]
    have he : ∑ x ∈ A, g x * φ x = ∑ x ∈ A, g x * (φ x - φ a) := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hzero, zero_mul, sub_zero]
    rw [he]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
    intro x hx
    rw [hrepr] at hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
    have ht' := Finset.mem_Icc.mp ht
    have ht₀ : (0 : ℝ) ≤ (t : ℝ) := by exact_mod_cast (show 0 ≤ t by omega)
    have hts : (t : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast ht'.2
    have hs : (A.card : ℝ) ≤ 2 * (R : ℝ) := by exact_mod_cast hsize
    rw [norm_mul]
    refine (mul_le_of_le_one_left (norm_nonneg _) (hg _)).trans ((hLip a t).trans ?_)
    rw [abs_of_nonneg ht₀]
    exact mul_le_mul_of_nonneg_left (hts.trans hs) hD
  change ‖∑ x ∈ X, g x * φ x‖ ≤ _
  rw [p.sum_atoms (fun x => g x * φ x)]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun A hA => hAtom A hA).trans_eq ?_)
  rw [← p.sum_atoms (fun _ => D * (2 * (R : ℝ)))]
  simp [nsmul_eq_mul]

private theorem countingForm_replace_one {k : ℕ} (N M : ℕ) (X : Finset ℤ)
    (P : Fin k → Polynomial ℤ) (v : ℤ → ℂ) (f : Fin k → ℤ → ℂ)
    (i : Fin k) (u : ℤ → ℂ) :
    countingForm N M X P v f - countingForm N M X P v (Function.update f i u) =
      2 * countingForm N M X P v (Function.update f i (fun x => (f i x - u x) / 2)) := by
  have hprod (x y : ℤ) (g : ℤ → ℂ) :
      (∏ j, Function.update f i g j (x + (P j).eval y)) =
        (∏ j ∈ Finset.univ.erase i, f j (x + (P j).eval y)) * g (x + (P i).eval y) := by
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  have hfun (x y : ℤ) :
      v y * (∏ j, f j (x + (P j).eval y)) -
          v y * (∏ j, Function.update f i u j (x + (P j).eval y)) =
        2 * (v y * ∏ j, Function.update f i (fun x => (f i x - u x) / 2) j
          (x + (P j).eval y)) := by
    nth_rw 1 [← Function.update_eq_self i f]
    rw [hprod, hprod, hprod]
    ring
  simp only [countingForm, ← sub_div, ← Finset.sum_sub_distrib, hfun, ← Finset.mul_sum,
    mul_div_assoc]

private def projectionPrefix {k : ℕ} (f g : Fin k → ℤ → ℂ) (j : ℕ)
    (i : Fin k) : ℤ → ℂ := if (i : ℕ) < j then g i else f i

private theorem projectionPrefix_succ {k : ℕ} (f g : Fin k → ℤ → ℂ) {j : ℕ}
    (hj : j < k) :
    projectionPrefix f g (j + 1) =
      Function.update (projectionPrefix f g j) ⟨j, hj⟩ (g ⟨j, hj⟩) := by
  funext i
  by_cases hi : i = ⟨j, hj⟩
  · subst i
    simp [projectionPrefix]
  have hine : (i : ℕ) ≠ j := fun h => hi (Fin.ext h)
  have he : ((i : ℕ) < j + 1) ↔ (i : ℕ) < j := by omega
  simp [projectionPrefix, Function.update_of_ne hi, he]

/-- A large difference of the two counts gives an inverse-theorem threshold
for one scaled residual, with earlier coordinates replaced by their projections. -/
theorem exists_large_coordinate_residual {k : ℕ} (hk : 0 < k) (N M : ℕ) (X : Finset ℤ)
    (P : Fin k → Polynomial ℤ) (v : ℤ → ℂ) (f g : Fin k → ℤ → ℂ) {ε : ℝ}
    (hε : ε < ‖countingForm N M X P v g - countingForm N M X P v f‖) :
    ∃ (i : Fin k) (F : Fin k → ℤ → ℂ),
      F i = (fun x => (f i x - g i x) / 2) ∧
      (∀ j, j ≠ i → F j = f j ∨ F j = g j) ∧
      ε / (2 * (k : ℝ)) ≤ ‖countingForm N M X P v F‖ := by
  classical
  let T (j : ℕ) := countingForm N M X P v (projectionPrefix f g j)
  let ρ := ε / (2 * (k : ℝ))
  have hT0 : T 0 = countingForm N M X P v f := by
    dsimp only [T]
    rw [show projectionPrefix f g 0 = f by funext i; simp [projectionPrefix]]
  have hTk : T k = countingForm N M X P v g := by
    have hp : projectionPrefix f g k = g := by
      funext i
      simp [projectionPrefix, i.isLt]
    dsimp only [T]
    rw [hp]
  have hmul : 2 * ρ * (k : ℝ) = ε := by
    have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    dsimp only [ρ]
    field_simp
    ring
  by_contra h
  have hstep (j : ℕ) (hj : j < k) : ‖T j - T (j + 1)‖ ≤ 2 * ρ := by
    let i : Fin k := ⟨j, hj⟩
    let F := Function.update (projectionPrefix f g j) i (fun x => (f i x - g i x) / 2)
    have hFi : F i = (fun x => (f i x - g i x) / 2) := Function.update_self i _ _
    have hFother (j' : Fin k) (hj' : j' ≠ i) : F j' = f j' ∨ F j' = g j' := by
      dsimp only [F]
      rw [Function.update_of_ne hj']
      simp only [projectionPrefix]
      split <;> simp
    have hi : projectionPrefix f g j i = f i := by simp [projectionPrefix, i]
    have hdiff : T j - T (j + 1) = 2 * countingForm N M X P v F := by
      simp only [T, projectionPrefix_succ f g hj]
      change countingForm N M X P v (projectionPrefix f g j) -
        countingForm N M X P v (Function.update (projectionPrefix f g j) i (g i)) = _
      rw [countingForm_replace_one, hi]
    rw [hdiff, norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]
    have hF : ‖countingForm N M X P v F‖ ≤ ρ := by
      by_contra! he
      exact h ⟨i, F, hFi, hFother, he.le⟩
    exact mul_le_mul_of_nonneg_left hF (by norm_num)
  have hbound (j : ℕ) (hj : j ≤ k) : ‖T j - T 0‖ ≤ 2 * ρ * (j : ℝ) := by
    induction j with
    | zero => simp
    | succ j ih =>
      calc
        ‖T (j + 1) - T 0‖ = ‖(T (j + 1) - T j) + (T j - T 0)‖ := by ring_nf
        _ ≤ ‖T (j + 1) - T j‖ + ‖T j - T 0‖ := norm_add_le _ _
        _ ≤ 2 * ρ + 2 * ρ * (j : ℝ) := by
          rw [norm_sub_rev (T (j + 1)) (T j)]
          exact add_le_add (hstep j (by omega)) (ih (by omega))
        _ = _ := by push_cast; ring
  have hlim := hbound k le_rfl
  rw [hTk, hT0, hmul] at hlim
  exact (not_le_of_gt hε) hlim

private theorem parameter_power_bound {N M q d ν : ℕ} (hq : 0 < q) (hν : ν ≤ d)
    (hd : 0 < d) (hM : 0 < M) (hMmax : M ≤ parameterLength N q d) :
    (M : ℝ)^ν ≤ N := by
  let Q := (q : ℝ)^(d - 1)
  have hQ : 1 ≤ Q := one_le_pow₀ (by exact_mod_cast hq)
  have hs : 0 ≤ (N : ℝ) / Q := by positivity
  have hfloor : (parameterLength N q d : ℝ) ≤ ((N : ℝ) / Q)^((d : ℝ)⁻¹) :=
    Nat.floor_le (Real.rpow_nonneg hs _)
  calc
    (M : ℝ)^ν ≤ (M : ℝ)^d := pow_le_pow_right₀ (by exact_mod_cast hM) hν
    _ ≤ (parameterLength N q d : ℝ)^d :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hMmax) _
    _ ≤ ((((N : ℝ) / Q)^((d : ℝ)⁻¹))^d) :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hfloor _
    _ = (N : ℝ) / Q := Real.rpow_inv_natCast_pow hs hd.ne'
    _ ≤ N := div_le_self (Nat.cast_nonneg _) hQ

private theorem absorb_cutoff_constant {S B : ℝ} (hB : 0 < B) :
    ∃ A₀ : ℝ, 0 < A₀ ∧
      ∀ ε : ℝ, 0 < ε → ε < 1/2 → S * ε^(-B) ≤ ε^(-A₀) := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt S (by norm_num : (1 : ℝ) < 2)
  refine ⟨B + (n : ℝ), by positivity, ?_⟩
  intro ε hε hεhalf
  have h₂ : (2 : ℝ) ≤ ε⁻¹ := by
    rw [← one_div, le_div_iff₀ hε]
    linarith
  have hpow : S ≤ ε^(-(n : ℝ)) := by
    rw [Real.rpow_neg hε.le, Real.rpow_natCast, ← inv_pow]
    exact hn.le.trans (pow_le_pow_left₀ (by norm_num) h₂ n)
  calc
    S * ε^(-B) ≤ ε^(-(n : ℝ)) * ε^(-B) :=
      mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hε.le _)
    _ = ε^(-(B + (n : ℝ))) := by rw [← Real.rpow_add hε]; congr 1; ring

private theorem choose_resolution {N M q ν J : ℕ} {u c E : ℝ}
    (hq : 0 < q) (hu : 1 ≤ u) (hqu : (q : ℝ) ≤ u)
    (hc : 0 < c) (hcquarter : c ≤ 1/4) (hE : (J : ℝ) ≤ E)
    (hMν : (M : ℝ)^ν ≤ N) (hlarge : 2 ≤ c * u^(-E) * (M : ℝ)^ν) :
    let z := c * u^(-E) * (M : ℝ)^ν
    let R := ⌊z⌋₊
    0 < R ∧ z/2 ≤ (R : ℝ) ∧ (R : ℝ) ≤ z ∧ (R : ℝ) + 1 ≤ (N : ℝ) / (q^J : ℕ) := by
  let z := c * u^(-E) * (M : ℝ)^ν
  let R := ⌊z⌋₊
  have h₂ : 2 ≤ R := Nat.le_floor (by change (2 : ℝ) ≤ z; exact hlarge)
  have hzlarge : 2 ≤ z := hlarge
  have hRz : (R : ℝ) ≤ z := Nat.floor_le (by linarith)
  have hzR : z/2 ≤ (R : ℝ) := by
    have hnext := Nat.lt_floor_add_one z
    have h₂R : (2 : ℝ) ≤ (R : ℝ) := by exact_mod_cast h₂
    linarith
  have hqJ : (0 : ℝ) < (q^J : ℕ) := Nat.cast_pos.mpr (pow_pos hq _)
  have hqJu : ((q^J : ℕ) : ℝ) ≤ u^(J : ℝ) := by
    rw [Nat.cast_pow, Real.rpow_natCast]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hqu _
  have hp : (q^J : ℕ) * u^(-E) ≤ 1 := by
    calc
      (q^J : ℕ) * u^(-E) ≤ u^(J : ℝ) * u^(-E) :=
        mul_le_mul_of_nonneg_right hqJu (Real.rpow_nonneg (by linarith) _)
      _ = u^((J : ℝ) - E) := by rw [sub_eq_add_neg, Real.rpow_add (by linarith : 0 < u)]
      _ ≤ 1 := by
        rw [← Real.rpow_zero u]
        exact Real.rpow_le_rpow_of_exponent_le hu (sub_nonpos.mpr hE)
  have hzsize : (q^J : ℕ) * z ≤ (N : ℝ) / 4 := by
    calc
      _ = c * (((q^J : ℕ) : ℝ) * u^(-E)) * (M : ℝ)^ν := by dsimp only [z]; ring
      _ ≤ c * 1 * (N : ℝ) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left hp hc.le) hMν (by positivity) (by positivity)
      _ ≤ _ := by nlinarith only [hcquarter, Nat.cast_nonneg (α := ℝ) N]
  refine ⟨(by decide : 0 < 2).trans_le h₂, hzR, hRz, (le_div_iff₀ hqJ).mpr ?_⟩
  have hsmall : (R : ℝ) + 1 ≤ 2*z := by linarith
  calc
    _ ≤ (2*z) * ((q^J : ℕ) : ℝ) := mul_le_mul_of_nonneg_right hsmall hqJ.le
    _ ≤ (N : ℝ) := by nlinarith only [hzsize, Nat.cast_nonneg (α := ℝ) N]

private theorem residual_lipschitz_power_bound {N M q J ν R : ℕ}
    {S u ε B b E c : ℝ} (hM : 0 < M) (hS : 0 < S) (hu : 1 ≤ u)
    (hqu : (q : ℝ) ≤ u) (hε : 0 < ε) (he : ε⁻¹ ≤ u) (hb : 0 < b)
    (hE : E = B + (J : ℝ) + b) (hc : 0 < c)
    (hR : (R : ℝ) ≤ c * u^(-E) * (M : ℝ)^ν) :
    (N : ℝ) * ((S * u^B * (M : ℝ)^(-(ν : ℝ)) * (q^J : ℕ)) * (2 * (R : ℝ))) ≤
      (2 * S * c) * ε^b * (N : ℝ) := by
  have hu' : 0 < u := by linarith
  have hMp : (0 : ℝ) < (M : ℝ)^ν := by positivity
  have huq : ((q^J : ℕ) : ℝ) ≤ u^(J : ℝ) := by
    rw [Nat.cast_pow, Real.rpow_natCast]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hqu _
  have hX : u^B * u^(J : ℝ) * u^(-E) = u^(-b) := by
    rw [← Real.rpow_add hu', ← Real.rpow_add hu', hE]
    congr 1
    ring
  have hεu : u^(-b) ≤ ε^b := by
    refine (Real.rpow_le_rpow_of_exponent_nonpos (by positivity : 0 < ε⁻¹) he
      (neg_nonpos.mpr hb.le)).trans_eq ?_
    rw [Real.inv_rpow hε.le, Real.rpow_neg hε.le, inv_inv]
  calc
    _ ≤ (N : ℝ) * ((S * u^B * (M : ℝ)^(-(ν : ℝ)) * (q^J : ℕ)) *
        (2 * (c * u^(-E) * (M : ℝ)^ν))) := by gcongr
    _ ≤ (N : ℝ) * ((S * u^B * (M : ℝ)^(-(ν : ℝ)) * u^(J : ℝ)) *
        (2 * (c * u^(-E) * (M : ℝ)^ν))) := by gcongr
    _ = (2*S*c) * u^(-b) * N := by
      rw [Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_natCast, ← hX]
      field_simp
      ring
    _ ≤ _ := by gcongr

/-- KMTT Lemma 5.3 follows from Lemma 3.4 by using predetermined factors
and testing the first large coordinate residual against their atom means. -/
theorem KMTTLocalInverse.toLocalWeakRegularity (hInv : KMTTLocalInverse) :
    KMTTLocalWeakRegularity := by
  classical
  intro C d ℓ hC hℓ
  have hC' : 1 ≤ 2*C^2+C := hC.trans (by linarith [sq_nonneg C])
  obtain ⟨a, A, b, B, b₀, ha, hA, hb, hB, hEst⟩ := hInv (2*C^2+C) d ℓ hC' hℓ
  let k : ℕ := ℓ + 1
  have hk : 0 < k := Nat.succ_pos ℓ
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  let cε : ℝ := (2 * (k : ℝ))⁻¹
  have hcε : 0 < cε := by dsimp only [cε]; positivity
  have hcε₁ : cε ≤ 1 := by
    dsimp only [cε]
    rw [inv_le_one₀ (by positivity)]
    linarith
  let J := b₀ + 1
  let E : ℝ := B + (J : ℝ) + b
  have hE : 0 < E := by dsimp only [E]; positivity
  have hBE : B ≤ E := by dsimp only [E]; linarith [Nat.cast_nonneg (α := ℝ) J]
  have hJE : (J : ℝ) ≤ E := by dsimp only [E]; linarith
  let S := A * cε^(-B)
  have hS : 0 < S := by dsimp only [S]; positivity
  let κ := a * cε^b
  have hκ : 0 < κ := by dsimp only [κ]; positivity
  let c := min (1/4 : ℝ) (κ/(4*S))
  have hc : 0 < c := lt_min (by norm_num) (by positivity)
  have hcquarter : c ≤ 1/4 := min_le_left _ _
  have hcκ : 2*S*c ≤ κ/2 := by
    have hm : c ≤ κ/(4*S) := min_le_right _ _
    have hmul := (le_div_iff₀ (by positivity : 0 < 4*S)).mp hm
    linarith
  let A₁ := max S (2/c)
  have hA₁ : 0 < A₁ := hS.trans_le (le_max_left _ _)
  obtain ⟨A₀, hA₀, hCut⟩ := absorb_cutoff_constant (S := S) hB
  refine ⟨A₀, A₁, E, c/2, E, J, hA₀, hA₁, hE, by positivity, hE, ?_⟩
  intro N M q hN hq hM hMmax ε hε hεhalf hMod P hP hDeg hCoeff f hf hfs
  let u := (q : ℝ)/ε
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hεone : ε ≤ 1 := by linarith
  have huq : (q : ℝ) ≤ u :=
    (le_div_iff₀ hε).mpr (mul_le_of_le_one_right (Nat.cast_nonneg _) hεone)
  have hu : 1 ≤ u := hqR.trans huq
  have hu' : 0 < u := by linarith
  have heu : ε⁻¹ ≤ u :=
    (one_div ε ▸ (div_le_div_of_nonneg_right hqR hε.le))
  by_cases hSmall : (M : ℝ) ≤ A₁ * u^E
  · exact Or.inl hSmall
  right
  let ν (i : Fin (ℓ+1)) := if i = 0 then (P 1).natDegree else (P i).natDegree
  have hν (i : Fin (ℓ+1)) : 0 < ν i := by
    have h1 : (1 : Fin (ℓ+1)) ≠ 0 := by simpa [Fin.one_eq_zero_iff] using hℓ.ne'
    by_cases hi : i = 0
    · simpa only [ν, if_pos hi] using (hCoeff 1 h1).2.2.1
    · simpa only [ν, if_neg hi] using (hCoeff i hi).2.2.1
  have hνd (i : Fin (ℓ+1)) : ν i ≤ d := by
    have hPi (j : Fin (ℓ+1)) : (P j).natDegree ≤ d := by
      rw [← hDeg]
      exact hP.2.2.2.monotone (Fin.le_last j)
    by_cases hi : i = 0
    · simpa only [ν, if_pos hi] using hPi 1
    · simpa only [ν, if_neg hi] using hPi i
  have hd : 0 < d := (hν 0).trans_le (hνd 0)
  let z (i : Fin (ℓ+1)) := c * u^(-E) * (M : ℝ)^(ν i)
  have hz (i : Fin (ℓ+1)) : 2 ≤ z i := by
    by_contra hzi'
    have hzi : z i < 2 := lt_of_not_ge hzi'
    apply hSmall
    have hMone : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have hMν : (M : ℝ) ≤ (M : ℝ)^(ν i) := by
      simpa only [pow_one] using pow_le_pow_right₀ hMone (show 1 ≤ ν i from hν i)
    have hprod : c * u^(-E) * (M : ℝ) < 2 :=
      (mul_le_mul_of_nonneg_left hMν (by positivity)).trans_lt hzi
    have hprod' : (M : ℝ) < (2/c) * u^E := by
      rw [Real.rpow_neg hu'.le] at hprod
      have hmul := mul_lt_mul_of_pos_right hprod (show 0 < u^E by positivity)
      have hp : u^E ≠ 0 := (Real.rpow_pos_of_pos hu' _).ne'
      have hmul' : c * (M : ℝ) < 2 * u^E := by
        have heq : c * (u^E)⁻¹ * (M : ℝ) * u^E = c * M := by field_simp
        rwa [heq] at hmul
      rw [div_mul_eq_mul_div, lt_div_iff₀ hc]
      simpa only [mul_comm (M : ℝ) c] using hmul'
    exact hprod'.le.trans (mul_le_mul_of_nonneg_right (le_max_right S (2/c)) (by positivity))
  let R (i : Fin (ℓ+1)) := ⌊z i⌋₊
  have hR (i : Fin (ℓ+1)) : 0 < R i ∧ z i/2 ≤ (R i : ℝ) ∧ (R i : ℝ) ≤ z i ∧
      (R i : ℝ) + 1 ≤ (N : ℝ) / (q^J : ℕ) :=
    choose_resolution hq hu huq hc hcquarter hJE
      (parameter_power_bound hq (hνd i) hd hM hMmax) (hz i)
  let p (i : Fin (ℓ+1)) : ProgressionPartition (positiveInterval N) (q^J) (R i) :=
    (fixedStep_progression_partition (pow_pos hq _) (hR i).1 (Or.inr (hR i).2.2.2)).some
  let g (i : Fin (ℓ+1)) := localFactorProjection (p i).atoms (f i)
  refine ⟨J, R, fun i => (p i).atoms, Nat.succ_pos b₀, le_rfl, ?_, ?_, ?_, ?_⟩
  · intro i
    refine ⟨(hR i).1, ?_⟩
    change (c/2) * u^(-E) * (M : ℝ)^(ν i) ≤ (R i : ℝ)
    convert (hR i).2.1 using 1
    dsimp only [z]
    ring
  · intro i x
    exact (p i).existsUnique_mem x
  · intro i D hD
    have hb := (p i).block D hD
    exact ⟨(p i).subset hD, by simpa only [Nat.cast_pow] using hb⟩
  · change ‖countingForm N M (positiveInterval N) P (fun _ => 1) g -
      countingForm N M (positiveInterval N) P (fun _ => 1) f‖ ≤ ε
    by_contra hdiff'
    have hdiff := lt_of_not_ge hdiff'
    obtain ⟨i, F, hFi, hFother, hLarge⟩ := exists_large_coordinate_residual hk N M
      (positiveInterval N) P (fun _ => 1) f g hdiff
    have hfull (j : Fin k) (x : ℤ) : ‖f j x‖ ≤ 1 := oneBounded_of_supported (hf j) (hfs j) x
    have hg (j : Fin k) (x : ℤ) : ‖g j x‖ ≤ 1 := (p j).projection_bounded (hfull j) x
    have hgs (j : Fin k) : SupportedOn (positiveInterval N) (g j) :=
      (p j).projection_supported (f j)
    have hFbound (j : Fin k) : OneBoundedOn (positiveInterval N) (F j) := by
      intro x _
      by_cases hj : j = i
      · subst j
        rw [hFi, norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num, div_le_iff₀ (by norm_num), one_mul]
        exact (norm_sub_le _ _).trans (by linarith [hfull i x, hg i x])
      rcases hFother j hj with hjf | hjg
      · rw [hjf]; exact hfull j x
      · rw [hjg]; exact hg j x
    have hFsupp (j : Fin k) : SupportedOn (positiveInterval N) (F j) := by
      intro x hx
      by_cases hj : j = i
      · subst j
        simp only [hFi, hfs i x hx, hgs i x hx, sub_self, zero_div]
      rcases hFother j hj with hjf | hjg
      · rw [hjf]; exact hfs j x hx
      · rw [hjg]; exact hgs j x hx
    let ρ := cε * ε
    have hρ : 0 < ρ := mul_pos hcε hε
    have hρhalf : ρ < 1/2 := (mul_le_of_le_one_left hε.le hcε₁).trans_lt hεhalf
    have hρeq : ρ = ε / (2 * (k : ℝ)) := by dsimp only [ρ, cε]; rw [div_eq_mul_inv, mul_comm]
    rw [← hρeq] at hLarge
    have hScale : A * ((q : ℝ)/ρ)^B = S * u^B := by
      rw [show (q : ℝ)/ρ = cε⁻¹*u by dsimp only [ρ, u]; field_simp,
        Real.mul_rpow (inv_nonneg.mpr hcε.le) hu'.le, Real.inv_rpow hcε.le,
        ← Real.rpow_neg hcε.le]
      dsimp only [S]
      ring
    have hρB : A * ρ^(-B) = S * ε^(-B) := by
      dsimp only [ρ, S]
      rw [Real.mul_rpow hcε.le hε.le, mul_assoc]
    have hρb : a * ρ^b = κ * ε^b := by
      dsimp only [ρ, κ]
      rw [Real.mul_rpow hcε.le hε.le, mul_assoc]
    rcases exists_localInverse_fixed_coordinate hEst hC hN hq hM hMmax P hP hDeg
      hCoeff F hFbound hFsupp i ρ hρ hρhalf hLarge with hs | hw
    · apply hSmall
      rw [hScale] at hs
      exact hs.trans (mul_le_mul (le_max_left _ _) (Real.rpow_le_rpow_of_exponent_le hu hBE)
        (by positivity) hA₁.le)
    obtain ⟨q', b', hq', _, hb', hq'ρ, φ, _, hCorr, hLip⟩ := hw
    have hq'Cut : q' ≤ ⌈ε^(-A₀)⌉₊ := by
      rw [hρB] at hq'ρ
      exact_mod_cast hq'ρ.trans ((hCut ε hε hεhalf).trans (Nat.le_ceil _))
    have hStep : q' * q^b' ∣ q^J := auxiliary_step_dvd_fixed_power hq' hq'Cut hMod hb'
    have hLip' : ∀ x t : ℤ, ‖φ (x + (q^J : ℕ) * t) - φ x‖ ≤
        (S * u^B * (M : ℝ)^(-(ν i : ℝ)) * (q^J : ℕ)) * |(t : ℝ)| := by
      apply modular_lipschitz_of_dvd φ (mul_pos hq' (pow_pos hq _)) hStep (by positivity)
      intro x t
      by_cases hi : i = 0 <;>
        simpa only [hScale, Nat.cast_mul, Nat.cast_pow, ν, hi, if_true, if_false] using hLip x t
    have hUp := (p i).norm_residual_correlation_le (hfull i) (by positivity) hLip'
    change ‖∑ x ∈ positiveInterval N, ((f i x - g i x) / 2) * φ x‖ ≤ _ at hUp
    rw [card_positiveInterval] at hUp
    have hPow := residual_lipschitz_power_bound (N := N) (J := J) (ν := ν i) (B := B)
      (E := E) hM hS hu huq hε heu hb rfl hc (hR i).2.2.1
    rw [hFi, hρb] at hCorr
    have hLast : (2*S*c) * ε^b * (N : ℝ) < κ * ε^b * (N : ℝ) := by
      have hbase : 2*S*c < κ := hcκ.trans_lt (by linarith)
      exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right hbase (by positivity)) (by positivity)
    exact (not_lt_of_ge hCorr) (hUp.trans_lt (hPow.trans_lt hLast))

end NilBohr
