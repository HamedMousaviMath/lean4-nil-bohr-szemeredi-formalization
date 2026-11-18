import NilBohr.Definitions

open scoped BigOperators

namespace NilBohr

/-- The exact number of density increases needed in the proof of the recurrence theorem. -/
noncomputable def densityIterationSteps (η δ : ℝ) : ℕ :=
  ⌊Real.log δ⁻¹ / Real.log (1 + η)⌋₊ + 1

theorem densityIterationSteps_le {η δ : ℝ} (hη : 0 < η)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) :
    (densityIterationSteps η δ : ℝ) ≤ Real.log δ⁻¹ / Real.log (1 + η) + 1 := by
  have hlog : 0 < Real.log (1 + η) := Real.log_pos (by linarith)
  have hinv : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ).mpr hδ₁
  have hratio : 0 ≤ Real.log δ⁻¹ / Real.log (1 + η) :=
    div_nonneg (Real.log_nonneg hinv) hlog.le
  simp only [densityIterationSteps, Nat.cast_add, Nat.cast_one]
  exact add_le_add_right (Nat.floor_le hratio) 1

theorem one_lt_density_after_iterationSteps {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) :
    1 < (1 + η) ^ densityIterationSteps η δ * δ := by
  have hbase : 0 < 1 + η := by linarith
  have hlog : 0 < Real.log (1 + η) := Real.log_pos (by linarith)
  have hfloor : Real.log δ⁻¹ / Real.log (1 + η) < (densityIterationSteps η δ : ℝ) := by
    simpa only [densityIterationSteps, Nat.cast_add, Nat.cast_one] using
      (Nat.lt_floor_add_one (Real.log δ⁻¹ / Real.log (1 + η)))
  have hloglt : Real.log δ⁻¹ < Real.log ((1 + η) ^ densityIterationSteps η δ) := by
    rw [Real.log_pow]
    exact (div_lt_iff₀ hlog).mp hfloor
  have hpow : δ⁻¹ < (1 + η) ^ densityIterationSteps η δ :=
    (Real.log_lt_log_iff (inv_pos.mpr hδ) (pow_pos hbase _)).mp hloglt
  simpa [hδ.ne'] using (mul_lt_mul_of_pos_right hpow hδ)

/-- Iterating the density, logarithmic modulus and logarithmic length updates.
The step callback sees exactly the inductive bounds and the remaining iteration budget. -/
theorem exists_density_iteration_state {State : Type*}
    (valid : State → Prop) (density logModulus logLength : State → ℝ)
    (s₀ : State) (J : ℕ) {η a b loss : ℝ}
    (hη : 0 ≤ η) (ha : 0 ≤ a) (ha₁ : a ≤ 1)
    (hb : 0 ≤ b) (hloss : 0 ≤ loss) (h₀ : valid s₀)
    (step : ∀ (i : ℕ) (s : State), i < J → valid s →
      (1 + η)^i * density s₀ ≤ density s →
      logModulus s ≤ b^i * logModulus s₀ →
      a^i * logLength s₀ - (i : ℝ) * loss ≤ logLength s →
      ∃ t, valid t ∧ (1 + η) * density s ≤ density t ∧
        logModulus t ≤ b * logModulus s ∧ a * logLength s - loss ≤ logLength t) :
    ∀ i ≤ J, ∃ s, valid s ∧ (1 + η)^i * density s₀ ≤ density s ∧
      logModulus s ≤ b^i * logModulus s₀ ∧
      a^i * logLength s₀ - (i : ℝ) * loss ≤ logLength s := by
  have hbase : 0 ≤ 1 + η := by linarith
  intro i
  induction i with
  | zero =>
      intro _
      exact ⟨s₀, h₀, by simp, by simp, by simp⟩
  | succ i ih =>
      intro hi
      have hij : i < J := Nat.lt_of_succ_le hi
      obtain ⟨s, hs, hds, hqs, hns⟩ := ih hij.le
      obtain ⟨t, ht, hdt, hqt, hnt⟩ := step i s hij hs hds hqs hns
      refine ⟨t, ht, ?_, ?_, ?_⟩
      · calc
          (1 + η) ^ (i + 1) * density s₀ = (1 + η) * ((1 + η)^i * density s₀) := by
            rw [pow_succ]; ring
          _ ≤ (1 + η) * density s := mul_le_mul_of_nonneg_left hds hbase
          _ ≤ density t := hdt
      · calc
          logModulus t ≤ b * logModulus s := hqt
          _ ≤ b * (b^i * logModulus s₀) := mul_le_mul_of_nonneg_left hqs hb
          _ = b ^ (i + 1) * logModulus s₀ := by rw [pow_succ]; ring
      · have herror := mul_le_mul_of_nonneg_right ha₁
          (mul_nonneg (Nat.cast_nonneg i) hloss)
        have hprev := mul_le_mul_of_nonneg_left hns ha
        rw [pow_succ, Nat.cast_succ]
        nlinarith only [hprev, herror, hnt]

/-- If the paper's step remains available, the density cannot stay below one.
This is a finite iteration lemma. The applicability of Proposition 3.1 remains
a separate mathematical obligation. -/
theorem density_iteration_contradiction {State : Type*}
    (valid : State → Prop) (density logModulus logLength : State → ℝ)
    (s₀ : State) {η a b loss : ℝ}
    (hη : 0 < η) (ha : 0 ≤ a) (ha₁ : a ≤ 1)
    (hb : 0 ≤ b) (hloss : 0 ≤ loss) (h₀ : valid s₀)
    (hδ : 0 < density s₀) (hbound : ∀ s, valid s → density s ≤ 1)
    (step : ∀ (i : ℕ) (s : State), i < densityIterationSteps η (density s₀) → valid s →
      (1 + η)^i * density s₀ ≤ density s →
      logModulus s ≤ b^i * logModulus s₀ →
      a^i * logLength s₀ - (i : ℝ) * loss ≤ logLength s →
      ∃ t, valid t ∧ (1 + η) * density s ≤ density t ∧
        logModulus t ≤ b * logModulus s ∧ a * logLength s - loss ≤ logLength t) :
    False := by
  let J := densityIterationSteps η (density s₀)
  obtain ⟨t, ht, hdt, _, _⟩ :=
    exists_density_iteration_state valid density logModulus logLength s₀ J hη.le ha ha₁ hb
      hloss h₀ step J le_rfl
  exact (not_lt_of_ge (hbound t ht)) ((one_lt_density_after_iterationSteps hη hδ).trans_le hdt)

/-- The partition average is a weighted average of its nonempty fibre densities.
Here the statement is made with integer cross products so there are no divisions by zero. -/
theorem exists_dense_fiber {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (A S : Finset X) (hAS : A ⊆ S) (hS : S.Nonempty) (f : X → Y) :
    ∃ y ∈ S.image f,
      A.card * (S.filter (fun x => f x = y)).card ≤
        (A.filter (fun x => f x = y)).card * S.card := by
  classical
  let image := S.image f
  have himage : image.Nonempty := hS.image _
  have hA : A.card = ∑ y ∈ image, (A.filter (fun x => f x = y)).card :=
    Finset.card_eq_sum_card_fiberwise (fun x hx => Finset.mem_image_of_mem f (hAS hx))
  have hS' : S.card = ∑ y ∈ image, (S.filter (fun x => f x = y)).card :=
    Finset.card_eq_sum_card_fiberwise (fun _ hx => Finset.mem_image_of_mem f hx)
  by_contra! h
  have hsum :=
    Finset.sum_lt_sum_of_nonempty himage (fun y hy => h y hy)
  simp only [← Finset.sum_mul, ← Finset.mul_sum, ← hA, ← hS'] at hsum
  exact (lt_irrefl _) hsum

/-- The equal-mass identity used with weak regularity in Proposition 3.1. -/
theorem sum_abs_sub_eq_twice_sum_posPart {X : Type*} (S : Finset X)
    (H : X → ℝ) (δ : ℝ) (hmass : ∑ x ∈ S, H x = (S.card : ℝ) * δ) :
    ∑ x ∈ S, |H x - δ| = 2 * ∑ x ∈ S, max (H x - δ) 0 := by
  have hpoint (x : X) : |H x - δ| = 2 * max (H x - δ) 0 - (H x - δ) := by
    rcases le_total (H x - δ) 0 with h | h
    · rw [abs_of_nonpos h, max_eq_right h]; ring
    · rw [abs_of_nonneg h, max_eq_left h]; ring
  simp only [hpoint, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hmass]
  simp [nsmul_eq_mul]

theorem equal_mass_l1_bound {X : Type*} (S : Finset X) (H : X → ℝ) {δ η : ℝ}
    (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (hmass : ∑ x ∈ S, H x = (S.card : ℝ) * δ)
    (hupper : ∀ x ∈ S, H x ≤ (1 + η) * δ) :
    ∑ x ∈ S, |H x - δ| ≤ 2 * η * δ * S.card := by
  rw [sum_abs_sub_eq_twice_sum_posPart S H δ hmass]
  have hsum : ∑ x ∈ S, max (H x - δ) 0 ≤ ∑ _x ∈ S, η * δ := by
    apply Finset.sum_le_sum
    intro x hx
    exact max_le (by linarith [hupper x hx]) (mul_nonneg hη hδ)
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  linarith


/-- The stage configuration in Proposition 3.1, indexed by positive (y).
The prime and its selector are both imposed on (qy+1). -/
def ContainsScaledConfiguration {ℓ : ℕ} (A : Finset ℤ)
    (P : Fin (ℓ + 1) → Polynomial ℤ) (selector : ℕ → Prop) (q : ℕ) : Prop :=
  ∃ (x : ℤ) (y : ℕ), 0 < y ∧ (q * y + 1).Prime ∧ selector (q * y + 1) ∧
    (∀ i, x + (rescalePolynomial (q : ℤ) (P i)).eval (y : ℤ) ∈ A) ∧
    Function.Injective (fun i => x + (rescalePolynomial (q : ℤ) (P i)).eval (y : ℤ))

/-- Pullback of a set to a one-based interval along a positive-step progression. -/
def progressionPullback (A : Finset ℤ) (a : ℤ) (L N : ℕ) : Finset ℤ :=
  (positiveInterval N).filter (fun x => a + (L : ℤ) * x ∈ A)

theorem progressionPullback_subset (A : Finset ℤ) (a : ℤ) (L N : ℕ) :
    progressionPullback A a L N ⊆ positiveInterval N :=
  Finset.filter_subset _ _

/-- The stage moduli (q) and (qL) give the exact same prime after affine
lifting, and distinct spatial sites stay distinct. -/
theorem lift_scaled_configuration {ℓ : ℕ} (P : Fin (ℓ + 1) → Polynomial ℤ)
    (hP : ∀ i, (P i).coeff 0 = 0) (selector : ℕ → Prop) (A : Finset ℤ)
    (a : ℤ) (q L N : ℕ) (hq : 0 < q) (hL : 0 < L) :
    ContainsScaledConfiguration (progressionPullback A a L N) P selector (q * L) →
      ContainsScaledConfiguration A P selector q := by
  rintro ⟨x, y, hy, hp, hret, hmem, hdist⟩
  have hq' : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
  have hL' : (L : ℤ) ≠ 0 := by exact_mod_cast hL.ne'
  have hlift (i : Fin (ℓ + 1)) :
      a + (L : ℤ) * (x + (rescalePolynomial ((q * L : ℕ) : ℤ) (P i)).eval (y : ℤ)) =
        a + (L : ℤ) * x + (rescalePolynomial (q : ℤ) (P i)).eval ((L * y : ℕ) : ℤ) := by
    push_cast
    rw [mul_add, eval_rescalePolynomial_mul _ _ _ (hP i) hq', add_assoc]
  refine ⟨a + (L : ℤ) * x, L * y, Nat.mul_pos hL hy, ?_, ?_, ?_, ?_⟩
  · simpa [Nat.mul_assoc] using hp
  · simpa [Nat.mul_assoc] using hret
  · intro i
    rw [← hlift]
    exact (Finset.mem_filter.mp (hmem i)).2
  · intro i j hij
    apply hdist
    exact mul_left_cancel₀ hL' (add_left_cancel ((hlift i).trans (hij.trans (hlift j).symm)))

theorem containsScaledConfiguration_one_iff {ℓ : ℕ}
    (P : Fin (ℓ + 1) → Polynomial ℤ) (hP : ∀ i, (P i).coeff 0 = 0)
    (A : Finset ℤ) (selector : ℕ → Prop) :
    ContainsScaledConfiguration A P selector 1 ↔ ContainsConfiguration A P selector := by
  have heval (i : Fin (ℓ + 1)) (y : ℤ) :
      (rescalePolynomial 1 (P i)).eval y = (P i).eval y := by
    simpa using (eval_rescalePolynomial 1 (P i) (hP i) y)
  constructor
  · rintro ⟨x, y, _, hp, hret, hmem, hdist⟩
    have harg : ((y + 1 : ℕ) : ℤ) - 1 = (y : ℤ) := by push_cast; ring
    refine ⟨x, y + 1, by simpa using hp, by simpa using hret, ?_, ?_⟩
    · simpa only [Nat.cast_one, heval, harg] using hmem
    · simpa only [Nat.cast_one, heval, harg] using hdist
  · rintro ⟨x, p, hp, hret, hmem, hdist⟩
    have hp₂ := hp.two_le
    have hy : 0 < p - 1 := by omega
    have hx : p - 1 + 1 = p := by omega
    have harg : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by omega
    refine ⟨x, p - 1, hy, by simpa [hx] using hp, by simpa [hx] using hret, ?_, ?_⟩
    · simpa only [Nat.cast_one, heval, harg] using hmem
    · simpa only [Nat.cast_one, heval, harg] using hdist


/-- Telescoping a finite product while keeping exactly (k-1) bounded
factors in every term. -/
theorem norm_prod_sub_le {k : ℕ} (f g : Fin k → ℂ) {U : ℝ}
    (hU : 0 ≤ U) (hf : ∀ i, ‖f i‖ ≤ U) (hg : ∀ i, ‖g i‖ ≤ U) :
    ‖(∏ i, f i) - ∏ i, g i‖ ≤ U ^ (k - 1) * ∑ i, ‖f i - g i‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
      cases k with
      | zero => simp
      | succ k =>
          rw [Fin.prod_univ_succ f, Fin.prod_univ_succ g, Fin.sum_univ_succ, Nat.succ_sub_one]
          let p := ∏ i : Fin (k + 1), f i.succ
          let q := ∏ i : Fin (k + 1), g i.succ
          have hp : ‖p‖ ≤ U ^ (k + 1) := by
            dsimp [p]
            rw [norm_prod]
            calc
              ∏ i : Fin (k + 1), ‖f i.succ‖ ≤ ∏ _i : Fin (k + 1), U :=
                Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hf i.succ)
              _ = U ^ (k + 1) := by simp
          have hi : ‖p - q‖ ≤ U ^ k * ∑ i : Fin (k + 1), ‖f i.succ - g i.succ‖ :=
            ih (fun i => f i.succ) (fun i => g i.succ)
              (fun i => hf i.succ) (fun i => hg i.succ)
          change ‖f 0 * p - g 0 * q‖ ≤ U ^ (k + 1) *
            (‖f 0 - g 0‖ + ∑ i : Fin (k + 1), ‖f i.succ - g i.succ‖)
          rw [show f 0 * p - g 0 * q = (f 0 - g 0) * p + g 0 * (p - q) by ring]
          calc
            ‖(f 0 - g 0) * p + g 0 * (p - q)‖ ≤
                ‖f 0 - g 0‖ * ‖p‖ + ‖g 0‖ * ‖p - q‖ := by
              simpa only [norm_mul] using norm_add_le ((f 0 - g 0) * p) (g 0 * (p - q))
            _ ≤ ‖f 0 - g 0‖ * U ^ (k + 1) + U *
                  (U ^ k * ∑ i : Fin (k + 1), ‖f i.succ - g i.succ‖) := by
              gcongr
              exact hg 0
            _ = U ^ (k + 1) *
                (‖f 0 - g 0‖ + ∑ i : Fin (k + 1), ‖f i.succ - g i.succ‖) := by
              rw [pow_succ]; ring

/-- Translating a finite spatial sum and bounding it by the total mass
on the common support of two inputs. -/
theorem sum_norm_translate_le (X S : Finset ℤ) (h : ℤ → ℂ) (t : ℤ)
    (hs : SupportedOn S h) :
    ∑ x ∈ X, ‖h (x + t)‖ ≤ ∑ z ∈ S, ‖h z‖ := by
  let f : ℤ → ℤ := fun x => x + t
  let Y := X.image f
  have hf : Function.Injective f := fun _ _ hxy => add_right_cancel hxy
  have hYX : ∑ z ∈ Y, ‖h z‖ = ∑ x ∈ X, ‖h (x + t)‖ :=
    Finset.sum_image (fun _ _ _ _ hxy => hf hxy)
  rw [← hYX]
  calc
    ∑ z ∈ Y, ‖h z‖ ≤ ∑ z ∈ S ∪ Y, ‖h z‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right
        (fun z _ _ => norm_nonneg (h z))
    _ = ∑ z ∈ S, ‖h z‖ :=
      (Finset.sum_subset Finset.subset_union_left (fun z _ hz => by rw [hs z hz, norm_zero])).symm

/-- The card of the manuscript's one-based integer interval. -/
@[simp] theorem card_positiveInterval (N : ℕ) : (positiveInterval N).card = N := by
  simp [positiveInterval, Int.card_Icc]

/-- Normalized telescope for the manuscript's exact unweighted counting form. -/
theorem unweighted_count_difference_le {k N M : ℕ} (X S : Finset ℤ)
    (P : Fin k → Polynomial ℤ) (f g : Fin k → ℤ → ℂ) {U : ℝ}
    (hU : 0 ≤ U) (hf : ∀ i z, ‖f i z‖ ≤ U) (hg : ∀ i z, ‖g i z‖ ≤ U)
    (hfs : ∀ i, SupportedOn S (f i)) (hgs : ∀ i, SupportedOn S (g i)) :
    ‖countingForm N M X P (fun _ => 1) f - countingForm N M X P (fun _ => 1) g‖ ≤
      U ^ (k - 1) / (N : ℝ) * ∑ i, ∑ z ∈ S, ‖f i z - g i z‖ := by
  classical
  by_cases hM : M = 0
  · simp [hM, countingForm]
    positivity
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM
  let F (x y : ℤ) := ∏ i, f i (x + (P i).eval y)
  let G (x y : ℤ) := ∏ i, g i (x + (P i).eval y)
  have hdiff (x y : ℤ) :
      ‖F x y - G x y‖ ≤ ∑ i, U ^ (k - 1) * ‖f i (x + (P i).eval y) -
        g i (x + (P i).eval y)‖ := by
    rw [← Finset.mul_sum]
    exact norm_prod_sub_le _ _ hU (fun i => hf i _) (fun i => hg i _)
  have hspace (y : ℤ) :
      ∑ x ∈ X, ∑ i, U ^ (k - 1) * ‖f i (x + (P i).eval y) -
        g i (x + (P i).eval y)‖ ≤
        ∑ i, U ^ (k - 1) * ∑ z ∈ S, ‖f i z - g i z‖ := by
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum (fun i _ => ?_)
    rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hU _)
    exact sum_norm_translate_le X S (fun z => f i z - g i z) ((P i).eval y)
      (fun z hz => by
        change f i z - g i z = 0
        rw [hfs i z hz, hgs i z hz, sub_self])
  have hnum :
      ‖∑ x ∈ X, ∑ y ∈ positiveInterval M, (F x y - G x y)‖ ≤
      (M : ℝ) * (U ^ (k - 1) * ∑ i, ∑ z ∈ S, ‖f i z - g i z‖) := by
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ y ∈ positiveInterval M, ∑ x ∈ X, ‖F x y - G x y‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum (fun _ _ => norm_sum_le _ _))
      _ ≤ ∑ y ∈ positiveInterval M,
          ∑ i, U ^ (k - 1) * ∑ z ∈ S, ‖f i z - g i z‖ := by
        exact Finset.sum_le_sum (fun y _ =>
          (Finset.sum_le_sum (fun x _ => hdiff x y)).trans (hspace y))
      _ = _ := by rw [← Finset.mul_sum]; simp [nsmul_eq_mul]
  simp only [countingForm, one_mul, ← sub_div, ← Finset.sum_sub_distrib,
    norm_div, Complex.norm_mul, Complex.norm_natCast]
  change ‖∑ x ∈ X, ∑ y ∈ positiveInterval M, (F x y - G x y)‖ / ((N : ℝ) * (M : ℝ)) ≤ _
  apply (div_le_div_of_nonneg_right hnum (by positivity)).trans_eq
  rw [div_eq_mul_inv, mul_inv, div_eq_mul_inv]
  calc
    _ = (M : ℝ) * (M : ℝ)⁻¹ *
        (U ^ (k - 1) * (N : ℝ)⁻¹ * ∑ i, ∑ z ∈ S, ‖f i z - g i z‖) := by ring
    _ = _ := by simp [hM']


/-- Every nonempty residue slice of the one-based interval is exactly a
one-based progression. Its length exceeds (N/q-1). -/
theorem residue_slice_as_progression {N q : ℕ} (hq : 0 < q)
    (r : ℤ) (hr : r ∈ (positiveInterval N).image (fun z => (z - 1) % (q : ℤ))) :
    ∃ (a : ℤ) (L : ℕ), 0 < L ∧ (N : ℝ) / (q : ℝ) - 1 < (L : ℝ) ∧
      ∀ z : ℤ, z ∈ positiveInterval N ∧ (z - 1) % (q : ℤ) = r ↔
        ∃ t ∈ positiveInterval L, a + (q : ℤ) * t = z := by
  obtain ⟨z₀, hz₀, hz₀r⟩ := Finset.mem_image.mp hr
  have hq' : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hr₀ : 0 ≤ r := hz₀r ▸ Int.emod_nonneg (z₀ - 1) hq'.ne'
  have hrq : r < (q : ℤ) := hz₀r ▸ Int.emod_lt_of_pos (z₀ - 1) hq'
  let a := r + 1 - (q : ℤ)
  have ha : a ≤ 0 := by dsimp [a]; omega
  let L := (((N : ℤ) - a) / (q : ℤ)).toNat
  have hNN : 0 ≤ (N : ℤ) - a := by omega
  have hLcast : (L : ℤ) = ((N : ℤ) - a) / (q : ℤ) :=
    Int.toNat_of_nonneg (Int.ediv_nonneg hNN hq'.le)
  have hright (t : ℤ) : a + (q : ℤ) * t ≤ N ↔ t ≤ (L : ℤ) := by
    rw [hLcast, Int.le_ediv_iff_mul_le hq']
    have heq : t * (q : ℤ) = (q : ℤ) * t := mul_comm _ _
    rw [heq]
    omega
  have hforward (z : ℤ) (hz : z ∈ positiveInterval N) (hzr : (z - 1) % (q : ℤ) = r) :
      ∃ t ∈ positiveInterval L, a + (q : ℤ) * t = z := by
    have hz' := Finset.mem_Icc.mp hz
    let t := (z - 1) / (q : ℤ) + 1
    have ht : 1 ≤ t := by
      dsimp [t]
      have := Int.ediv_nonneg (show 0 ≤ z - 1 by omega) hq'.le
      omega
    have hdt := Int.emod_add_ediv (z - 1) (q : ℤ)
    rw [hzr] at hdt
    have hval : a + (q : ℤ) * t = z := by dsimp [a, t]; linarith [hdt]
    exact ⟨t, Finset.mem_Icc.mpr ⟨ht, (hright t).mp (by simpa only [hval] using hz'.2)⟩, hval⟩
  have hL : 0 < L := by
    obtain ⟨t, ht, _⟩ := hforward z₀ hz₀ hz₀r
    have := Finset.mem_Icc.mp ht
    omega
  refine ⟨a, L, hL, ?_, ?_⟩
  · have hrem := Int.emod_lt_of_pos ((N : ℤ) - a) hq'
    have hdivEq := Int.emod_add_ediv ((N : ℤ) - a) (q : ℤ)
    rw [← hLcast] at hdivEq
    have hNq : (N : ℤ) < (q : ℤ) * ((L : ℤ) + 1) := by linarith [hrem, hdivEq, ha]
    have hNqR : (N : ℝ) < (q : ℝ) * ((L : ℝ) + 1) := by exact_mod_cast hNq
    have hdiv : (N : ℝ) / (q : ℝ) < (L : ℝ) + 1 :=
      (div_lt_iff₀ hqR).mpr (by simpa [mul_comm] using hNqR)
    linarith
  · intro z
    constructor
    · rintro ⟨hz, hzr⟩
      exact hforward z hz hzr
    · rintro ⟨t, ht, rfl⟩
      have ht' := Finset.mem_Icc.mp ht
      have hval : a + (q : ℤ) * t - 1 = r + (q : ℤ) * (t - 1) := by dsimp [a]; ring
      refine ⟨Finset.mem_Icc.mpr ⟨?_, (hright t).mpr ht'.2⟩, ?_⟩
      · have hpos := mul_nonneg hq'.le (show 0 ≤ t - 1 by omega)
        omega
      · rw [hval]
        simp [Int.add_emod, Int.emod_eq_of_lt hr₀ hrq]

/-- The initial rescaled progression in the recurrence proof, including
cardinality, containment, density, and the real length bound. -/
theorem exists_densest_residue_progression {N q : ℕ} (hN : 0 < N) (hq : 0 < q)
    (A : Finset ℤ) (hA : A ⊆ positiveInterval N) :
    ∃ (a : ℤ) (L : ℕ), 0 < L ∧ (N : ℝ) / (q : ℝ) - 1 < (L : ℝ) ∧
      (positiveInterval L).image (fun t => a + (q : ℤ) * t) ⊆ positiveInterval N ∧
      setDensity A N ≤ setDensity (progressionPullback A a q L) L := by
  classical
  have hI : (positiveInterval N).Nonempty := Finset.card_pos.mp (by simpa using hN)
  obtain ⟨r, hr, hcard⟩ := exists_dense_fiber A (positiveInterval N) hA hI
    (fun z => (z - 1) % (q : ℤ))
  obtain ⟨a, L, hL, hbound, hrep⟩ := residue_slice_as_progression hq r hr
  let f : ℤ → ℤ := fun t => a + (q : ℤ) * t
  have hq' : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
  have hfi : Function.Injective f := fun x y hxy => mul_left_cancel₀ hq' (add_left_cancel hxy)
  have hImage : (positiveInterval L).image f =
      (positiveInterval N).filter (fun z => (z - 1) % (q : ℤ) = r) := by
    ext z
    simp only [Finset.mem_image, Finset.mem_filter]
    exact (hrep z).symm
  have hPullImage : (progressionPullback A a q L).image f =
      A.filter (fun z => (z - 1) % (q : ℤ) = r) := by
    ext z
    constructor
    · intro hz
      obtain ⟨t, ht, heq⟩ := Finset.mem_image.mp hz
      obtain ⟨htI, hmem⟩ := Finset.mem_filter.mp ht
      have hz' := (hrep z).mpr ⟨t, htI, heq⟩
      exact Finset.mem_filter.mpr ⟨heq ▸ hmem, hz'.2⟩
    · intro hz
      obtain ⟨hzA, hzr⟩ := Finset.mem_filter.mp hz
      obtain ⟨t, ht, heq⟩ := (hrep z).mp ⟨hA hzA, hzr⟩
      exact Finset.mem_image.mpr ⟨t, Finset.mem_filter.mpr ⟨ht, heq.symm ▸ hzA⟩, heq⟩
  rw [← hImage, ← hPullImage, Finset.card_image_of_injective _ hfi,
    Finset.card_image_of_injective _ hfi, card_positiveInterval, card_positiveInterval] at hcard
  refine ⟨a, L, hL, hbound, ?_, ?_⟩
  · change (positiveInterval L).image f ⊆ positiveInterval N
    rw [hImage]
    exact Finset.filter_subset _ _
  · unfold setDensity
    have hcross : (A.card : ℝ) * (L : ℝ) ≤ (progressionPullback A a q L).card * (N : ℝ) := by
      exact_mod_cast hcard
    exact (div_le_div_iff₀ (by exact_mod_cast hN) (by exact_mod_cast hL)).mpr hcross


/-- The equal-density model function, with zero extension off the interval. -/
noncomputable def densityModel (N : ℕ) (δ : ℝ) (z : ℤ) : ℂ :=
  if z ∈ positiveInterval N then (δ : ℂ) else 0

/-- A discrepancy larger than the telescope bound forces a point of
increased density in one of the weak regularity factors. For the manuscript's
conditional expectations, this point lies in the required denser atom. -/
theorem exists_density_increase_of_count_discrepancy {k N M : ℕ}
    (hN : 0 < N) (P : Fin k → Polynomial ℤ) (H : Fin k → ℤ → ℝ) {δ η : ℝ}
    (hδ : 0 ≤ δ) (hη : 0 ≤ η) (hH₀ : ∀ i z, 0 ≤ H i z)
    (hHsupp : ∀ i z, z ∉ positiveInterval N → H i z = 0)
    (hmass : ∀ i, ∑ z ∈ positiveInterval N, H i z = (N : ℝ) * δ)
    (hdisc : (k : ℝ) * (2 * η * δ) * ((1 + η) * δ) ^ (k - 1) <
      ‖countingForm N M (positiveInterval N) P (fun _ => 1) (fun i z => (H i z : ℂ)) -
       countingForm N M (positiveInterval N) P (fun _ => 1) (fun _ => densityModel N δ)‖) :
    ∃ i z, z ∈ positiveInterval N ∧ (1 + η) * δ < H i z := by
  classical
  by_contra! hupper
  let U := (1 + η) * δ
  have hU : 0 ≤ U := mul_nonneg (by linarith) hδ
  have hf (i : Fin k) (z : ℤ) : ‖(H i z : ℂ)‖ ≤ U := by
    rw [Complex.norm_of_nonneg (hH₀ i z)]
    by_cases hz : z ∈ positiveInterval N
    · exact hupper i z hz
    · rw [hHsupp i z hz]
      exact hU
  have hg (z : ℤ) : ‖densityModel N δ z‖ ≤ U := by
    unfold densityModel
    split_ifs with hz
    · rw [Complex.norm_of_nonneg hδ]
      exact le_mul_of_one_le_left hδ (by linarith)
    · simpa using hU
  have ht := unweighted_count_difference_le (N := N) (M := M)
    (positiveInterval N) (positiveInterval N) P
    (fun i z => (H i z : ℂ)) (fun _ => densityModel N δ) hU hf (fun _ => hg)
    (fun i z hz => by simp [hHsupp i z hz])
    (fun _ z hz => by simp [densityModel, hz])
  have hfamilysum : ∑ i : Fin k, ∑ z ∈ positiveInterval N, ‖(H i z : ℂ) - densityModel N δ z‖ ≤
      (k : ℝ) * (2 * η * δ * N) := by
    calc
      _ ≤ ∑ _i : Fin k, (2 * η * δ * N) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        have hi := equal_mass_l1_bound (positiveInterval N) (H i) hδ hη
          (by simpa using hmass i) (hupper i)
        simp only [card_positiveInterval] at hi
        convert hi using 1
        apply Finset.sum_congr rfl
        intro z hz
        simp only [densityModel, if_pos hz, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      _ = _ := by simp [nsmul_eq_mul]
  have hscaled := mul_le_mul_of_nonneg_left hfamilysum
    (show 0 ≤ U ^ (k - 1) / (N : ℝ) by positivity)
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have heq : U ^ (k - 1) / (N : ℝ) * ((k : ℝ) * (2 * η * δ * N)) =
      (k : ℝ) * (2 * η * δ) * U ^ (k - 1) := by
    field_simp
    ring
  exact (not_lt_of_ge ((ht.trans hscaled).trans_eq heq)) hdisc


private theorem rpow_density_horizon (η δ b : ℝ) (hδ : 0 < δ) (hb : 0 < b) :
    b ^ (Real.log δ⁻¹ / Real.log (1 + η) + 1) =
      b * δ ^ (-(Real.log b / Real.log (1 + η))) := by
  rw [Real.rpow_add hb, Real.rpow_one, Real.rpow_def_of_pos hb, Real.rpow_def_of_pos hδ,
    Real.log_inv, mul_comm b]
  congr 1
  congr 1
  ring

/-- The manuscript's (delta^{-O(1)}) loss in the bound on the logarithmic modulus. -/
theorem modulus_growth_to_density_power {η δ b : ℝ} (hη : 0 < η)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hb : 1 ≤ b) {i : ℕ}
    (hi : i ≤ densityIterationSteps η δ) :
    b ^ i ≤ b * δ ^ (-(Real.log b / Real.log (1 + η))) := by
  have hbound : (i : ℝ) ≤ Real.log δ⁻¹ / Real.log (1 + η) + 1 :=
    (show (i : ℝ) ≤ (densityIterationSteps η δ : ℝ) by exact_mod_cast hi).trans
      (densityIterationSteps_le hη hδ hδ₁)
  rw [← rpow_density_horizon η δ b hδ (by linarith), ← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le hb hbound

/-- The manuscript's (delta^{O(1)}) lower bound for the (i)-th power of the
logarithmic length contraction. -/
theorem length_contraction_to_density_power {η δ a : ℝ} (hη : 0 < η)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (ha : 0 < a) (ha₁ : a ≤ 1) {i : ℕ}
    (hi : i ≤ densityIterationSteps η δ) :
    a * δ ^ (-(Real.log a / Real.log (1 + η))) ≤ a ^ i := by
  have hbound : (i : ℝ) ≤ Real.log δ⁻¹ / Real.log (1 + η) + 1 :=
    (show (i : ℝ) ≤ (densityIterationSteps η δ : ℝ) by exact_mod_cast hi).trans
      (densityIterationSteps_le hη hδ hδ₁)
  rw [← rpow_density_horizon η δ a hδ ha, ← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_ge ha ha₁ hbound

/-- Raising the stage modulus keeps its original divisibility and introduces
no new prime factors. -/
theorem modulus_power_preserves_prime_support {w q L j : ℕ} (hj : 0 < j)
    (hL : L ∣ q) (hsmooth : ∀ p : ℕ, p.Prime → p ∣ q → p ≤ w) :
    L ∣ q ^ j ∧ ∀ p : ℕ, p.Prime → p ∣ q ^ j → p ≤ w := by
  exact ⟨hL.trans (dvd_pow_self _ hj.ne'), fun p hp hdvd => hsmooth p hp (hp.dvd_of_dvd_pow hdvd)⟩

theorem log_modulus_after_power {q B Bmax : ℕ} (hq : 0 < q) (hB : B ≤ Bmax) :
    Real.log (q ^ (B + 1) : ℕ) ≤ (Bmax + 1 : ℝ) * Real.log (q : ℝ) := by
  rw [Nat.cast_pow, Real.log_pow, Nat.cast_add, Nat.cast_one]
  have hq₁ : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_succ hB)
    (Real.log_nonneg hq₁)

/-- A floor-aware logarithmic lower bound for the manuscript's parameter length. -/
theorem log_parameterLength_lower {N q d : ℕ} (hN : 0 < N) (hq : 0 < q)
    (hscale : 2 ≤ ((N : ℝ) / (q : ℝ) ^ (d - 1)) ^ ((d : ℝ)⁻¹)) :
    (d : ℝ)⁻¹ * (Real.log N - ((d - 1 : ℕ) : ℝ) * Real.log q) - Real.log 2 ≤
      Real.log (parameterLength N q d : ℝ) := by
  let x := ((N : ℝ) / (q : ℝ) ^ (d - 1)) ^ ((d : ℝ)⁻¹)
  have hx : 2 ≤ x := hscale
  have hf : x < (parameterLength N q d : ℝ) + 1 :=
    Nat.lt_floor_add_one x
  have hx₂ : x / 2 ≤ (parameterLength N q d : ℝ) := by linarith
  have hlog := Real.log_le_log (show 0 < x / 2 by linarith) hx₂
  have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  rw [Real.log_div (by linarith : x ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)] at hlog
  dsimp [x] at hlog
  rw [Real.log_rpow (div_pos hN' (pow_pos hq' _)), Real.log_div hN'.ne'
    (pow_pos hq' _).ne', Real.log_pow] at hlog
  exact hlog

/-- Taking logarithms of the length conclusion of Proposition 3.1, retaining
the floor loss and all constants. -/
theorem log_incremented_length_lower {N N' q d r : ℕ} {δ c C : ℝ}
    (hN : 0 < N) (hq : 0 < q) (hδ : 0 < δ) (hc : 0 < c)
    (hscale : 2 ≤ ((N : ℝ) / (q : ℝ) ^ (d - 1)) ^ ((d : ℝ)⁻¹))
    (hinc : c * (q : ℝ) ^ (-C) * δ ^ C * (parameterLength N q d : ℝ)^r ≤ (N' : ℝ)) :
    (r : ℝ) / d * Real.log N -
      (((r : ℝ) / d) * ((d - 1 : ℕ) : ℝ) + C) * Real.log q + C * Real.log δ +
      Real.log c - (r : ℝ) * Real.log 2 ≤ Real.log N' := by
  have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hMp : (0 : ℝ) < (parameterLength N q d : ℝ) := by
    have hf : ((N : ℝ) / (q : ℝ) ^ (d - 1)) ^ ((d : ℝ)⁻¹) <
        (parameterLength N q d : ℝ) + 1 := Nat.lt_floor_add_one _
    linarith
  have hpq := Real.rpow_pos_of_pos hq' (-C)
  have hpδ := Real.rpow_pos_of_pos hδ C
  have hpos := mul_pos (mul_pos (mul_pos hc hpq) hpδ) (pow_pos hMp r)
  have hlog := Real.log_le_log hpos hinc
  rw [Real.log_mul (mul_pos (mul_pos hc hpq) hpδ).ne' (pow_pos hMp r).ne',
    Real.log_mul (mul_pos hc hpq).ne' hpδ.ne', Real.log_mul hc.ne' hpq.ne',
    Real.log_rpow hq', Real.log_rpow hδ, Real.log_pow] at hlog
  have hlen := mul_le_mul_of_nonneg_left (log_parameterLength_lower hN hq hscale)
    (Nat.cast_nonneg r : (0 : ℝ) ≤ (r : ℝ))
  simp only [div_eq_mul_inv] at *
  linarith only [hlen, hlog]


/-- Least common multiple of the integers (1,ldots,w). -/
def initialModulus (w : ℕ) : ℕ := (Finset.Icc 1 w).lcm id

/-- Prime factor bound used with positive moduli. -/
def ModulusSmooth (w q : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ q → p ≤ w

/-- Uniform constants in Proposition 3.1. The positive multiplier
`lengthConstant` makes its lower Vinogradov bound explicit. -/
structure DensityIncrementConstants where
  c : ℝ
  η : ℝ
  K : ℝ
  E : ℝ
  C₁ : ℝ
  lengthConstant : ℝ
  Bmax : ℕ
  Nmin : ℕ
  c_pos : 0 < c
  η_pos : 0 < η
  K_pos : 0 < K
  E_pos : 0 < E
  C₁_pos : 0 < C₁
  lengthConstant_pos : 0 < lengthConstant

/-- The uniform conclusion of Proposition 3.1 for fixed constants,
a fixed polynomial family, and a fixed prime selector. -/
def DensityIncrementAtParameters {ℓ : ℕ} (P : Fin (ℓ + 1) → Polynomial ℤ)
    (selector : ℕ → Prop) (d r : ℕ) (c : DensityIncrementConstants) : Prop :=
  ∀ (N q w : ℕ) (A : Finset ℤ), c.Nmin ≤ N → 0 < N → 0 < q →
    A ⊆ positiveInterval N →
    let δ := setDensity A N
    0 < δ → δ ≤ 1 →
    c.K * δ ^ (-c.E) ≤ (w : ℝ) → (w : ℝ) ≤ Real.log N ^ c.c →
    initialModulus w ∣ q → ModulusSmooth w q → Real.log q ≤ (w : ℝ)^2 →
    ¬ ContainsScaledConfiguration A P selector q →
    ∃ (B : ℕ) (a : ℤ) (N' : ℕ), 1 ≤ B ∧ B ≤ c.Bmax ∧
      (positiveInterval N').image (fun z => a + ((q ^ B : ℕ) : ℤ) * z) ⊆
        positiveInterval N ∧
      (1 + c.η) * δ * N' ≤ (progressionPullback A a (q ^ B) N').card ∧
      c.lengthConstant * (q : ℝ) ^ (-c.C₁) * δ ^ c.C₁ *
        (parameterLength N q d : ℝ)^r ≤ (N' : ℝ)

/-- Exact fixed-data assertion of Proposition 3.1 after the degrees are read
from the family; the selected Heisenberg primes are an instance of `selector`. -/
def DensityIncrementFor {ℓ : ℕ} (P : Fin (ℓ + 1) → Polynomial ℤ)
    (selector : ℕ → Prop) : Prop :=
  ∃ c : DensityIncrementConstants,
    DensityIncrementAtParameters P selector (P (Fin.last ℓ)).natDegree
      (P 1).natDegree c

private structure DensityStage where
  N : ℕ
  q : ℕ
  A : Finset ℤ
  hN : 0 < N
  hq : 0 < q
  hA : A ⊆ positiveInterval N

theorem setDensity_le_one {N : ℕ} {A : Finset ℤ} (hN : 0 < N)
    (hA : A ⊆ positiveInterval N) : setDensity A N ≤ 1 := by
  rw [setDensity, div_le_iff₀ (show (0 : ℝ) < N by exact_mod_cast hN), one_mul]
  have h := Finset.card_le_card hA
  simpa using h

/-- A finite-scale consequence of Proposition 3.1. The three numerical
inequalities in `resource` are the remaining parameter-selection obligations
when this reduction is used to prove the asymptotic Theorem 1.2. -/
theorem recurrence_of_density_increment_at_scale {ℓ d r N w q₀ : ℕ}
    (P : Fin (ℓ + 1) → Polynomial ℤ) (hP : ∀ i, (P i).coeff 0 = 0)
    (selector : ℕ → Prop) (c : DensityIncrementConstants)
    (increment : DensityIncrementAtParameters P selector d r c)
    (A : Finset ℤ) (hN : 0 < N) (hA : A ⊆ positiveInterval N)
    (hq₀ : 0 < q₀) (hdiv : initialModulus w ∣ q₀) (hsmooth : ModulusSmooth w q₀)
    (hr : r ≤ d) (hδ : 0 < setDensity A N)
    (hw : c.K * setDensity A N ^ (-c.E) ≤ (w : ℝ))
    (loss L₀ : ℝ) (hloss : 0 ≤ loss)
    (hstart : ∀ L : ℕ, (N : ℝ) / q₀ - 1 < (L : ℝ) → L₀ ≤ Real.log L)
    (hlossBound : (((r : ℝ) / d) * ((d - 1 : ℕ) : ℝ) + c.C₁) * (w : ℝ)^2 -
      c.C₁ * Real.log (setDensity A N) - Real.log c.lengthConstant + (r : ℝ) * Real.log 2 ≤ loss)
    (resource : ∀ (i n q : ℕ), i < densityIterationSteps c.η (setDensity A N) →
      0 < n → 0 < q →
      Real.log q ≤ ((c.Bmax : ℝ) + 1)^i * Real.log q₀ →
      ((r : ℝ) / d)^i * L₀ - (i : ℝ) * loss ≤ Real.log n →
      c.Nmin ≤ n ∧ (w : ℝ) ≤ Real.log n ^ c.c ∧ Real.log q ≤ (w : ℝ)^2 ∧
        2 ≤ ((n : ℝ) / (q : ℝ) ^ (d - 1)) ^ ((d : ℝ)⁻¹)) :
    ContainsConfiguration A P selector := by
  classical
  by_contra habsent
  let δ := setDensity A N
  let J := densityIterationSteps c.η δ
  let contraction := (r : ℝ) / d
  let growth := (c.Bmax : ℝ) + 1
  have hcon₀ : 0 ≤ contraction := by positivity
  have hcon₁ : contraction ≤ 1 := by
    by_cases hd : d = 0
    · simp [contraction, hd]
    · apply (div_le_iff₀ (show (0 : ℝ) < d by exact_mod_cast Nat.pos_of_ne_zero hd)).mpr
      simpa using (show (r : ℝ) ≤ (d : ℝ) by exact_mod_cast hr)
  have hgrowth : 0 ≤ growth := by positivity
  obtain ⟨a₀, N₀, hN₀, hn₀length, _, hδ₀⟩ := exists_densest_residue_progression hN hq₀ A hA
  let s₀ : DensityStage := ⟨N₀, q₀, progressionPullback A a₀ q₀ N₀, hN₀, hq₀,
    progressionPullback_subset _ _ _ _⟩
  let valid (s : DensityStage) : Prop :=
    initialModulus w ∣ s.q ∧ ModulusSmooth w s.q ∧
      ¬ ContainsScaledConfiguration s.A P selector s.q
  let density (s : DensityStage) := setDensity s.A s.N
  let logModulus (s : DensityStage) := Real.log (s.q : ℝ)
  let logLength (s : DensityStage) := Real.log (s.N : ℝ)
  have hvalid₀ : valid s₀ := by
    refine ⟨hdiv, hsmooth, ?_⟩
    intro hconf
    apply habsent
    apply (containsScaledConfiguration_one_iff P hP A selector).mp
    apply lift_scaled_configuration P hP selector A a₀ 1 q₀ N₀ Nat.one_pos hq₀
    simpa [s₀] using hconf
  have hinit : L₀ ≤ logLength s₀ := hstart N₀ hn₀length
  have hstep (i : ℕ) (s : DensityStage) (hi : i < J) :
      valid s → (1 + c.η)^i * density s₀ ≤ density s →
      logModulus s ≤ growth^i * logModulus s₀ →
      contraction^i * logLength s₀ - (i : ℝ) * loss ≤ logLength s →
      ∃ t, valid t ∧ (1 + c.η) * density s ≤ density t ∧
        logModulus t ≤ growth * logModulus s ∧
        contraction * logLength s - loss ≤ logLength t := by
    rintro ⟨hL, hsm, hno⟩ hdens hqsize hnsize
    have hpow : 1 ≤ (1 + c.η)^i := one_le_pow₀ (by linarith [c.η_pos])
    have hdens' : δ ≤ density s := calc
      δ ≤ density s₀ := hδ₀
      _ ≤ (1 + c.η)^i * density s₀ := le_mul_of_one_le_left (hδ.le.trans hδ₀) hpow
      _ ≤ density s := hdens
    have hsδ : 0 < density s := hδ.trans_le hdens'
    have hsδ₁ : density s ≤ 1 := setDensity_le_one s.hN s.hA
    have hlength : contraction^i * L₀ - (i : ℝ) * loss ≤ logLength s :=
      (sub_le_sub_right (mul_le_mul_of_nonneg_left hinit (pow_nonneg hcon₀ _)) _).trans hnsize
    obtain ⟨hsN, hsw, hsq, hscale⟩ := resource i s.N s.q hi s.hN s.hq hqsize hlength
    have hsmallδ : density s ^ (-c.E) ≤ δ ^ (-c.E) :=
      Real.rpow_le_rpow_of_nonpos hδ hdens' (neg_nonpos.mpr c.E_pos.le)
    have hsmin : c.K * density s ^ (-c.E) ≤ (w : ℝ) :=
      (mul_le_mul_of_nonneg_left hsmallδ c.K_pos.le).trans hw
    obtain ⟨B, a, N', _, hB, _, hgain, hlen⟩ :=
      increment s.N s.q w s.A hsN s.hN s.hq s.hA hsδ hsδ₁ hsmin hsw hL hsm hsq hno
    have hN' : 0 < N' := by
      have hfloor : 0 < (parameterLength s.N s.q d : ℝ) := by
        have hlt : ((s.N : ℝ) / (s.q : ℝ) ^ (d - 1)) ^ ((d : ℝ)⁻¹) <
            (parameterLength s.N s.q d : ℝ) + 1 := Nat.lt_floor_add_one _
        linarith
      have hpos : 0 < c.lengthConstant * (s.q : ℝ) ^ (-c.C₁) *
          density s ^ c.C₁ * (parameterLength s.N s.q d : ℝ)^r :=
        mul_pos (mul_pos (mul_pos c.lengthConstant_pos (Real.rpow_pos_of_pos
          (by exact_mod_cast s.hq) _)) (Real.rpow_pos_of_pos hsδ _)) (pow_pos hfloor _)
      exact_mod_cast hpos.trans_le hlen
    let t : DensityStage := ⟨N', s.q ^ (B + 1), progressionPullback s.A a (s.q ^ B) N', hN',
      pow_pos s.hq _, progressionPullback_subset _ _ _ _⟩
    refine ⟨t, ?_, ?_, log_modulus_after_power s.hq hB, ?_⟩
    · obtain ⟨htL, htsm⟩ := modulus_power_preserves_prime_support (Nat.succ_pos B) hL hsm
      refine ⟨htL, htsm, ?_⟩
      intro hconf
      apply hno
      apply lift_scaled_configuration P hP selector s.A a s.q (s.q^B) N' s.hq (pow_pos s.hq _)
      simpa [t, pow_succ, Nat.mul_comm] using hconf
    · change (1 + c.η) * density s ≤
        ((progressionPullback s.A a (s.q ^ B) N').card : ℝ) / (N' : ℝ)
      exact (le_div_iff₀ (show (0 : ℝ) < N' by exact_mod_cast hN')).mpr hgain
    · have hnew := log_incremented_length_lower s.hN s.hq hsδ c.lengthConstant_pos hscale hlen
      have hqbound := mul_le_mul_of_nonneg_left hsq
        (show 0 ≤ contraction * ((d - 1 : ℕ) : ℝ) + c.C₁ by
          exact add_nonneg (mul_nonneg hcon₀ (Nat.cast_nonneg _)) c.C₁_pos.le)
      have hdbound := mul_le_mul_of_nonneg_left (Real.log_le_log hδ hdens') c.C₁_pos.le
      change contraction * Real.log (s.N : ℝ) - loss ≤ Real.log (N' : ℝ)
      linarith only [hnew, hqbound, hdbound, hlossBound]
  obtain ⟨s, _, hfinal, _, _⟩ := exists_density_iteration_state valid density logModulus logLength
    s₀ J c.η_pos.le hcon₀ hcon₁ hgrowth hloss hvalid₀ hstep J le_rfl
  have hlast := mul_le_mul_of_nonneg_left hδ₀ (pow_nonneg (show 0 ≤ 1 + c.η by linarith [c.η_pos]) J)
  exact (not_lt_of_ge (setDensity_le_one s.hN s.hA))
    ((one_lt_density_after_iterationSteps c.η_pos hδ).trans_le (hlast.trans hfinal))

end NilBohr
