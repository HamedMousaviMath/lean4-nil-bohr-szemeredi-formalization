import NilBohr.GreenTaoLeibman
import NilBohr.TwistedOrbit

/-! The binomial smoothness bounds from the quantitative Leibman theorem
applied to real polynomial representatives. -/

namespace NilBohr

private theorem leibmanCircleDifference_add (i : ℕ) (f g : ℕ → Circle) (n : ℕ) :
    leibmanCircleDifference i (fun t => f t + g t) n =
      leibmanCircleDifference i f n + leibmanCircleDifference i g n := by
  induction i generalizing f g with
  | zero => rfl
  | succ i ih =>
    simp only [leibmanCircleDifference]
    have h : (fun t => (f (t+1) + g (t+1)) - (f t + g t)) =
        fun t => (f (t+1) - f t) + (g (t+1) - g t) := by
      funext t
      abel
    rw [h, ih]

private theorem leibmanCircleDifference_const (i : ℕ) (c : Circle) (n : ℕ) :
    leibmanCircleDifference i (fun _ => c) n = if i = 0 then c else 0 := by
  induction i generalizing c with
  | zero => simp [leibmanCircleDifference]
  | succ i ih => simp [leibmanCircleDifference, ih]

private theorem leibmanCircleDifference_sum {ι : Type*} (i n : ℕ) (s : Finset ι)
    (f : ι → ℕ → Circle) :
    leibmanCircleDifference i (fun t => ∑ j ∈ s, f j t) n =
      ∑ j ∈ s, leibmanCircleDifference i (f j) n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [leibmanCircleDifference_const]
  | insert j s hj ih => simp [hj, leibmanCircleDifference_add, ih]

private theorem leibmanCircleDifference_choose (i j : ℕ) (c : ℝ) :
    leibmanCircleDifference i (fun t => ((c * (t.choose j : ℝ) : ℝ) : Circle)) 0 =
      if i = j then (c : Circle) else 0 := by
  induction i generalizing j with
  | zero =>
    cases j <;> simp [leibmanCircleDifference]
  | succ i ih =>
    cases j with
    | zero => simp [leibmanCircleDifference, leibmanCircleDifference_const]
    | succ j =>
      rw [leibmanCircleDifference]
      have heq : (fun t : ℕ => ((c * ((t+1).choose (j+1) : ℝ) : ℝ) : Circle) -
          ((c * (t.choose (j+1) : ℝ) : ℝ) : Circle)) =
          (fun t : ℕ => ((c * (t.choose j : ℝ) : ℝ) : Circle)) := by
        funext t
        rw [← AddCircle.coe_sub, Nat.choose_succ_succ, Nat.cast_add, mul_add, add_sub_cancel_right]
      rw [heq, ih]
      simp only [Nat.succ_inj]

/-- The forward differences at zero read off precisely the nonconstant
binomial coefficients, with the constant term ignored. -/
theorem leibmanCircleDifference_binomial (d : ℕ) (b₀ : ℝ) (b : ℕ → ℝ)
    {i : ℕ} (hi : i < d) :
    leibmanCircleDifference (i+1) (fun t => ((b₀ + realBinomialPhase d b t : ℝ) : Circle)) 0 =
      (b (i+1) : Circle) := by
  classical
  have hfun : (fun t : ℕ => ((b₀ + realBinomialPhase d b t : ℝ) : Circle)) =
      fun t => (b₀ : Circle) +
        ∑ j ∈ Finset.range d, ((b (j+1) * (t.choose (j+1) : ℝ) : ℝ) : Circle) := by
    funext t
    rw [realBinomialPhase, AddCircle.coe_add]
    congr 1
    exact map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) _ _
  rw [hfun, leibmanCircleDifference_add, leibmanCircleDifference_const,
    leibmanCircleDifference_sum]
  simp only [Nat.add_one_ne_zero, if_false, zero_add, leibmanCircleDifference_choose, Nat.succ_inj]
  simp [Finset.sum_ite_eq, hi]

theorem leibmanCircleDifference_linear (a b : ℝ) :
    leibmanCircleDifference 1 (fun t => ((a + b*(t : ℝ) : ℝ) : Circle)) 0 = (b : Circle) := by
  simp [leibmanCircleDifference, ← AddCircle.coe_sub]

end NilBohr
