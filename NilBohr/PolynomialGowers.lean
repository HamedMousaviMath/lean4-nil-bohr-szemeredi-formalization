import NilBohr.GowersMultiplier

/-! Ordinary polynomial phases and interval Gowers quantities. -/

open Polynomial

namespace NilBohr

/-- A nonzero polynomial minus its real translate has smaller degree. -/
theorem degree_sub_translate_lt {p : Polynomial ℝ} (hp : p ≠ 0) (t : ℝ) :
    (p - p.comp (X + C t)).degree < p.degree := by
  have hn : p.comp (X + C t) ≠ 0 := by
    intro h
    rcases comp_eq_zero_iff.mp h with h | ⟨_, h⟩
    · exact hp h
    · have hh := congrArg natDegree h
      simp at hh
  apply degree_sub_lt ?_ hp ?_
  · rw [degree_eq_natDegree hp, degree_eq_natDegree hn, natDegree_comp]
    simp
  · rw [leadingCoeff_comp (by simp : (X + C t : Polynomial ℝ).natDegree ≠ 0)]
    simp [(monic_X_add_C t).leadingCoeff]

private theorem cubeDifference_sub (f g : ℤ → ℝ) (hs : List ℤ) (x : ℤ) :
    cubeDifference hs (fun n => f n - g n) x =
      cubeDifference hs f x - cubeDifference hs g x := by
  induction hs generalizing x with
  | nil => rfl
  | cons t ts ih => simp only [cubeDifference, ih]; ring

private theorem cubeDifference_translate (f : ℤ → ℝ) (hs : List ℤ) (x t : ℤ) :
    cubeDifference hs (fun n => f (n+t)) x = cubeDifference hs f (x+t) := by
  induction hs generalizing x with
  | nil => rfl
  | cons u us ih =>
      simp only [cubeDifference, ih, show x+u+t = x+t+u by ring]

private theorem cubeDifference_polynomial_zero (p : Polynomial ℝ) (hs : List ℤ)
    (hp : p.degree < (hs.length : WithBot ℕ)) (x : ℤ) :
    cubeDifference hs (fun n => p.eval (n : ℝ)) x = 0 := by
  induction hs generalizing p x with
  | nil =>
      by_cases hz : p = 0
      · simp [hz, cubeDifference]
      · rw [degree_eq_natDegree hz] at hp
        change (p.natDegree : WithBot ℕ) < ((0 : ℕ) : WithBot ℕ) at hp
        exact (Nat.not_lt_zero _ (WithBot.coe_lt_coe.mp hp)).elim
  | cons t ts ih =>
      by_cases hz : p = 0
      · have h₀ : (0 : Polynomial ℝ).degree < (ts.length : WithBot ℕ) := by
          rw [degree_zero]
          exact WithBot.bot_lt_coe _
        rw [hz, cubeDifference, ih 0 h₀ x, ih 0 h₀ (x+t), sub_self]
      let Q := p - p.comp (X + C (t : ℝ))
      have hQ : Q.degree < (ts.length : WithBot ℕ) := by
        have hdeg := degree_sub_translate_lt hz (t : ℝ)
        rw [degree_eq_natDegree hz] at hp hdeg
        apply hdeg.trans_le
        change (p.natDegree : WithBot ℕ) ≤ (ts.length : WithBot ℕ)
        norm_cast at hp ⊢
        exact Nat.lt_succ_iff.mp hp
      have heval : (fun n : ℤ => Q.eval (n : ℝ)) =
          (fun n : ℤ => p.eval (n : ℝ) - p.eval ((n+t : ℤ) : ℝ)) := by
        funext n
        simp [Q, eval_comp]
      have h := ih Q hQ x
      rw [heval, cubeDifference_sub] at h
      rw [cubeDifference, ← cubeDifference_translate (fun n : ℤ => p.eval (n : ℝ)) ts x t]
      exact h

/-- Multiplication by a polynomial phase of degree below the cube order leaves
the exact normalized interval Gowers quantity unchanged. -/
theorem normalizedGowers_mul_polynomial_phase (L U : ℤ) (S : ℕ) (P : Polynomial ℝ)
    (hP : P.natDegree < S) (f : ℤ → ℂ) :
    normalizedGowers S L U (fun n => f n * phaseExponential (P.eval (n : ℝ))) =
      normalizedGowers S L U f := by
  let a : ℤ → ℝ := fun n => P.eval (n : ℝ)
  have hzero : zeroOutside L U (fun n => f n * phaseExponential (a n)) =
      (fun n => zeroOutside L U f n * phaseExponential (a n)) := by
    funext n
    unfold zeroOutside
    split_ifs <;> simp
  change normalizedGowers S L U (fun n => f n * phaseExponential (a n)) = _
  have heq : gowersCubePower S L U (fun n => f n * phaseExponential (a n)) =
      gowersCubePower S L U f := by
    let dirs (h : Fin S → Fin (2*(U-L).toNat+1)) : List ℤ :=
      List.ofFn (fun j => ((h j).val : ℤ) - ((U-L).toNat : ℤ))
    change (∑ x ∈ Finset.Icc L U, ∑ h, cubeProduct (dirs h)
      (zeroOutside L U (fun n => f n*phaseExponential (a n))) x) =
      ∑ x ∈ Finset.Icc L U, ∑ h, cubeProduct (dirs h) (zeroOutside L U f) x
    rw [hzero]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun h _ => ?_
    have hd : P.degree < ((dirs h).length : WithBot ℕ) := by
      refine degree_le_natDegree.trans_lt ?_
      simpa [dirs] using (WithBot.coe_lt_coe.mpr hP)
    simp only [cubeProduct_mul, cubeProduct_phaseExponential, a,
      cubeDifference_polynomial_zero P _ hd x, phaseExponential_zero, mul_one]
  unfold normalizedGowers
  rw [heq]

end NilBohr
