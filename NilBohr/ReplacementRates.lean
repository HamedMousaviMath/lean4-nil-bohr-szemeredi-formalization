import NilBohr.PhaseReplacement

/-! The number of dual replacements is fixed. Its losses can therefore be
bounded by a fixed power of the original count size. -/

namespace NilBohr

noncomputable def phaseReplacementCoefficient (a K D : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => a * ((phaseReplacementCoefficient a K D n)^2 / K)^D

noncomputable def phaseReplacementRate (a K D δ : ℝ) (j : ℕ) : ℝ :=
  phaseReplacementCoefficient a K D j * δ^((2*D)^j : ℝ)

theorem phaseReplacementCoefficient_pos {a K D : ℝ} (ha : 0 < a) (hK : 0 < K) :
    ∀ j, 0 < phaseReplacementCoefficient a K D j := by
  intro j
  induction j with
  | zero => simp [phaseReplacementCoefficient]
  | succ j ih =>
    rw [phaseReplacementCoefficient]
    positivity

theorem phaseReplacementRate_zero (a K D δ : ℝ) : phaseReplacementRate a K D δ 0 = δ := by
  simp [phaseReplacementRate,phaseReplacementCoefficient]

theorem phaseReplacementRate_succ {a K D δ : ℝ} (ha : 0 < a) (hK : 0 < K)
    (hδ : 0 < δ) (j : ℕ) :
    phaseReplacementRate a K D δ (j+1) =
      a * ((phaseReplacementRate a K D δ j)^2 / K)^D := by
  let A := phaseReplacementCoefficient a K D j
  let B := (2*D)^j
  have hA := phaseReplacementCoefficient_pos (D:=D) ha hK j
  change a * (A^2/K)^D * δ^((2*D)^(j+1) : ℝ) = a * ((A*δ^B)^2/K)^D
  rw [show (A*δ^B)^2/K = (A^2/K)*(δ^B)^2 by ring,
    Real.mul_rpow (by positivity) (by positivity)]
  rw [← Real.rpow_natCast (δ^B) 2, ← Real.rpow_mul hδ.le, ← Real.rpow_mul hδ.le]
  have he : (2*D)^(j+1) = B * 2 * D := by
    rw [pow_succ]
    dsimp [B]
    ring
  rw [he, mul_assoc]
  norm_num

theorem phaseReplacementRate_pos {a K D δ : ℝ} (ha : 0 < a) (hK : 0 < K)
    (hδ : 0 < δ) (j : ℕ) : 0 < phaseReplacementRate a K D δ j := by
  exact mul_pos (phaseReplacementCoefficient_pos ha hK j) (Real.rpow_pos_of_pos hδ _)

theorem phaseReplacementRate_le_one {a K D δ : ℝ}
    (ha : 0 < a) (ha' : a ≤ 1) (hK : 1 ≤ K) (hD : 1 ≤ D)
    (hδ : 0 < δ) (hδ' : δ ≤ 1) :
    ∀ j, phaseReplacementRate a K D δ j ≤ 1 := by
  intro j
  induction j with
  | zero => simpa [phaseReplacementRate_zero] using hδ'
  | succ j ih =>
    rw [phaseReplacementRate_succ ha (by linarith) hδ]
    have h := phaseReplacementRate_pos (D:=D) ha (by linarith : 0 < K) hδ j
    have hdiv : (phaseReplacementRate a K D δ j)^2 / K ≤ 1 := by
      apply (div_le_one (by linarith : 0 < K)).mpr
      nlinarith only [h,ih,hK, mul_nonneg h.le (sub_nonneg.mpr ih)]
    exact mul_le_one₀ ha' (Real.rpow_nonneg (by positivity) _) (Real.rpow_le_one
      (by positivity) hdiv (by linarith))

theorem phaseReplacementRate_succ_le_dual {a K D δ : ℝ}
    (ha : 0 < a) (ha' : a ≤ 1) (hK : 1 ≤ K) (hD : 1 ≤ D)
    (hδ : 0 < δ) (hδ' : δ ≤ 1) (j : ℕ) :
    phaseReplacementRate a K D δ (j+1) ≤ (phaseReplacementRate a K D δ j)^2/K ∧
    (phaseReplacementRate a K D δ j)^2/K ≤ phaseReplacementRate a K D δ j := by
  let r := phaseReplacementRate a K D δ j
  have hr := phaseReplacementRate_pos (D:=D) ha (by linarith : 0 < K) hδ j
  have hr' := phaseReplacementRate_le_one ha ha' hK hD hδ hδ' j
  have hdual : r^2/K ≤ r := by
    apply (div_le_iff₀ (by linarith : 0 < K)).mpr
    calc
      _ ≤ r*1 := by
        rw [pow_two]
        exact mul_le_mul_of_nonneg_left hr' hr.le
      _ ≤ _ := mul_le_mul_of_nonneg_left hK hr.le
  refine ⟨?_,hdual⟩
  rw [phaseReplacementRate_succ ha (by linarith) hδ]
  change a * (r^2/K)^D ≤ r^2/K
  have hdual' : 0 < r^2/K := by positivity
  have hp := Real.rpow_le_rpow_of_exponent_ge hdual' (hdual.trans hr') hD
  rw [Real.rpow_one] at hp
  exact (mul_le_mul_of_nonneg_right ha' (by positivity)).trans (by simpa only [one_mul] using hp)

theorem phaseReplacementRate_antitone {a K D δ : ℝ}
    (ha : 0 < a) (ha' : a ≤ 1) (hK : 1 ≤ K) (hD : 1 ≤ D)
    (hδ : 0 < δ) (hδ' : δ ≤ 1) :
    Antitone (phaseReplacementRate a K D δ) :=
  antitone_nat_of_succ_le (fun j => (phaseReplacementRate_succ_le_dual ha ha' hK hD hδ hδ' j).1.trans
    (phaseReplacementRate_succ_le_dual ha ha' hK hD hδ hδ' j).2)

end NilBohr
