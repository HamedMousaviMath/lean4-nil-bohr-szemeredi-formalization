import NilBohr.Bohr

/-! The bracket-phase recurrence reduction in Corollary 1.3. -/

open Polynomial

namespace NilBohr

/-- At a prescribed degree, keep the existing polynomial if there is one,
and fill a missing positive degree with the corresponding monomial. -/
private noncomputable def polynomialAtDegree {ℓ : ℕ} (P : Fin (ℓ + 1) → Polynomial ℤ)
    (j : ℕ) : Polynomial ℤ := by
  classical
  exact if h : ∃ i, (P i).natDegree = j then P (Classical.choose h) else X ^ j

private theorem natDegree_polynomialAtDegree {ℓ : ℕ} (P : Fin (ℓ + 1) → Polynomial ℤ)
    (j : ℕ) : (polynomialAtDegree P j).natDegree = j := by
  classical
  unfold polynomialAtDegree
  split_ifs with h
  · exact Classical.choose_spec h
  · exact natDegree_X_pow (R := ℤ) j

private theorem polynomialAtDegree_original {ℓ : ℕ} {P : Fin (ℓ + 1) → Polynomial ℤ}
    (hP : FixedPolynomialFamily P) (i : Fin (ℓ + 1)) :
    polynomialAtDegree P (P i).natDegree = P i := by
  classical
  unfold polynomialAtDegree
  split_ifs with h
  · exact congrArg P (hP.2.2.2.injective (Classical.choose_spec h))
  · exact (h ⟨i, rfl⟩).elim

private theorem fixedPolynomialFamily_polynomialAtDegree {ℓ d : ℕ}
    {P : Fin (ℓ + 1) → Polynomial ℤ} (hP : FixedPolynomialFamily P) (hd : 0 < d) :
    FixedPolynomialFamily (fun i : Fin (d + 1) => polynomialAtDegree P (i : ℕ)) := by
  have hzero : polynomialAtDegree P 0 = 0 := by
    simpa [hP.2.1] using polynomialAtDegree_original hP 0
  refine ⟨hd, hzero, ?_, ?_⟩
  · intro i
    by_cases hi : (i : ℕ) = 0
    · simp [hi, hzero]
    · classical
      change (polynomialAtDegree P (i : ℕ)).coeff 0 = 0
      unfold polynomialAtDegree
      split_ifs with h
      · exact hP.2.2.1 _
      · rw [coeff_X_pow]
        simp [hi, eq_comm]
  · intro i j hij
    simpa only [natDegree_polynomialAtDegree] using hij

private theorem coeff_natDegree_nonzero_of_degree {R : Polynomial ℤ} {d : ℕ}
    (hR : R.natDegree = d) (hd : 0 < d) : R.coeff d ≠ 0 := by
  rw [← hR, coeff_natDegree, leadingCoeff_ne_zero]
  intro hzero
  simp [hzero] at hR
  omega

private theorem eval_linear {R : Polynomial ℤ} (hR : R.natDegree = 1)
    (hzero : R.coeff 0 = 0) (n : ℤ) : R.eval n = R.coeff 1 * n := by
  have h := congrArg (eval n) (as_sum_range_C_mul_X_pow R)
  simpa [hR, Finset.sum_range_succ, hzero] using h

private theorem eval_quadratic {R : Polynomial ℤ} (hR : R.natDegree = 2)
    (hzero : R.coeff 0 = 0) (n : ℤ) : R.eval n = R.coeff 2 * n ^ 2 + R.coeff 1 * n := by
  have h := congrArg (eval n) (as_sum_range_C_mul_X_pow R)
  simpa [hR, Finset.sum_range_succ, hzero, add_comm] using h

/-- Reflect the central half of an arc across zero. -/
private noncomputable def reflectedCentralArc (J : OpenArc) : OpenArc where
  start := -J.start - 3 * J.length / 4
  length := J.length / 2
  length_pos := by linarith [J.length_pos]
  length_lt_one := by linarith [J.length_lt_one]

private theorem contains_of_reflectedCentralArc {J : OpenArc} {z w : ℝ}
    (hz : (reflectedCentralArc J).Contains z) (hclose : torusNorm (w + z) < J.length / 4) :
    J.Contains w := by
  obtain ⟨z₀, hz₀, hcoe⟩ := hz
  have hz₁ : -J.start - 3 * J.length / 4 < z₀ := hz₀.1
  have hz₂ : z₀ < -J.start - 3 * J.length / 4 + J.length / 2 := hz₀.2
  let m : ℤ := round (w + z)
  have habs : |w + z - (m : ℝ)| < J.length / 4 := by
    simpa only [torusNorm_eq, m] using hclose
  obtain ⟨hlower, hupper⟩ := abs_lt.1 habs
  refine ⟨-z₀ + (w + z - (m : ℝ)), ⟨?_, ?_⟩, ?_⟩
  · linarith
  · linarith
  · have hm : ((m : ℝ) : Circle) = 0 :=
      (AddCircle.coe_eq_zero_iff (1 : ℝ)).2 ⟨m, by simp⟩
    simp only [AddCircle.coe_add, AddCircle.coe_neg, AddCircle.coe_sub, hcoe, hm]
    abel

/-- Corollary 1.3 follows from Theorem 1.2. Inserting monomials at any
missing degree up to the enlarged maximum makes the ordering by degree
explicit. It does not change the configuration retained at the end. -/
theorem bracket_recurrence_of_heisenberg_recurrence (hrec : HeisenbergRecurrence) :
    BracketRecurrence := by
  classical
  intro ℓ P hP α β hα hβ J
  let d := max 2 (P (Fin.last ℓ)).natDegree
  have hd : 2 ≤ d := le_max_left _ _
  let Q (i : Fin (d + 1)) := polynomialAtDegree P (i : ℕ)
  have hQ : FixedPolynomialFamily Q :=
    fixedPolynomialFamily_polynomialAtDegree hP (by omega)
  let i₁ : Fin (d + 1) := ⟨1, by omega⟩
  let i₂ : Fin (d + 1) := ⟨2, by omega⟩
  have hQ₁ : (Q i₁).natDegree = 1 := natDegree_polynomialAtDegree P 1
  have hQ₂ : (Q i₂).natDegree = 2 := natDegree_polynomialAtDegree P 2
  let a := (Q i₁).coeff 1
  let b := (Q i₂).coeff 2
  let c := (Q i₂).coeff 1
  have ha : a ≠ 0 := coeff_natDegree_nonzero_of_degree hQ₁ (by omega)
  have hb : b ≠ 0 := coeff_natDegree_nonzero_of_degree hQ₂ (by omega)
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb
  let θ := α * β / 2
  let ε := min (β / 2) (min ((1 - β) / 2) (J.length / (8 * (3 + |α|))))
  have hcα : 0 < 3 + |α| := by positivity
  have hε : 0 < ε := by
    dsimp [ε]
    exact lt_min (by linarith [hβ.1]) (lt_min (by linarith [hβ.2.1])
      (div_pos J.length_pos (mul_pos (by norm_num) hcα)))
  have hεβ : ε < β := (min_le_left _ _).trans_lt (by linarith [hβ.1])
  have hεβ' : ε < 1 - β :=
    ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by linarith [hβ.2.1])
  have hεarc : (3 + |α|) * ε < J.length / 4 := by
    have hle : ε ≤ J.length / (8 * (3 + |α|)) :=
      (min_le_right _ _).trans (min_le_right _ _)
    have hmul := (le_div_iff₀ (mul_pos (by norm_num) hcα)).1 hle
    nlinarith only [hmul, J.length_pos]
  obtain ⟨L, hL, hwidth⟩ := exists_circle_bin_width hε
  let ω : Fin 4 → ℝ := ![α / (a : ℝ), β / (a : ℝ),
    θ * (1 - (c : ℝ) / b) / a, θ / b]
  let color (u : ℤ) (j : Fin 4) := circleBin L hL (ω j * (u : ℝ))
  have hpair {u v : ℤ} (hcol : color u = color v) (j : Fin 4) :
      torusNorm (ω j * ((u : ℝ) - (v : ℝ))) < ε := by
    have h := (norm_circle_sub_lt_of_circleBin_eq hL (congrFun hcol j)).trans hwidth
    change torusNorm (ω j * (u : ℝ) - ω j * (v : ℝ)) < ε at h
    rwa [← mul_sub] at h
  obtain ⟨κ, hκ, N₀, hcells⟩ :=
    recurrence_in_color_cell (hrec Q hQ α β hα hβ (reflectedCentralArc J)) color
  refine ⟨κ, hκ, N₀, ?_⟩
  intro N hN A hA hdense
  obtain ⟨B, x, p, hp, hphase, hpoints, hdistinct⟩ := hcells N hN A hA hdense
  let n : ℤ := (p : ℤ) - 1
  have hx : color x = B := by
    simpa [hQ.2.1] using (Finset.mem_filter.1 (hpoints 0)).2
  have hx₁ : color (x + a * n) = B := by
    simpa only [n, eval_linear hQ₁ (hQ.2.2.1 i₁)] using
      (Finset.mem_filter.1 (hpoints i₁)).2
  have hx₂ : color (x + (b * n ^ 2 + c * n)) = B := by
    simpa only [n, eval_quadratic hQ₂ (hQ.2.2.1 i₂)] using
      (Finset.mem_filter.1 (hpoints i₂)).2
  have hlin (j : Fin 4) : torusNorm (ω j * ((a : ℝ) * (n : ℝ))) < ε := by
    have H := hpair (hx₁.trans hx.symm) j
    push_cast at H
    rw [add_sub_cancel_left] at H
    exact H
  have hsmallα : torusNorm (α * (n : ℝ)) < ε := by
    have H := hlin 0
    change torusNorm (α / (a : ℝ) * ((a : ℝ) * (n : ℝ))) < ε at H
    simpa only [← mul_assoc, div_mul_cancel₀ _ ha'] using H
  have hsmallβ : torusNorm (β * (n : ℝ)) < ε := by
    have H := hlin 1
    change torusNorm (β / (a : ℝ) * ((a : ℝ) * (n : ℝ))) < ε at H
    simpa only [← mul_assoc, div_mul_cancel₀ _ ha'] using H
  have hsmall₁ : torusNorm (θ * (1 - (c : ℝ) / b) * (n : ℝ)) < ε := by
    have H := hlin 2
    change torusNorm (θ * (1 - (c : ℝ) / b) / (a : ℝ) * ((a : ℝ) * (n : ℝ))) < ε at H
    rw [← mul_assoc, div_mul_cancel₀ _ ha'] at H
    exact H
  have hsmall₂ : torusNorm (θ * ((n : ℝ)^2 + (c : ℝ) / b * (n : ℝ))) < ε := by
    have H := hpair (hx₂.trans hx.symm) 3
    change torusNorm (θ / (b : ℝ) * (((x + (b * n ^ 2 + c * n) : ℤ) : ℝ) - (x : ℝ))) < ε at H
    push_cast at H
    rw [add_sub_cancel_left] at H
    have heq : θ / (b : ℝ) * ((b : ℝ) * (n : ℝ)^2 + (c : ℝ) * (n : ℝ)) =
        θ * ((n : ℝ)^2 + (c : ℝ) / b * (n : ℝ)) := by
      calc
        _ = (θ / (b : ℝ) * (b : ℝ)) * (n : ℝ)^2 +
            θ * ((c : ℝ) / b * (n : ℝ)) := by ring
        _ = _ := by rw [div_mul_cancel₀ _ hb', mul_add]
    rwa [heq] at H
  have hsmallθ : torusNorm (θ * ((n : ℝ)^2 + (n : ℝ))) < 2 * ε := by
    have heq : θ * ((n : ℝ)^2 + (n : ℝ)) =
        θ * (1 - (c : ℝ) / b) * (n : ℝ) +
        θ * ((n : ℝ)^2 + (c : ℝ) / b * (n : ℝ)) := by ring
    rw [heq]
    apply (torusNorm_add_le _ _).trans_lt
    linarith
  have hbr : J.Contains (bracketPhase α β n) :=
    contains_of_reflectedCentralArc hphase
      (lt_trans (bracketPhase_near_neg_heisenbergPhase α β ε n hεβ hεβ' hsmallα hsmallβ
        hsmallθ) hεarc)
  let ix (j : Fin (ℓ + 1)) : Fin (d + 1) :=
    ⟨(P j).natDegree, Nat.lt_succ_of_le
      ((hP.2.2.2.monotone (Fin.le_last j)).trans (le_max_right _ _))⟩
  have hix (j : Fin (ℓ + 1)) : Q (ix j) = P j := polynomialAtDegree_original hP j
  refine ⟨x, p, hp, hbr, ?_, ?_⟩
  · intro j
    simpa only [hix j] using (Finset.mem_filter.1 (hpoints (ix j))).1
  · intro i j hij
    apply hP.2.2.2.injective
    have h := hdistinct (show x + (Q (ix i)).eval n = x + (Q (ix j)).eval n by
      simpa only [hix, n] using hij)
    exact congrArg Fin.val h

end NilBohr
