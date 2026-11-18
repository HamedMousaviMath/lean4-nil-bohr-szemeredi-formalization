import NilBohr.GowersCubeVolume

/-! Adjacent orders of the exact interval Gowers norms.
The first comparison is Cauchy–Schwarz on the remaining directions after
writing the next cube power as a sum of squared correlations. -/

namespace NilBohr

/-- Cauchy–Schwarz over the `S` directions in the smaller cube sum. -/
theorem gowersCubePower_re_sq_le_succ (S : ℕ) (L U : ℤ) (hLU : L ≤ U)
    (f : ℤ → ℂ) :
    (gowersCubePower S L U f).re ^ 2 ≤
      ((2 * (U-L).toNat + 1 : ℕ) : ℝ)^S * (gowersCubePower (S+1) L U f).re := by
  let D := 2 * (U-L).toNat + 1
  let F (h : Fin S → Fin D) := ∑ x ∈ Finset.Icc L U,
    cubeProduct (gowersDirectionsHere L U S h) (zeroOutside L U f) x
  have hsmall : gowersCubePower S L U f = ∑ h, F h := by
    change (∑ x ∈ Finset.Icc L U, ∑ h : Fin S → Fin D,
      cubeProduct (gowersDirectionsHere L U S h) (zeroOutside L U f) x) = _
    exact Finset.sum_comm
  rw [hsmall, gowersCubePower_succ_eq_sum_sq L U hLU, Complex.re_sum, Complex.re_sum]
  change (∑ h : Fin S → Fin D, (F h).re)^2 ≤
    (D : ℝ)^S * ∑ h : Fin S → Fin D, ((‖F h‖^2 : ℝ) : ℂ).re
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset (Fin S → Fin D)) (fun _ => (1 : ℝ)) (fun h => (F h).re)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] at hCS
  apply hCS.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro h _
  rw [Complex.ofReal_re, ← sq_abs (F h).re]
  exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm _) _
 
/-- Comparison in the normalization `U^S(I)/U^S(1_I)`.
The cube volume estimates are isolated here to make the dependence of the
constant on the order explicit. -/
theorem normalizedGowers_adjacent_of_cube_volumes
    (hlower : ∀ (S M : ℕ), 0 < M →
      ((M : ℝ) / (S+1))^(S+1) ≤
        (gowersCubePower S 1 (M : ℤ) (fun _ => 1)).re)
    (hupper : ∀ (S M : ℕ), 0 < M →
      (gowersCubePower S 1 (M : ℤ) (fun _ => 1)).re ≤
        (M : ℝ) * (2 * (M : ℝ))^S) :
    NormalizedGowersAdjacentMonotonicity := by
  intro S hS
  let p : ℝ := ((2 : ℝ)^(S+1))⁻¹
  let K : ℝ := (2 : ℝ)^(2*S+1) * ((S : ℝ)+1)^(2*(S+1))
  refine ⟨K^p, Real.rpow_pos_of_pos (by dsimp [K]; positivity) p, ?_⟩
  intro M hM f
  have hMr : 0 < (M : ℝ) := by exact_mod_cast hM
  have hI : (1 : ℤ) ≤ (M : ℤ) := by exact_mod_cast hM
  let A := (gowersCubePower S 1 (M : ℤ) f).re
  let B := (gowersCubePower (S+1) 1 (M : ℤ) f).re
  let C := (gowersCubePower S 1 (M : ℤ) (fun _ => 1)).re
  let D := (gowersCubePower (S+1) 1 (M : ℤ) (fun _ => 1)).re
  let T : ℝ := ((2 * ((M : ℤ)-1).toNat + 1 : ℕ) : ℝ)^S
  have hA : 0 ≤ A := gowersCubePower_re_nonnegative _ _ _ hS f
  have hB : 0 ≤ B := gowersCubePower_re_nonnegative _ _ _ (by omega) f
  have hC : 0 < C := (by positivity : 0 < ((M : ℝ) / (S+1))^(S+1)).trans_le (hlower S M hM)
  have hD : 0 < D :=
    (by positivity : 0 < ((M : ℝ) / (((S+1 : ℕ) : ℝ)+1))^((S+1)+1)).trans_le
      (hlower (S+1) M hM)
  have hT : T ≤ (2*(M:ℝ))^S := by
    apply pow_le_pow_left₀ (by positivity)
    push_cast
    have hcast : ((((M : ℤ)-1).toNat : ℕ) : ℝ) = (M : ℝ)-1 := by
      exact_mod_cast (Int.toNat_of_nonneg (sub_nonneg.mpr hI))
    rw [hcast]
    linarith
  have hCS : A^2 ≤ T * B := gowersCubePower_re_sq_le_succ S _ _ hI f
  have hPower : (M:ℝ)^(2*(S+1)) ≤ C^2 * ((S:ℝ)+1)^(2*(S+1)) := by
    have H := pow_le_pow_left₀ (by positivity : 0 ≤ ((M:ℝ)/((S:ℝ)+1))^(S+1))
      (hlower S M hM) 2
    rw [← pow_mul, div_pow] at H
    have hidx : (S+1)*2 = 2*(S+1) := by omega
    rw [hidx] at H
    rw [div_le_iff₀ (by positivity)] at H
    exact H
  have hTD : T * D ≤ K * C^2 := by
    calc
      T * D ≤ (2*(M:ℝ))^S * ((M:ℝ)*(2*(M:ℝ))^(S+1)) :=
        mul_le_mul hT (hupper (S+1) M hM) hD.le (by positivity)
      _ = (2:ℝ)^(2*S+1) * (M:ℝ)^(2*(S+1)) := by
        rw [mul_left_comm, ← pow_add, mul_pow, mul_left_comm]
        rw [← pow_succ']
        rw [show S + (S + 1) = 2*S+1 by omega,
          show 2*S+1+1 = 2*(S+1) by omega]
      _ ≤ K * C^2 := by
        dsimp [K]
        rw [mul_assoc, mul_comm (((S:ℝ)+1)^_) (C^2)]
        exact mul_le_mul_of_nonneg_left hPower (by positivity)
  have hRatio : A^2/C^2 ≤ K*(B/D) :=
    calc
      A^2/C^2 ≤ (T * B)/C^2 := div_le_div_of_nonneg_right hCS (sq_nonneg _)
      _ = (T * D / C^2) * (B / D) := by field_simp; ring
      _ ≤ K * (B / D) :=
        mul_le_mul_of_nonneg_right ((div_le_iff₀ (sq_pos_of_pos hC)).2 hTD)
          (div_nonneg hB hD.le)
  have hExponent : ((2 : ℝ)^S)⁻¹ = 2*p := by
    dsimp [p]
    rw [pow_succ]
    field_simp
  have hp : 0 ≤ p := by dsimp [p]; positivity
  calc
    normalizedGowers S 1 (M : ℤ) f = (A^2/C^2)^p := by
      change A ^ ((2 : ℝ)^S)⁻¹ / C ^ ((2 : ℝ)^S)⁻¹ = _
      rw [hExponent, Real.div_rpow (sq_nonneg A) (sq_nonneg C),
        ← Real.rpow_natCast_mul hA, ← Real.rpow_natCast_mul hC.le]
      norm_num
    _ ≤ (K*(B/D))^p :=
      Real.rpow_le_rpow (div_nonneg (sq_nonneg _) (sq_nonneg _)) hRatio hp
    _ = K^p * normalizedGowers (S+1) 1 (M : ℤ) f := by
      change (K*(B/D))^p = K^p * (B^p / D^p)
      rw [Real.mul_rpow (by dsimp [K]; positivity) (div_nonneg hB hD.le),
        Real.div_rpow hB hD.le]

/-- The normalized interval norms increase up to a constant depending
only on the order. No Gowers norm inequalities are assumed. -/
theorem normalizedGowersAdjacentMonotonicity : NormalizedGowersAdjacentMonotonicity :=
  normalizedGowers_adjacent_of_cube_volumes gowersCubePower_one_lower gowersCubePower_one_upper

end NilBohr
