import NilBohr.GowersCubeVolume

namespace NilBohr

private noncomputable def dilationVolumeConstant (S : ℕ) : ℝ :=
  (2:ℝ)^S * (2*((S:ℝ)+1))^(S+1)

private theorem dilationVolumeConstant_pos (S : ℕ) : 0 < dilationVolumeConstant S := by
  unfold dilationVolumeConstant
  positivity

private theorem gowersCubePower_one_le_dilation_factor (S L q b : ℕ)
    (hq : 0 < q) (hqL : q ≤ L) :
    (gowersCubePower S (b:ℤ) ((L:ℤ)+b) (fun _=>1)).re ≤
      dilationVolumeConstant S * (q:ℝ)^(S+1) *
        (gowersCubePower S 1 (L/q:ℕ) (fun _=>1)).re := by
  let N : ℕ := L/q
  have hN : 0 < N := Nat.div_pos hqL hq
  have hfirst : L+1 ≤ (N+1)*q := by
    have h := Nat.lt_div_mul_add (a := L) (b := q) hq
    simpa [N, Nat.add_mul] using Nat.succ_le_of_lt h
  have hsize : L+1 ≤ 2*q*N := by
    calc
      _ ≤ (N+1)*q := hfirst
      _ ≤ (2*N)*q := Nat.mul_le_mul_right q (by omega)
      _ = _ := by ring
  have hsizeR : (L:ℝ)+1 ≤ 2*(q:ℝ)*(N:ℝ) := by exact_mod_cast hsize
  have hbox : (L:ℝ)+1 ≤ 2*((S:ℝ)+1)*(q:ℝ) * ((N:ℝ)/((S:ℝ)+1)) := by
    refine hsizeR.trans_eq ?_
    have hS : (S:ℝ)+1 ≠ 0 := by positivity
    field_simp
    ring
  have hup := gowersCubePower_one_upper_interval S (b:ℤ) ((L:ℤ)+b) (by linarith)
  have hu : (((L:ℤ)+b)-(b:ℤ)).toNat = L := by omega
  rw [hu, Nat.cast_add, Nat.cast_one] at hup
  have hlow := gowersCubePower_one_lower S N hN
  calc
    _ ≤ ((L:ℝ)+1) * (2*((L:ℝ)+1))^S := hup
    _ = (2:ℝ)^S * ((L:ℝ)+1)^(S+1) := by rw [mul_pow, pow_succ]; ring
    _ ≤ (2:ℝ)^S * (2*((S:ℝ)+1)*(q:ℝ) * ((N:ℝ)/((S:ℝ)+1)))^(S+1) := by
      gcongr
    _ = dilationVolumeConstant S * (q:ℝ)^(S+1) * ((N:ℝ)/((S:ℝ)+1))^(S+1) := by
      rw [dilationVolumeConstant]
      simp only [mul_assoc, mul_pow]
    _ ≤ _ := mul_le_mul_of_nonneg_left hlow (mul_nonneg (dilationVolumeConstant_pos S).le (by positivity))

private theorem dilation_indicator_pos (S L q : ℕ) (hq : 0 < q) (hqL : q ≤ L) :
    0 < (gowersCubePower S 1 (L/q:ℕ) (fun _=>1)).re := by
  have hN := Nat.div_pos hqL hq
  exact lt_of_lt_of_le (by positivity) (gowersCubePower_one_lower S (L/q) hN)

/-- The ratio of the two indicator normalizations in the dilation theorem is
bounded by an order-dependent constant times the required power of the step. -/
theorem normalized_gowers_dilation_ratio (S : ℕ) :
    ∃ A : ℝ, 0 < A ∧ ∀ (L q b : ℕ), 0 < q → q ≤ L →
      ((gowersCubePower S (b:ℤ) ((L:ℤ)+b) (fun _=>1)).re)^(((2:ℝ)^S)⁻¹) /
        ((gowersCubePower S 1 (L/q:ℕ) (fun _=>1)).re)^(((2:ℝ)^S)⁻¹) ≤
        A * (q:ℝ)^(((S:ℝ)+1)/(2:ℝ)^S) := by
  let e := ((2:ℝ)^S)⁻¹
  refine ⟨(dilationVolumeConstant S)^e, Real.rpow_pos_of_pos (dilationVolumeConstant_pos S) _, ?_⟩
  intro L q b hq hqL
  let a := (gowersCubePower S (b:ℤ) ((L:ℤ)+b) (fun _=>1)).re
  let c := (gowersCubePower S 1 (L/q:ℕ) (fun _=>1)).re
  have hc : 0 < c := dilation_indicator_pos S L q hq hqL
  have ha : 0 ≤ a := by
    have h := gowersCubePower_one_lower_interval S (b:ℤ) ((L:ℤ)+b) (by linarith)
    exact le_trans (by positivity) h
  have hd : 0 ≤ dilationVolumeConstant S := (dilationVolumeConstant_pos S).le
  have hqR : 0 ≤ (q:ℝ) := Nat.cast_nonneg _
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hC : 0 < c^e := Real.rpow_pos_of_pos hc _
  change a^e/c^e ≤ (dilationVolumeConstant S)^e * (q:ℝ)^(((S:ℝ)+1)/(2:ℝ)^S)
  apply (div_le_iff₀ hC).mpr
  have hraw : a ≤ dilationVolumeConstant S * (q:ℝ)^(S+1) * c :=
    gowersCubePower_one_le_dilation_factor S L q b hq hqL
  calc
    _ ≤ (dilationVolumeConstant S * (q:ℝ)^(S+1) * c)^e :=
      Real.rpow_le_rpow ha hraw he
    _ = _ := by
      rw [Real.mul_rpow (by positivity) hc.le, Real.mul_rpow hd (by positivity),
        ← Real.rpow_natCast_mul hqR]
      simp [e, div_eq_mul_inv]

end NilBohr
