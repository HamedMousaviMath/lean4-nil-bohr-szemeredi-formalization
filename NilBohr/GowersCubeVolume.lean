import NilBohr.GowersComparison

open scoped ComplexConjugate BigOperators

namespace NilBohr

private theorem cubeProduct_indicator_zero_or_one (L U x : ℤ) (steps : List ℤ) :
    let p := cubeProduct steps (zeroOutside L U (fun _ => 1)) x
    p = 0 ∨ p = 1 := by
  induction steps generalizing x with
  | nil =>
    simp only [cubeProduct, zeroOutside]
    split_ifs <;> simp
  | cons t ts ih =>
    obtain h | h := ih x
    · simp [cubeProduct, h]
    · obtain h' | h' := ih (x + t) <;> simp [cubeProduct, h, h']

private theorem cubeProduct_indicator_eq_one_of_nonneg_steps (L U x B : ℤ) (steps : List ℤ)
    (hL : L ≤ x) (hU : x + (steps.length : ℤ) * B ≤ U)
    (hB : 0 ≤ B) (hsteps : ∀ t ∈ steps, 0 ≤ t ∧ t ≤ B) :
    cubeProduct steps (zeroOutside L U (fun _ => 1)) x = 1 := by
  induction steps generalizing x with
  | nil =>
    simp only [List.length_nil, Nat.cast_zero, zero_mul, add_zero] at hU
    simp only [cubeProduct, zeroOutside, if_pos (Finset.mem_Icc.mpr ⟨hL, hU⟩)]
  | cons t ts ih =>
    have ht := hsteps t (List.mem_cons_self)
    have hts : ∀ s ∈ ts, 0 ≤ s ∧ s ≤ B := fun s hs =>
      hsteps s (List.mem_cons_of_mem _ hs)
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one, add_mul, one_mul] at hU
    rw [cubeProduct, ih x hL (by linarith) hts, ih (x+t) (by linarith) (by linarith) hts]
    simp

private theorem int_card_Icc_eq_diameter_add_one (L U : ℤ) (hLU : L ≤ U) :
    (Finset.Icc L U).card = (U-L).toNat+1 := by
  rw [Int.card_Icc]
  omega

/-- The indicator cube sum is bounded above by the number of available base
points times the number of choices of bounded directions. -/
theorem gowersCubePower_one_upper_interval (S : ℕ) (L U : ℤ) (hLU : L ≤ U) :
    (gowersCubePower S L U (fun _ => 1)).re ≤
      (((U-L).toNat+1 : ℕ) : ℝ) * (2*(((U-L).toNat+1 : ℕ) : ℝ))^S := by
  classical
  let D := (U-L).toNat
  change (∑ x ∈ Finset.Icc L U, ∑ h : Fin S → Fin (2*D+1),
    (cubeProduct (gowersDirectionsHere L U S h) (zeroOutside L U (fun _ => 1)) x : ℂ)).re ≤ _
  simp_rw [Complex.re_sum]
  calc
    _ ≤ ∑ x ∈ Finset.Icc L U, ∑ _ : Fin S → Fin (2*D+1), (1:ℝ) := by
      refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun h _ => ?_
      obtain hz | ho := cubeProduct_indicator_zero_or_one L U x (gowersDirectionsHere L U S h)
      · simp [hz]
      · simp [ho]
    _ = (((U-L).toNat+1 : ℕ) : ℝ) * ((2*D+1 : ℕ) : ℝ)^S := by
      simp [Fintype.card_fun, int_card_Icc_eq_diameter_add_one L U hLU]
    _ ≤ _ := by
      gcongr
      dsimp [D]
      push_cast
      linarith

/-- A box of side `⌊(U-L)/(S+1)⌋+1` supplies a family of cubes staying in
the interval. This uniformly lower bounds the indicator normalization. -/
theorem gowersCubePower_one_lower_interval (S : ℕ) (L U : ℤ) (hLU : L ≤ U) :
    ((((U-L).toNat + 1 : ℕ) : ℝ) / (S+1))^(S+1) ≤
      (gowersCubePower S L U (fun _ => 1)).re := by
  classical
  let D := (U-L).toNat
  let B := D/(S+1)
  have hD : (D : ℤ) = U-L := Int.toNat_of_nonneg (sub_nonneg.mpr hLU)
  have hBD : B ≤ D := Nat.div_le_self _ _
  have hmul : B * (S+1) ≤ D := Nat.div_mul_le_self _ _
  have hreal : (((U-L).toNat+1 : ℕ) : ℝ)/(S+1) ≤ ((B+1 : ℕ) : ℝ) := by
    apply (div_le_iff₀ (by positivity : (0:ℝ) < (S:ℝ)+1)).mpr
    have h : D < (B+1)*(S+1) := by
      simpa [Nat.add_mul] using Nat.lt_div_mul_add (a := D) (b := S+1) (by omega)
    exact_mod_cast (Nat.succ_le_of_lt h)
  let bx : Fin (B+1) ↪ ℤ :=
    ⟨fun i => L + (i.val : ℤ), by intro i j h; apply Fin.ext; simpa using h⟩
  let bh : (Fin S → Fin (B+1)) ↪ (Fin S → Fin (2*D+1)) :=
    ⟨fun f j => ⟨D+(f j).val, by have := (f j).isLt; omega⟩, by
      intro f g h
      funext j
      apply Fin.ext
      have hj := congrArg (fun t : Fin S → Fin (2*D+1) => (t j).val) h
      simpa using hj⟩
  let X : Finset ℤ := Finset.univ.map bx
  let H : Finset (Fin S → Fin (2*D+1)) := Finset.univ.map bh
  let F (x : ℤ) (h : Fin S → Fin (2*D+1)) : ℝ :=
    (cubeProduct (gowersDirectionsHere L U S h) (zeroOutside L U (fun _ => 1)) x).re
  have hX : X ⊆ Finset.Icc L U := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
    have hi : (i.val : ℤ) ≤ (D:ℤ) := by exact_mod_cast (show i.val ≤ D by omega)
    exact Finset.mem_Icc.mpr ⟨by change L ≤ L + (i.val:ℤ); omega, by
      change L + (i.val:ℤ) ≤ U
      omega⟩
  have hFnonneg (x : ℤ) (h : Fin S → Fin (2*D+1)) : 0 ≤ F x h := by
    obtain hz | ho := cubeProduct_indicator_zero_or_one L U x (gowersDirectionsHere L U S h)
    · simp [F, hz]
    · simp [F, ho]
  have hFone (x : ℤ) (hx : x ∈ X) (h : Fin S → Fin (2*D+1)) (hh : h ∈ H) : F x h = 1 := by
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨f, _, rfl⟩ := Finset.mem_map.mp hh
    have hix : (i.val : ℤ) ≤ B := by exact_mod_cast (show i.val ≤ B by omega)
    have hmulz : (B : ℤ) * ((S:ℤ)+1) ≤ D := by exact_mod_cast hmul
    have hf (j : Fin S) :
        (((bh f j).val : ℤ) - (D : ℤ)) = ((f j).val : ℤ) := by
      change ((D + (f j).val : ℕ) : ℤ) - (D : ℤ) = (f j).val
      push_cast
      omega
    have hcube : cubeProduct (gowersDirectionsHere L U S (bh f))
        (zeroOutside L U (fun _ => 1)) (bx i) = 1 := by
      apply cubeProduct_indicator_eq_one_of_nonneg_steps L U _ (B:ℤ)
      · change L ≤ L + (i.val : ℤ)
        omega
      · simp only [gowersDirectionsHere, List.length_ofFn]
        change L + (i.val : ℤ) + (S : ℤ) * (B : ℤ) ≤ U
        nlinarith only [hix, hmulz, hD]
      · positivity
      · intro t ht
        simp only [gowersDirectionsHere, List.mem_ofFn] at ht
        obtain ⟨j, rfl⟩ := ht
        rw [show ((U-L).toNat : ℤ) = (D : ℤ) by rfl, hf]
        exact ⟨by positivity, by exact_mod_cast (show (f j).val ≤ B from Nat.lt_succ_iff.mp (f j).isLt)⟩
    simp [F, hcube]
  change _ ≤ (∑ x ∈ Finset.Icc L U, ∑ h : Fin S → Fin (2*D+1),
    (cubeProduct (gowersDirectionsHere L U S h) (zeroOutside L U (fun _ => 1)) x : ℂ)).re
  simp_rw [Complex.re_sum]
  change _ ≤ ∑ x ∈ Finset.Icc L U, ∑ h : Fin S → Fin (2*D+1), F x h
  calc
    _ ≤ ((B+1 : ℕ) : ℝ)^(S+1) := by gcongr
    _ = ∑ _ ∈ X, ∑ _ ∈ H, (1 : ℝ) := by
      simp [X, H, Fintype.card_fun, Nat.cast_pow, pow_succ, mul_comm]
    _ = ∑ x ∈ X, ∑ h ∈ H, F x h :=
      Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun h hh => (hFone x hx h hh).symm
    _ ≤ _ := by
      exact (Finset.sum_le_sum fun x _ => Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ H) (fun h _ _ => hFnonneg x h)).trans
        (Finset.sum_le_sum_of_subset_of_nonneg hX (fun x _ _ =>
          Finset.sum_nonneg (fun h _ => hFnonneg x h)))

/-- Upper normalization bound on the manuscript's positive integer interval. -/
theorem gowersCubePower_one_upper (S M : ℕ) (hM : 0 < M) :
    (gowersCubePower S 1 (M:ℤ) (fun _ => 1)).re ≤ (M:ℝ)*(2*(M:ℝ))^S := by
  have hm : (1:ℤ) ≤ (M:ℤ) := by exact_mod_cast hM
  simpa only [show ((M:ℤ)-1).toNat+1 = M by omega] using
    gowersCubePower_one_upper_interval S 1 M hm

/-- Lower normalization bound on the manuscript's positive integer interval. -/
theorem gowersCubePower_one_lower (S M : ℕ) (hM : 0 < M) :
    ((M : ℝ)/(S+1))^(S+1) ≤ (gowersCubePower S 1 (M:ℤ) (fun _ => 1)).re := by
  have hm : (1:ℤ) ≤ (M:ℤ) := by exact_mod_cast hM
  simpa only [show ((M:ℤ)-1).toNat+1 = M by omega] using
    gowersCubePower_one_lower_interval S 1 M hm

end NilBohr
