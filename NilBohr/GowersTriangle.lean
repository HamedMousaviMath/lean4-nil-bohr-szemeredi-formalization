import NilBohr.GowersComparison

/-!
The finite Gowers–Cauchy–Schwarz and triangle inequalities in the
project's zero-extended interval normalization.
-/

open scoped BigOperators ComplexConjugate

namespace NilBohr

private abbrev CubeVertex (s : ℕ) := Fin s → Bool

private def directionSum {s : ℕ} (v : CubeVertex s) (h : Fin s → ℤ) : ℤ :=
  ∑ j, if v j then h j else 0

private def signedValue {s : ℕ} (v : CubeVertex s) (z : ℂ) : ℂ :=
  if Even (∑ j, (v j).toNat) then z else conj z

private def mixedProduct {s : ℕ} (F : CubeVertex s → ℤ → ℂ)
    (h : Fin s → ℤ) (x : ℤ) : ℂ :=
  ∏ v, signedValue v (F v (x + directionSum v h))

private def face {s : ℕ} (F : CubeVertex (s + 1) → ℤ → ℂ)
    (i : Fin (s + 1)) (b : Bool) : CubeVertex s → ℤ → ℂ :=
  fun v => F (i.insertNth b v)

private theorem vertexDirections_insert {s : ℕ} (i : Fin (s + 1)) (b : Bool)
    (v : CubeVertex s) (t : ℤ) (h : Fin s → ℤ) :
    directionSum (i.insertNth b v) (i.insertNth t h) =
      (if b then t else 0) + directionSum v h := by
  unfold directionSum
  rw [Fin.sum_univ_succAbove _ i]
  simp

private theorem vertexParity_insert {s : ℕ} (i : Fin (s + 1)) (b : Bool)
    (v : CubeVertex s) (z : ℂ) :
    signedValue (i.insertNth b v) z =
      if b then conj (signedValue v z) else signedValue v z := by
  unfold signedValue
  rw [Fin.sum_univ_succAbove _ i]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  cases b
  · simp
  · by_cases h : Even (∑ j, (v j).toNat)
    · simp [Nat.even_add, h]
    · simp [Nat.even_add, h]

private theorem mixedProduct_insert {s : ℕ} (F : CubeVertex (s+1) → ℤ → ℂ)
    (i : Fin (s + 1)) (t : ℤ) (h : Fin s → ℤ) (x : ℤ) :
    mixedProduct F (i.insertNth t h) x =
      mixedProduct (face F i false) h x *
        conj (mixedProduct (face F i true) h (x + t)) := by
  unfold mixedProduct
  let G (v : CubeVertex (s + 1)) := signedValue v
    (F v (x + directionSum v (i.insertNth t h)))
  let e := Fin.insertNthEquiv (fun _ => Bool) i
  rw [← Fintype.prod_equiv e (fun p => G (e p)) G (fun _ => rfl)]
  rw [Fintype.prod_prod_type, Fintype.prod_bool, map_prod, mul_comm]
  simp only [e, G, Fin.insertNthEquiv, Equiv.coe_fn_mk, vertexDirections_insert, vertexParity_insert,
    face, Bool.false_eq_true, Bool.true_eq, ↓reduceIte, zero_add, add_assoc]

private theorem mixedProduct_const {s : ℕ} (h : Fin s → ℤ) (f : ℤ → ℂ) (x : ℤ) :
    mixedProduct (fun _ => f) h x = cubeProduct (List.ofFn h) f x := by
  induction s generalizing x with
  | zero =>
    letI : Unique (CubeVertex 0) :=
      ⟨⟨fun i => Fin.elim0 i⟩, fun g => funext fun i => Fin.elim0 i⟩
    simp [mixedProduct, signedValue, directionSum, cubeProduct, Fintype.prod_unique]
  | succ s ih =>
    rw [← Fin.insertNth_self_removeNth 0 h, mixedProduct_insert, List.ofFn_succ, cubeProduct]
    rw [Fin.insertNth_apply_same]
    congr 1
    · rw [show face (fun _ => f) 0 false = fun _ : CubeVertex s => f by rfl, ih]
      rfl
    · rw [show face (fun _ => f) 0 true = fun _ : CubeVertex s => f by rfl, ih]
      rfl

private abbrev DirectionIndex (L U : ℤ) := Fin (2 * (U-L).toNat + 1)

private def direction (L U : ℤ) (j : DirectionIndex L U) : ℤ :=
  (j.val : ℤ) - ((U-L).toNat : ℤ)

private theorem direction_insert {L U : ℤ} {s : ℕ} (i : Fin (s + 1))
    (j : DirectionIndex L U) (h : Fin s → DirectionIndex L U) :
    (fun v => direction L U (i.insertNth (α := fun _ => DirectionIndex L U) j h v)) =
      i.insertNth (direction L U j) (fun v => direction L U (h v)) := by
  funext v
  cases v using i.succAboveCases <;> simp

private noncomputable def sliceSum (L U : ℤ) {s : ℕ} (F : CubeVertex s → ℤ → ℂ)
    (h : Fin s → DirectionIndex L U) : ℂ :=
  ∑ x ∈ Finset.Icc L U, mixedProduct (fun v => zeroOutside L U (F v)) (direction L U ∘ h) x

/-- The multilinear interval cube sum with one function at each vertex. -/
noncomputable def intervalGowersForm (L U : ℤ) (s : ℕ)
    (F : (Fin s → Bool) → ℤ → ℂ) : ℂ :=
  ∑ h : Fin s → DirectionIndex L U, sliceSum L U F h

theorem intervalGowersForm_diag (L U : ℤ) (s : ℕ) (f : ℤ → ℂ) :
    intervalGowersForm L U s (fun _ => f) = gowersCubePower s L U f := by
  unfold intervalGowersForm sliceSum gowersCubePower
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun h _ =>
    mixedProduct_const (direction L U ∘ h) _ _

private theorem mixedProduct_zero_outside {L U x : ℤ} (hx : x ∉ Finset.Icc L U)
    {s : ℕ} (F : CubeVertex s → ℤ → ℂ) (h : Fin s → ℤ) :
    mixedProduct (fun v => zeroOutside L U (F v)) h x = 0 := by
  unfold mixedProduct
  refine Finset.prod_eq_zero (Finset.mem_univ (fun _ : Fin s => false)) ?_
  simp [signedValue, directionSum, zeroOutside, hx]

private theorem sum_shifted_direction {L U x : ℤ} (hLU : L ≤ U)
    (hx : x ∈ Finset.Icc L U) (F : ℤ → ℂ) (hF : ∀ y, y ∉ Finset.Icc L U → F y = 0) :
    (∑ j : DirectionIndex L U, F (x + direction L U j)) = ∑ y ∈ Finset.Icc L U, F y := by
  let W := (U-L).toNat
  let J := Finset.Icc (x-(W : ℤ)) (x+(W : ℤ))
  have hW : (W : ℤ) = U-L := Int.toNat_of_nonneg (sub_nonneg.mpr hLU)
  have hJ : Finset.Icc L U ⊆ J := by
    intro y hy
    have hy' := Finset.mem_Icc.mp hy
    have hx' := Finset.mem_Icc.mp hx
    apply Finset.mem_Icc.mpr
    omega
  calc
    (∑ j : DirectionIndex L U, F (x + direction L U j)) = ∑ y ∈ J, F y := by
      apply Finset.sum_bij (fun j _ => x + direction L U j)
      · intro j _
        apply Finset.mem_Icc.mpr
        change x - (W : ℤ) ≤ x + ((j.val : ℤ) - (W : ℤ)) ∧
          x + ((j.val : ℤ) - (W : ℤ)) ≤ x + (W : ℤ)
        have h := j.isLt
        omega
      · intro i _ j _ h
        apply Fin.ext
        simp only [direction] at h
        omega
      · intro y hy
        have hy' := Finset.mem_Icc.mp hy
        let j := (y-x+(W : ℤ)).toNat
        have hj : (j : ℤ) = y-x+(W : ℤ) := Int.toNat_of_nonneg (by omega)
        refine ⟨⟨j, by omega⟩, Finset.mem_univ _, ?_⟩
        unfold direction
        change x + ((j : ℤ) - (W : ℤ)) = y
        omega
      · intros
        rfl
    _ = ∑ y ∈ Finset.Icc L U, F y := (Finset.sum_subset hJ (fun y _ hy => hF y hy)).symm

set_option maxHeartbeats 800000 in
private theorem intervalGowersForm_split {L U : ℤ} (hLU : L ≤ U) {s : ℕ}
    (F : CubeVertex (s + 1) → ℤ → ℂ) (i : Fin (s + 1)) :
    intervalGowersForm L U (s+1) F =
      ∑ h : Fin s → DirectionIndex L U,
        sliceSum L U (face F i false) h * conj (sliceSum L U (face F i true) h) := by
  let e := Fin.insertNthEquiv (fun _ : Fin (s + 1) => DirectionIndex L U) i
  unfold intervalGowersForm
  rw [← Fintype.sum_equiv e (fun p => sliceSum L U F (e p)) (sliceSum L U F) (fun _ => rfl)]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun h _ => ?_
  let A := fun x => mixedProduct (fun v => zeroOutside L U (face F i false v)) (direction L U ∘ h) x
  let B := fun x => mixedProduct (fun v => zeroOutside L U (face F i true v)) (direction L U ∘ h) x
  change (∑ j : DirectionIndex L U, sliceSum L U F (i.insertNth j h)) =
    (∑ x ∈ Finset.Icc L U, A x) * conj (∑ y ∈ Finset.Icc L U, B y)
  have ht (j : DirectionIndex L U) : sliceSum L U F (i.insertNth j h) =
      ∑ x ∈ Finset.Icc L U, A x * conj (B (x + direction L U j)) := by
    unfold sliceSum
    refine Finset.sum_congr rfl fun x _ => ?_
    change mixedProduct (fun v => zeroOutside L U (F v))
        (fun v => direction L U (i.insertNth (α := fun _ => DirectionIndex L U) j h v)) x = _
    rw [direction_insert, mixedProduct_insert]
    rfl
  simp_rw [ht]
  rw [Finset.sum_comm]
  have hr (x : ℤ) (hx : x ∈ Finset.Icc L U) :
      (∑ j : DirectionIndex L U, A x * conj (B (x + direction L U j))) =
        ∑ y ∈ Finset.Icc L U, A x * conj (B y) := by
    refine sum_shifted_direction hLU hx (fun y => A x * conj (B y)) fun y hy => ?_
    simp [B, mixedProduct_zero_outside hy]
  rw [Finset.sum_congr rfl hr]
  simp_rw [← Finset.mul_sum, ← map_sum]
  rw [Finset.sum_mul]

private theorem norm_sum_mul_conj_sq_le {ι : Type*} [Fintype ι] (A B : ι → ℂ) :
    ‖∑ h, A h * conj (B h)‖ ^ 2 ≤ (∑ h, ‖A h‖ ^ 2) * ∑ h, ‖B h‖ ^ 2 := by
  have hnorm := norm_sum_le (Finset.univ : Finset ι) (fun h => A h * conj (B h))
  simp only [norm_mul, Complex.norm_conj] at hnorm
  exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq _ (fun h => ‖A h‖) (fun h => ‖B h‖))

private def copyFace {s : ℕ} (F : CubeVertex s → ℤ → ℂ)
    (i : Fin s) (b : Bool) : CubeVertex s → ℤ → ℂ :=
  fun v => F (Function.update v i b)

private theorem intervalGowersForm_copy_norm {L U : ℤ} (hLU : L ≤ U)
    {s : ℕ} (F : CubeVertex (s+1) → ℤ → ℂ) (i : Fin (s+1)) (b : Bool) :
    ‖intervalGowersForm L U (s+1) (copyFace F i b)‖ =
      ∑ h : Fin s → DirectionIndex L U, ‖sliceSum L U (face F i b) h‖ ^ 2 := by
  have hcopy (c : Bool) : face (copyFace F i b) i c = face F i b := by
    funext v
    simp [face, copyFace]
  rw [intervalGowersForm_split hLU _ i, hcopy, hcopy]
  simp_rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_of_nonneg]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

private theorem intervalGowersForm_cs {L U : ℤ} (hLU : L ≤ U)
    {s : ℕ} (F : CubeVertex s → ℤ → ℂ) (i : Fin s) :
    ‖intervalGowersForm L U s F‖ ^ 2 ≤
      ‖intervalGowersForm L U s (copyFace F i false)‖ *
        ‖intervalGowersForm L U s (copyFace F i true)‖ := by
  cases s with
  | zero => exact Fin.elim0 i
  | succ s =>
    rw [intervalGowersForm_split hLU F i, intervalGowersForm_copy_norm hLU,
      intervalGowersForm_copy_norm hLU]
    exact norm_sum_mul_conj_sq_le _ _

private def freeCoordinates {s : ℕ} (J : Finset (Fin s)) (a v : CubeVertex s) :
    CubeVertex s :=
  fun i => if i ∈ J then v i else a i

private def matchingVertices {s : ℕ} (J : Finset (Fin s)) (a : CubeVertex s) :
    Finset (CubeVertex s) :=
  Finset.univ.filter (fun v => ∀ i ∉ J, v i = a i)

private theorem matchingVertices_insert {s : ℕ} {J : Finset (Fin s)} {i : Fin s}
    (hi : i ∉ J) (a : CubeVertex s) (b : Bool) :
    (matchingVertices (insert i J) a).filter (fun v => v i = b) =
      matchingVertices J (Function.update a i b) := by
  ext v
  simp only [matchingVertices, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, not_or]
  constructor
  · rintro ⟨hv, hvi⟩ j hj
    by_cases hji : j = i
    · subst j
      simpa using hvi
    · simpa [Function.update_of_ne hji] using hv j ⟨hji, hj⟩
  · intro hv
    refine ⟨fun j hj => ?_, ?_⟩
    · simpa [Function.update_of_ne hj.1] using hv j hj.2
    · simpa using hv i hi

private theorem copyFace_freeCoordinates {s : ℕ} (F : CubeVertex s → ℤ → ℂ)
    {J : Finset (Fin s)} {i : Fin s} (hi : i ∉ J) (a : CubeVertex s) (b : Bool) :
    copyFace (fun v => F (freeCoordinates (insert i J) a v)) i b =
      fun v => F (freeCoordinates J (Function.update a i b) v) := by
  funext v
  unfold copyFace
  apply congrArg F
  funext j
  by_cases hji : j = i
  · subst j
    simp [freeCoordinates, hi]
  · simp [freeCoordinates, hji, Function.update_of_ne hji]

private theorem intervalGowersForm_iterate_cs {L U : ℤ} (hLU : L ≤ U)
    {s : ℕ} (F : CubeVertex s → ℤ → ℂ) (J : Finset (Fin s)) (a : CubeVertex s) :
    ‖intervalGowersForm L U s (fun v => F (freeCoordinates J a v))‖ ^ (2 ^ J.card) ≤
      ∏ v ∈ matchingVertices J a, ‖intervalGowersForm L U s (fun _ => F v)‖ := by
  classical
  induction J using Finset.induction_on generalizing a with
  | empty =>
    have he : matchingVertices ∅ a = {a} := by
      ext v
      simp [matchingVertices, funext_iff]
    have hf : (fun v => F (freeCoordinates ∅ a v)) = fun _ : CubeVertex s => F a := by
      funext v
      apply congrArg F
      funext j
      simp [freeCoordinates]
    simp only [he, hf, Finset.card_empty, pow_zero, pow_one, Finset.prod_singleton, le_refl]
  | insert i J hi ih =>
    let W (v : CubeVertex s) := ‖intervalGowersForm L U s (fun _ => F v)‖
    let B := intervalGowersForm L U s (fun v => F (freeCoordinates (insert i J) a v))
    change ‖B‖ ^ (2 ^ (insert i J).card) ≤ ∏ v ∈ matchingVertices (insert i J) a, W v
    have hCS := intervalGowersForm_cs hLU (fun v => F (freeCoordinates (insert i J) a v)) i
    simp only [copyFace_freeCoordinates _ hi] at hCS
    have hsplit : (∏ v ∈ matchingVertices (insert i J) a, W v) =
        (∏ v ∈ matchingVertices J (Function.update a i false), W v) *
          ∏ v ∈ matchingVertices J (Function.update a i true), W v := by
      have hS := Finset.prod_filter_mul_prod_filter_not (matchingVertices (insert i J) a)
        (fun v => v i = false) W
      have hnot : (matchingVertices (insert i J) a).filter (fun v => ¬v i = false) =
          (matchingVertices (insert i J) a).filter (fun v => v i = true) := by
        ext v
        cases hv : v i <;> simp [hv]
      rw [hnot, matchingVertices_insert hi, matchingVertices_insert hi] at hS
      exact hS.symm
    rw [hsplit, Finset.card_insert_of_not_mem hi, pow_succ (2 : ℕ), mul_comm (2 ^ J.card), pow_mul]
    refine (pow_le_pow_left₀ (sq_nonneg _) hCS _).trans ?_
    rw [mul_pow]
    exact mul_le_mul (ih (Function.update a i false)) (ih (Function.update a i true))
      (pow_nonneg (norm_nonneg _) _) (Finset.prod_nonneg fun _ _ => norm_nonneg _)

/-- The Gowers–Cauchy–Schwarz inequality for the unscaled interval cube
sum, in a form with only natural powers. -/
theorem intervalGowersForm_norm_pow_le (L U : ℤ) (hLU : L ≤ U)
    (s : ℕ) (F : (Fin s → Bool) → ℤ → ℂ) :
    ‖intervalGowersForm L U s F‖ ^ (2 ^ s) ≤
      ∏ v : Fin s → Bool, ‖gowersCubePower s L U (F v)‖ := by
  have H := intervalGowersForm_iterate_cs hLU F Finset.univ (fun _ => false)
  have hf : (fun v => F (freeCoordinates Finset.univ (fun _ => false) v)) = F := by
    funext v
    apply congrArg F
    funext j
    simp [freeCoordinates]
  have hm : matchingVertices Finset.univ (fun _ : Fin s => false) = Finset.univ := by
    ext v
    simp [matchingVertices]
  rw [hf, hm, Finset.card_univ, Fintype.card_fin] at H
  simpa only [intervalGowersForm_diag] using H

private theorem gowersCubePower_norm_eq_re (L U : ℤ) (hLU : L ≤ U)
    (s : ℕ) (hs : 1 ≤ s) (f : ℤ → ℂ) :
    ‖gowersCubePower s L U f‖ = (gowersCubePower s L U f).re := by
  cases s with
  | zero => omega
  | succ s =>
    rw [gowersCubePower_succ_eq_sum_sq L U hLU, ← Complex.ofReal_sum, Complex.norm_real,
      Complex.ofReal_re, Real.norm_of_nonneg]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _

private noncomputable def unnormalizedGowers (L U : ℤ) (s : ℕ) (f : ℤ → ℂ) : ℝ :=
  (gowersCubePower s L U f).re ^ ((2 : ℝ)^s)⁻¹

private theorem pow_root_eq_self (x : ℝ) (hx : 0 ≤ x) (s : ℕ) :
    (x ^ (2 ^ s : ℕ)) ^ ((2 : ℝ)^s)⁻¹ = x := by
  rw [← Real.rpow_natCast_mul hx, Nat.cast_pow, Nat.cast_ofNat,
    mul_inv_cancel₀ (by positivity : (2:ℝ)^s ≠ 0), Real.rpow_one]

/-- The full multilinear estimate in terms of the unnormalized Gowers
quantities of the separate vertex functions. -/
theorem intervalGowersForm_norm_le (L U : ℤ) (hLU : L ≤ U) (s : ℕ) (hs : 1 ≤ s)
    (F : (Fin s → Bool) → ℤ → ℂ) :
    ‖intervalGowersForm L U s F‖ ≤
      ∏ v : Fin s → Bool, (gowersCubePower s L U (F v)).re ^ ((2 : ℝ)^s)⁻¹ := by
  let W (v : CubeVertex s) := ‖gowersCubePower s L U (F v)‖
  have H := Real.rpow_le_rpow (pow_nonneg (norm_nonneg (intervalGowersForm L U s F)) (2^s))
    (intervalGowersForm_norm_pow_le L U hLU s F)
    (inv_nonneg.mpr (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) s))
  rw [pow_root_eq_self _ (norm_nonneg _) s,
    ← Real.finset_prod_rpow Finset.univ W (fun i _ => norm_nonneg _) _] at H
  simpa only [W, gowersCubePower_norm_eq_re L U hLU s hs] using H

private def chooseByVertex {s : ℕ} (a : CubeVertex s → Bool) (f g : ℤ → ℂ) :
    CubeVertex s → ℤ → ℂ :=
  fun v => if a v then f else g

private theorem mixedProduct_expand_sum (L U : ℤ) {s : ℕ} (f g : ℤ → ℂ)
    (h : Fin s → ℤ) (x : ℤ) :
    mixedProduct (fun _ => zeroOutside L U (fun n => f n + g n)) h x =
      ∑ a : CubeVertex s → Bool,
        mixedProduct (fun v => zeroOutside L U (chooseByVertex a f g v)) h x := by
  classical
  unfold mixedProduct
  let H (v : CubeVertex s) (b : Bool) :=
    signedValue v (zeroOutside L U (if b then f else g) (x + directionSum v h))
  have hf (v : CubeVertex s) : signedValue v
      (zeroOutside L U (fun n => f n + g n) (x + directionSum v h)) =
      ∑ b : Bool, H v b := by
    rw [Fintype.sum_bool]
    simp only [H, Bool.true_eq, ↓reduceIte, Bool.false_eq_true]
    simp only [signedValue, zeroOutside]
    split_ifs <;> simp
  simp_rw [hf]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  rfl

private theorem intervalGowersForm_expand_sum (L U : ℤ) (s : ℕ) (f g : ℤ → ℂ) :
    gowersCubePower s L U (fun n => f n + g n) =
      ∑ a : CubeVertex s → Bool,
        intervalGowersForm L U s (chooseByVertex a f g) := by
  rw [← intervalGowersForm_diag]
  unfold intervalGowersForm sliceSum
  simp_rw [mixedProduct_expand_sum L U f g]
  simp_rw [show ∀ h : Fin s → DirectionIndex L U,
    (∑ x ∈ Finset.Icc L U, ∑ a : CubeVertex s → Bool,
      mixedProduct (fun v => zeroOutside L U (chooseByVertex a f g v)) (direction L U ∘ h) x) =
    (∑ a : CubeVertex s → Bool, ∑ x ∈ Finset.Icc L U,
      mixedProduct (fun v => zeroOutside L U (chooseByVertex a f g v)) (direction L U ∘ h) x)
    from fun _ => Finset.sum_comm]
  rw [Finset.sum_comm]

private theorem unnormalizedGowers_triangle (L U : ℤ) (s : ℕ)
    (hs : 1 ≤ s) (hLU : L ≤ U) (f g : ℤ → ℂ) :
    unnormalizedGowers L U s (fun n => f n + g n) ≤
      unnormalizedGowers L U s f + unnormalizedGowers L U s g := by
  let R := unnormalizedGowers L U s f + unnormalizedGowers L U s g
  have hR : 0 ≤ R :=
    add_nonneg (Real.rpow_nonneg (gowersCubePower_re_nonnegative _ _ _ hs _) _)
      (Real.rpow_nonneg (gowersCubePower_re_nonnegative _ _ _ hs _) _)
  have hBound : ‖gowersCubePower s L U (fun n => f n + g n)‖ ≤ R ^ (2 ^ s : ℕ) := by
    rw [intervalGowersForm_expand_sum]
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ a : CubeVertex s → Bool, ∏ v : CubeVertex s,
          unnormalizedGowers L U s (chooseByVertex a f g v) := by
        apply Finset.sum_le_sum
        intro a _
        exact intervalGowersForm_norm_le L U hLU s hs _
      _ = ∏ _ : CubeVertex s, R := by
        let H (_ : CubeVertex s) (b : Bool) := unnormalizedGowers L U s (if b then f else g)
        change (∑ a : CubeVertex s → Bool, ∏ v : CubeVertex s, H v (a v)) = _
        rw [← Fintype.piFinset_univ, Finset.sum_prod_piFinset]
        congr 1
        funext v
        rw [Fintype.sum_bool]
        rfl
      _ = R ^ (2 ^ s : ℕ) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
          Fintype.card_fin]
  change (gowersCubePower s L U (fun n => f n + g n)).re ^ ((2 : ℝ)^s)⁻¹ ≤ R
  rw [← gowersCubePower_norm_eq_re L U hLU s hs, ← pow_root_eq_self R hR s]
  exact Real.rpow_le_rpow (norm_nonneg _) hBound (by positivity)

/-- The triangle inequality with the exact interval cube normalization. -/
theorem normalizedGowers_triangle (L U : ℤ) (s : ℕ) (hs : 1 ≤ s) (hLU : L ≤ U)
    (f g : ℤ → ℂ) :
    normalizedGowers s L U (fun n => f n + g n) ≤
      normalizedGowers s L U f + normalizedGowers s L U g := by
  unfold normalizedGowers
  rw [← add_div]
  exact div_le_div_of_nonneg_right (unnormalizedGowers_triangle L U s hs hLU f g)
    (Real.rpow_nonneg (gowersCubePower_re_nonnegative _ _ _ hs _) _)

end NilBohr
