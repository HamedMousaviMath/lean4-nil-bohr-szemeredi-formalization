import NilBohr.GowersComparison
import NilBohr.GowersDilationRatio
import NilBohr.GowersTriangle
import NilBohr.PolynomialGowers
import NilBohr.LocalizedPrimeModel

/-! The finite affine dilation and residue-class restriction of the
interval Gowers norms used in KMTT Lemma 2.2. -/

open Polynomial
open scoped BigOperators ComplexConjugate

namespace NilBohr

private theorem cubeProduct_affine (steps : List ℤ) (f : ℤ → ℂ) (b q x : ℤ) :
    cubeProduct steps (fun n => f (q*n+b)) x =
      cubeProduct (steps.map (q * ·)) f (q*x+b) := by
  induction steps generalizing x with
  | nil => rfl
  | cons a steps ih =>
    simp only [cubeProduct, List.map_cons, ih, show q*(x+a)+b = (q*x+b)+q*a by ring]

private theorem cubeProduct_nonzero_vertices {f : ℤ → ℂ} {steps : List ℤ} {x : ℤ}
    (h : cubeProduct steps f x ≠ 0) :
    f x ≠ 0 ∧ ∀ a ∈ steps, f (x+a) ≠ 0 := by
  induction steps generalizing x with
  | nil => simpa [cubeProduct] using h
  | cons a steps ih =>
    have h' := mul_ne_zero_iff.mp h
    have htail : cubeProduct steps f (x+a) ≠ 0 := by
      intro hz
      exact h'.2 (by simp [hz])
    have h₀ := ih h'.1
    have h₁ := ih htail
    refine ⟨h₀.1, fun t ht => ?_⟩
    rcases List.mem_cons.mp ht with rfl | ht
    · exact h₁.1
    · exact h₀.2 _ ht

/-- Restrict an integer function to the affine image of the closed interval. -/
noncomputable def affineIntervalRestriction (b q l u : ℤ) (f : ℤ → ℂ) : ℤ → ℂ :=
  fun x => open Classical in if ∃ n ∈ Finset.Icc l u, x = q*n+b then f x else 0

/-- An affine change of variables preserves the unnormalized cube sum
exactly, with the target function set to zero outside the image. -/
theorem gowersCubePower_affine_interval (S : ℕ) (b : ℤ) {q l u L U : ℤ} (hq : 0 < q)
    (hlu : l ≤ u) (hLU : L ≤ U)
    (hImg : ∀ n ∈ Finset.Icc l u, q*n+b ∈ Finset.Icc L U) (f : ℤ → ℂ) :
    gowersCubePower S L U (affineIntervalRestriction b q l u f) =
      gowersCubePower S l u (fun n => f (q*n+b)) := by
  classical
  let W := (u-l).toNat
  let D := (U-L).toNat
  have hW : (W : ℤ) = u-l := Int.toNat_of_nonneg (sub_nonneg.mpr hlu)
  have hD : (D : ℤ) = U-L := Int.toNat_of_nonneg (sub_nonneg.mpr hLU)
  have hWidth : q*(W : ℤ) ≤ (D : ℤ) := by
    have hl := (Finset.mem_Icc.mp (hImg l (Finset.mem_Icc.mpr ⟨le_rfl,hlu⟩))).1
    have hu := (Finset.mem_Icc.mp (hImg u (Finset.mem_Icc.mpr ⟨hlu,le_rfl⟩))).2
    rw [hW,hD,mul_sub]
    linarith
  let embDir (i : Fin (2*W+1)) : Fin (2*D+1) := ⟨
    (q*((i.val : ℤ)-(W : ℤ))+(D : ℤ)).toNat, by
      have hi : (i.val : ℤ) ≤ 2*(W : ℤ) := by exact_mod_cast Nat.lt_succ_iff.mp i.isLt
      have hi0 : (0 : ℤ) ≤ i.val := by positivity
      have hupper : q*((i.val : ℤ)-(W : ℤ)) ≤ D :=
        (mul_le_mul_of_nonneg_left (by omega : (i.val : ℤ)-(W : ℤ) ≤ W) hq.le).trans hWidth
      have hlower : -(D : ℤ) ≤ q*((i.val : ℤ)-(W : ℤ)) := by
        have h := mul_le_mul_of_nonneg_left (show -(W : ℤ) ≤ (i.val : ℤ)-(W : ℤ) by omega) hq.le
        rw [mul_neg] at h
        omega
      omega⟩
  have hEmb (i : Fin (2*W+1)) :
      ((embDir i).val : ℤ) - D = q*((i.val : ℤ)-W) := by
    have hi : (0:ℤ) ≤ i.val := by positivity
    have h := mul_le_mul_of_nonneg_left (show -(W : ℤ) ≤ (i.val : ℤ)-(W : ℤ) by omega) hq.le
    rw [mul_neg] at h
    change (((q*((i.val : ℤ)-(W : ℤ))+(D : ℤ)).toNat : ℕ) : ℤ) - D = _
    rw [Int.toNat_of_nonneg (by omega)]
    ring
  have hFinj : Function.Injective embDir := by
    intro i j hij
    apply Fin.ext
    have h := (hEmb i).symm.trans ((by rw [hij]) : ((embDir i).val : ℤ) - D = _)
    rw [hEmb] at h
    have := mul_left_cancel₀ hq.ne' h
    omega
  let A : Finset (ℤ × (Fin S → Fin (2*W+1))) :=
    Finset.Icc l u ×ˢ Finset.univ
  let B : Finset (ℤ × (Fin S → Fin (2*D+1))) :=
    Finset.Icc L U ×ˢ Finset.univ
  let E : (ℤ × (Fin S → Fin (2*W+1))) → (ℤ × (Fin S → Fin (2*D+1))) :=
    fun p => (q*p.1+b, embDir ∘ p.2)
  have hEinj : Function.Injective E := by
    intro x y h
    apply Prod.ext
    · have h₁ := congrArg Prod.fst h
      exact mul_left_cancel₀ hq.ne' (add_right_cancel h₁)
    · funext j
      apply hFinj
      exact congrFun (congrArg Prod.snd h) j
  have hSub : A.image E ⊆ B := by
    rintro _ hmem
    rcases Finset.mem_image.mp hmem with ⟨x,hx,rfl⟩
    exact Finset.mem_product.mpr ⟨hImg x.1 (Finset.mem_product.mp hx).1, Finset.mem_univ _⟩
  let g := zeroOutside L U (affineIntervalRestriction b q l u f)
  have hSupport {x} (hg : g x ≠ 0) : ∃ n ∈ Finset.Icc l u, x = q*n+b := by
    by_cases hn : ∃ n ∈ Finset.Icc l u, x = q*n+b
    · exact hn
    · exfalso
      exact hg (by simp only [g,zeroOutside,affineIntervalRestriction,if_neg hn,ite_self])
  have hBase (x : ℤ) : g (q*x+b) = zeroOutside l u (fun n => f (q*n+b)) x := by
    by_cases hx : x ∈ Finset.Icc l u
    · have he : ∃ n ∈ Finset.Icc l u, q*x+b = q*n+b := ⟨x,hx,rfl⟩
      simp only [g,zeroOutside,affineIntervalRestriction,if_pos hx,if_pos (hImg x hx),if_pos he]
    · have hn : ¬∃ n ∈ Finset.Icc l u, q*x+b = q*n+b := by
        rintro ⟨n, hn, he⟩
        exact hx ((mul_left_cancel₀ hq.ne' (add_right_cancel he)).symm ▸ hn)
      simp only [g,zeroOutside,affineIntervalRestriction,if_neg hx,if_neg hn,ite_self]
  let prodB (p : ℤ × (Fin S → Fin (2*D+1))) :=
    cubeProduct (gowersDirectionsHere L U S p.2) g p.1
  let prodA (p : ℤ × (Fin S → Fin (2*W+1))) :=
    cubeProduct (gowersDirectionsHere l u S p.2) (zeroOutside l u (fun n => f (q*n+b))) p.1
  have hProd (p) : prodB (E p) = prodA p := by
    have hSteps : gowersDirectionsHere L U S (embDir ∘ p.2) =
        (gowersDirectionsHere l u S p.2).map (q * ·) := by
      unfold gowersDirectionsHere
      rw [List.map_ofFn]
      congr 1
      funext j
      exact hEmb (p.2 j)
    exact (by simpa only [prodA,prodB,E,Prod.fst,Prod.snd,hSteps,hBase] using
      (cubeProduct_affine (gowersDirectionsHere l u S p.2) g b q p.1).symm)
  have hOut (p : ℤ × (Fin S → Fin (2*D+1))) (hp : p ∉ A.image E) : prodB p = 0 := by
    by_cases hp' : prodB p = 0
    · exact hp'
    exfalso
    have hp'' : cubeProduct (gowersDirectionsHere L U S p.2) g p.1 ≠ 0 := hp'
    obtain ⟨h0,hs⟩ := cubeProduct_nonzero_vertices hp'' 
    obtain ⟨x,hx,hx'⟩ := hSupport h0
    have hStep (j : Fin S) :
        ∃ i : Fin (2*W+1), embDir i = p.2 j := by
      have hm : ((((p.2 j).val : ℤ)-(D : ℤ)) : ℤ) ∈ gowersDirectionsHere L U S p.2 := by
        apply List.mem_ofFn.mpr
        exact ⟨j,rfl⟩
      obtain ⟨y,hy,hy'⟩ := hSupport (hs _ hm)
      have hxd := Finset.mem_Icc.mp hx
      have hyd := Finset.mem_Icc.mp hy
      have hDiff : ((p.2 j).val : ℤ)-D = q*(y-x) := by
        rw [mul_sub]
        linarith only [hx',hy']
      have hz : 0 ≤ y-x+(W : ℤ) := by omega
      let i : Fin (2*W+1) := ⟨(y-x+(W : ℤ)).toNat, by omega⟩
      refine ⟨i,Fin.ext ?_⟩
      have hi : (i.val : ℤ) - W = y-x := by
        change (((y-x+(W : ℤ)).toNat : ℕ) : ℤ) - W = _
        rw [Int.toNat_of_nonneg hz]
        ring
      have he := hEmb i
      rw [hi,← hDiff] at he
      omega
    choose k hk using hStep
    apply hp
    refine Finset.mem_image.mpr ⟨(x,k), Finset.mem_product.mpr ⟨hx,Finset.mem_univ _⟩, ?_⟩
    exact Prod.ext hx'.symm (funext hk)
  change (∑ x ∈ Finset.Icc L U, ∑ h, prodB (x,h)) =
    (∑ x ∈ Finset.Icc l u, ∑ h, prodA (x,h))
  rw [← Finset.sum_product, ← Finset.sum_product]
  change (∑ p ∈ B, prodB p) = ∑ p ∈ A, prodA p
  rw [← Finset.sum_subset hSub (fun p _ => hOut p), Finset.sum_image (fun _ _ _ _ h => hEinj h)]
  exact Finset.sum_congr rfl (fun p _ => hProd p)

/-- Translating the interval and the argument of the function preserves the cube sum. -/
theorem gowersCubePower_translate_interval (S : ℕ) (l u b : ℤ) (hlu : l ≤ u) (f : ℤ → ℂ) :
    gowersCubePower S (l+b) (u+b) f = gowersCubePower S l u (fun n => f (n+b)) := by
  classical
  have hImg (n : ℤ) (hn : n ∈ Finset.Icc l u) : 1*n+b ∈ Finset.Icc (l+b) (u+b) := by
    simp [Finset.mem_Icc] at hn ⊢
    exact hn
  have hAff := gowersCubePower_affine_interval S b (by norm_num) hlu (by omega) hImg f
  have hz : zeroOutside (l+b) (u+b) (affineIntervalRestriction b 1 l u f) =
      zeroOutside (l+b) (u+b) f := by
    funext x
    by_cases hx : x ∈ Finset.Icc (l+b) (u+b)
    · obtain ⟨hl,hu⟩ := Finset.mem_Icc.mp hx
      have himg : ∃ n ∈ Finset.Icc l u, x = 1*n+b :=
        ⟨x-b, Finset.mem_Icc.mpr ⟨by omega,by omega⟩, by ring⟩
      simp only [zeroOutside, if_pos hx, affineIntervalRestriction, if_pos himg]
    · simp only [zeroOutside, if_neg hx]
  simpa only [gowersCubePower, hz, one_mul] using hAff

/-- Simultaneously translating the interval and function preserves the normalized norm. -/
theorem normalizedGowers_translate_interval (S : ℕ) (l u b : ℤ) (hlu : l ≤ u) (f : ℤ → ℂ) :
    normalizedGowers S (l+b) (u+b) f = normalizedGowers S l u (fun n => f (n+b)) := by
  unfold normalizedGowers
  rw [gowersCubePower_translate_interval S l u b hlu f,
    gowersCubePower_translate_interval S l u b hlu (fun _ => 1)]

/-- Only the values on the summation interval affect the normalized norm. -/
theorem normalizedGowers_congr_interval (L U : ℤ) (S : ℕ) {f g : ℤ → ℂ}
    (h : ∀ x ∈ Finset.Icc L U, f x = g x) :
    normalizedGowers S L U f = normalizedGowers S L U g := by
  have hzero : zeroOutside L U f = zeroOutside L U g := by
    funext x
    by_cases hx : x ∈ Finset.Icc L U
    · simpa only [zeroOutside, if_pos hx] using h x hx
    · simp only [zeroOutside, if_neg hx]
  simp only [normalizedGowers,gowersCubePower,hzero]

private theorem cubeProduct_zero_directions (s : ℕ) (hs : 1 ≤ s) (f : ℤ → ℂ) (x : ℤ) :
    cubeProduct (List.replicate s 0) f x = ((‖f x‖^(2^s : ℕ) : ℝ) : ℂ) := by
  cases s with
  | zero => omega
  | succ n =>
    induction n with
    | zero => simpa [cubeProduct, Complex.normSq_eq_norm_sq] using Complex.mul_conj (f x)
    | succ n ih =>
      have ih' := ih (by omega)
      rw [List.replicate_succ, cubeProduct, add_zero, ih', Complex.conj_ofReal, ← Complex.ofReal_mul,
        ← pow_add, pow_succ (2 : ℕ) (n+1), Nat.mul_two]

private theorem gowersDirectionsHere_zero (L U : ℤ) (s : ℕ) :
    let D := (U-L).toNat
    gowersDirectionsHere L U s (fun _ => ⟨D, by omega⟩ : Fin s → Fin (2*D+1)) =
      List.replicate s 0 := by
  simp [gowersDirectionsHere, List.ofFn_const]

/-- The single-point contribution is at most the full Gowers cube power.
The all-zero directions in the sum of squares bound its value from below. -/
theorem gowersCubePower_pointwise_lower (L U : ℤ) (S : ℕ) (hS : 2 ≤ S)
    (f : ℤ → ℂ) (b : ℤ) (hb : b ∈ Finset.Icc L U) :
    ‖f b‖^(2^S : ℕ) ≤ (gowersCubePower S L U f).re := by
  obtain ⟨s,rfl⟩ : ∃ s : ℕ, S = s+1 := ⟨S-1, by omega⟩
  have hLU := (Finset.mem_Icc.mp hb).1.trans (Finset.mem_Icc.mp hb).2
  let D := (U-L).toNat
  let hzero : Fin s → Fin (2*D+1) := fun _ => ⟨D, by omega⟩
  rw [gowersCubePower_succ_eq_sum_sq L U hLU s f, Complex.re_sum]
  simp only [Complex.ofReal_re]
  have hsq (x : ℤ) (hx : x ∈ Finset.Icc L U) :
      cubeProduct (gowersDirectionsHere L U s hzero) (zeroOutside L U f) x =
        ((‖f x‖^(2^s : ℕ) : ℝ) : ℂ) := by
    rw [gowersDirectionsHere_zero, cubeProduct_zero_directions s (by omega), zeroOutside, if_pos hx]
  have hTerm : ‖∑ x ∈ Finset.Icc L U,
      cubeProduct (gowersDirectionsHere L U s hzero) (zeroOutside L U f) x‖ =
        ∑ x ∈ Finset.Icc L U, ‖f x‖^(2^s : ℕ) := by
    rw [show (∑ x ∈ Finset.Icc L U,
      cubeProduct (gowersDirectionsHere L U s hzero) (zeroOutside L U f) x) =
        ∑ x ∈ Finset.Icc L U, ((‖f x‖^(2^s : ℕ) : ℝ) : ℂ) from
        Finset.sum_congr rfl hsq, ← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    exact Finset.sum_nonneg (fun _ _ => by positivity)
  calc
    _ = (‖f b‖^(2^s:ℕ))^2 := by rw [← pow_mul, pow_succ (2:ℕ) s]
    _ ≤ ‖∑ x ∈ Finset.Icc L U,
      cubeProduct (gowersDirectionsHere L U s hzero) (zeroOutside L U f) x‖^2 := by
      rw [hTerm]
      apply pow_le_pow_left₀ (by positivity)
      exact Finset.single_le_sum (fun x _ => pow_nonneg (norm_nonneg (f x)) _) hb
    _ ≤ _ := Finset.single_le_sum
      (f := fun h => ‖∑ x ∈ Finset.Icc L U,
        cubeProduct (gowersDirectionsHere L U s h) (zeroOutside L U f) x‖^2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ hzero)

/-- Subtracting the value at a point from a function costs at most its full
ambient Gowers norm for the singleton term. -/
theorem normalizedGowers_singleton_le (L U : ℤ) (S : ℕ) (hS : 2 ≤ S)
    (f : ℤ → ℂ) (b : ℤ) (hb : b ∈ Finset.Icc L U) (z : ℂ) (hz : ‖z‖ ≤ ‖f b‖) :
    normalizedGowers S L U (fun x => if x = b then z else 0) ≤ normalizedGowers S L U f := by
  have hLU := (Finset.mem_Icc.mp hb).1.trans (Finset.mem_Icc.mp hb).2
  have hAff := gowersCubePower_affine_interval S b (q := 1) (l := 0) (u := 0)
    (by norm_num) le_rfl hLU (by
      intro n hn
      have hn' : n = 0 := by simpa using hn
      simpa [hn'] using hb)
    (fun _ => z)
  have hCut : affineIntervalRestriction b 1 0 0 (fun _ => z) =
      fun x => if x = b then z else 0 := by
    funext x
    have hx : (∃ n ∈ Finset.Icc (0:ℤ) 0, x = 1*n+b) ↔ x = b := by simp
    simp only [affineIntervalRestriction,hx]
  rw [hCut] at hAff
  have hConst : gowersCubePower S 0 0 (fun _ => z) = ((‖z‖^(2^S : ℕ) : ℝ) : ℂ) := by
    change (∑ x ∈ Finset.Icc (0:ℤ) 0, ∑ h : Fin S → Fin (2*((0:ℤ)-0).toNat+1),
      cubeProduct (gowersDirectionsHere 0 0 S h) (zeroOutside 0 0 (fun _ => z)) x) = _
    simp only [Finset.Icc_self,Finset.sum_singleton]
    have hOne : Unique (Fin S → Fin (2*((0:ℤ)-0).toNat+1)) := by
      change Unique (Fin S → Fin 1)
      infer_instance
    rw [Finset.univ_unique, Finset.sum_singleton]
    have hd (h : Fin S → Fin (2*((0:ℤ)-0).toNat+1)) :
        gowersDirectionsHere 0 0 S h = List.replicate S 0 := by
      have he : h = fun _ => ⟨((0:ℤ)-0).toNat, by decide⟩ := Subsingleton.elim _ _
      rw [he,gowersDirectionsHere_zero]
    rw [hd, cubeProduct_zero_directions S (by omega)]
    simp [zeroOutside]
  unfold normalizedGowers
  rw [hAff,hConst,Complex.ofReal_re]
  apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg
    (gowersCubePower_re_nonnegative L U S (by omega) _) _)
  exact Real.rpow_le_rpow (by positivity)
    ((pow_le_pow_left₀ (norm_nonneg z) hz _).trans (gowersCubePower_pointwise_lower L U S hS f b hb))
    (by positivity)

private theorem normalizedGowers_sum_le {ι : Type*} (L U : ℤ) (S : ℕ) (hS : 1 ≤ S)
    (hLU : L ≤ U)
    (I : Finset ι) (f : ι → ℤ → ℂ) :
    normalizedGowers S L U (fun x => ∑ i ∈ I, f i x) ≤
      ∑ i ∈ I, normalizedGowers S L U (f i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using (normalizedGowers_real_scale L U S hS 0 le_rfl (fun _ => 0)).le
  | insert i I hi ih =>
    simp only [Finset.sum_insert hi]
    exact (normalizedGowers_triangle L U S hS hLU _ _).trans (add_le_add_left ih _)

/-- Restricting a weight to one residue class contracts the Gowers norm. -/
theorem normalizedGowers_residue_restriction (L U : ℤ) (S : ℕ) (hS : 2 ≤ S)
    (hLU : L ≤ U)
    (q : ℕ) (hq : 0 < q) (b : ℤ) (f : ℤ → ℂ) :
    normalizedGowers S L U (fun x => if (q:ℤ) ∣ x-b then f x else 0) ≤
      normalizedGowers S L U f := by
  classical
  letI : NeZero q := ⟨hq.ne'⟩
  let P (r : ZMod q) := C ((r.val : ℝ)/(q : ℝ)) * (X - C (b:ℝ))
  let F (r : ZMod q) (x : ℤ) := f x * phaseExponential ((P r).eval (x:ℝ))
  have hDeg (r : ZMod q) : (P r).natDegree < S := by
    dsimp [P]
    refine (natDegree_C_mul_le _ _).trans_lt ?_
    exact (natDegree_sub_le _ _).trans_lt (by simp; omega)
  have hFour (x : ℤ) :
      (if (q:ℤ) ∣ x-b then (1:ℂ) else 0) =
        ∑ r : ZMod q, (q : ℂ)⁻¹ * phaseExponential ((P r).eval (x:ℝ)) := by
    simpa [P, Int.modEq_zero_iff_dvd, Int.cast_sub] using
      residue_indicator_fourier q (x-b) 0
  have hFun : (fun x => if (q:ℤ) ∣ x-b then f x else 0) =
      fun x => (((q:ℝ)⁻¹ : ℝ):ℂ) * ∑ r : ZMod q, F r x := by
    funext x
    have hs : (if (q:ℤ) ∣ x-b then f x else 0) =
        (if (q:ℤ) ∣ x-b then (1:ℂ) else 0) * f x := by split_ifs <;> simp
    rw [hs, hFour, Complex.ofReal_inv, Complex.ofReal_natCast, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun r _ => by simp only [F]; ring)
  rw [hFun, normalizedGowers_real_scale L U S (by omega) _ (by positivity)]
  refine (mul_le_mul_of_nonneg_left (normalizedGowers_sum_le L U S (by omega) hLU Finset.univ F)
    (by positivity)).trans ?_
  simp_rw [F, normalizedGowers_mul_polynomial_phase L U S _ (hDeg _)]
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  simp [ZMod.card, nsmul_eq_mul, ← mul_assoc,hqR]

/-- Normalized dilation with an arbitrary integer shift. The extra left endpoint
of the ambient interval contributes a single point. -/
theorem normalizedGowers_dilation (S : ℕ) (hS : 2 ≤ S) :
    ∃ A : ℝ, 0 < A ∧ ∀ (L q : ℕ) (b : ℤ), 0 < q → q ≤ L → ∀ f : ℤ → ℂ,
      normalizedGowers S 1 (L / q : ℕ) (fun n => f ((q : ℤ) * n + b)) ≤
        A * (q : ℝ)^(((S : ℝ) + 1) / (2 : ℝ)^S) *
          normalizedGowers S b ((L : ℤ) + b) f := by
  obtain ⟨A,hA,hRatio⟩ := normalized_gowers_dilation_ratio S
  refine ⟨2*A, by positivity, ?_⟩
  intro L q b hq hqL f
  classical
  let B : ℤ := b
  let U : ℤ := (L : ℤ)+b
  let M : ℕ := L/q
  have hM : 0 < M := Nat.div_pos hqL hq
  have hMZ : 1 ≤ (M : ℤ) := by exact_mod_cast hM
  have hBU : B ≤ U := by dsimp [B,U]; omega
  have hBmem : B ∈ Finset.Icc B U := Finset.mem_Icc.mpr ⟨le_rfl,hBU⟩
  have hqZ : 0 < (q : ℤ) := by exact_mod_cast hq
  have hdiv : (M : ℤ) = (L : ℤ) / (q : ℤ) := by simp [M]
  have hImg (n : ℤ) (hn : n ∈ Finset.Icc 1 (M : ℤ)) :
      (q : ℤ)*n+B ∈ Finset.Icc B U := by
    obtain ⟨hn1,hnM⟩ := Finset.mem_Icc.mp hn
    have hnL : n*(q : ℤ) ≤ (L : ℤ) :=
      (Int.le_ediv_iff_mul_le hqZ).mp (hnM.trans_eq hdiv)
    have hn0 : 0 ≤ n := by omega
    have hqn : 0 ≤ (q : ℤ)*n := mul_nonneg hqZ.le hn0
    exact Finset.mem_Icc.mpr ⟨by linarith only [hqn], by dsimp [B,U]; linarith only [hnL]⟩
  let g (x : ℤ) := if (q : ℤ) ∣ x-B then f x else 0
  let z (x : ℤ) := if x = B then -f B else 0
  let cut := affineIntervalRestriction B (q : ℤ) 1 (M : ℤ) f
  have hCut (x : ℤ) (hx : x ∈ Finset.Icc B U) : cut x = g x + z x := by
    obtain ⟨hxB,hxU⟩ := Finset.mem_Icc.mp hx
    have hset : (∃ n ∈ Finset.Icc (1:ℤ) (M:ℤ), x = (q:ℤ)*n+B) ↔
        (q : ℤ) ∣ x-B ∧ x ≠ B := by
      constructor
      · rintro ⟨n,hn,rfl⟩
        have hn0 : 0 < n := by have := (Finset.mem_Icc.mp hn).1; omega
        have hp := mul_pos hqZ hn0
        exact ⟨⟨n, by ring⟩, by linarith only [hp]⟩
      · rintro ⟨⟨n,hn⟩,hne⟩
        have hn0 : 0 < n := (mul_pos_iff_of_pos_left hqZ).mp (by omega)
        have hnL : n*(q : ℤ) ≤ (L : ℤ) := by dsimp [B,U] at *; linarith only [hn,hxU]
        have hnM := ((Int.le_ediv_iff_mul_le hqZ).mpr hnL).trans_eq hdiv.symm
        exact ⟨n, Finset.mem_Icc.mpr ⟨by omega,hnM⟩, by linarith only [hn]⟩
    change (if ∃ n ∈ Finset.Icc (1:ℤ) (M:ℤ), x = (q:ℤ)*n+B then f x else 0) = g x + z x
    by_cases he : x = B
    · have hNoImg : ¬ ∃ n ∈ Finset.Icc (1:ℤ) (M:ℤ), x = (q:ℤ)*n+B :=
        fun hi => (hset.mp hi).2 he
      simp only [if_neg hNoImg]
      subst x
      simp [g,z]
    · by_cases hdvd : (q : ℤ) ∣ x-B
      · simp only [if_pos (hset.mpr ⟨hdvd,he⟩),g,z,if_pos hdvd,if_neg he,add_zero]
      · have hNoImg : ¬ ∃ n ∈ Finset.Icc (1:ℤ) (M:ℤ), x = (q:ℤ)*n+B :=
          fun hi => hdvd (hset.mp hi).1
        simp only [if_neg hNoImg,g,z,if_neg hdvd,if_neg he,add_zero]
  have hRestrict : normalizedGowers S B U cut ≤ 2 * normalizedGowers S B U f := by
    rw [normalizedGowers_congr_interval B U S hCut]
    calc
      _ ≤ normalizedGowers S B U g + normalizedGowers S B U z :=
        normalizedGowers_triangle B U S (by omega) hBU g z
      _ ≤ normalizedGowers S B U f + normalizedGowers S B U f :=
        add_le_add (normalizedGowers_residue_restriction B U S hS hBU q hq B f)
          (normalizedGowers_singleton_le B U S hS f B hBmem (-f B) (by simp))
      _ = _ := by ring
  have hAff := gowersCubePower_affine_interval S B hqZ hMZ hBU hImg f
  change gowersCubePower S B U cut = _ at hAff
  let e := ((2:ℝ)^S)⁻¹
  let da := (gowersCubePower S B U (fun _ => 1)).re^e
  let ds := (gowersCubePower S 1 (M:ℤ) (fun _ => 1)).re^e
  have hda : 0 < da := by
    apply Real.rpow_pos_of_pos
    exact lt_of_lt_of_le (by positivity) (gowersCubePower_one_lower_interval S B U hBU)
  have hds : 0 < ds := by
    apply Real.rpow_pos_of_pos
    exact lt_of_lt_of_le (by positivity) (gowersCubePower_one_lower S M hM)
  have hNorm : normalizedGowers S 1 (M:ℤ) (fun n => f ((q:ℤ)*n+B)) =
      normalizedGowers S B U cut * (da/ds) := by
    unfold normalizedGowers
    change (gowersCubePower S 1 (M:ℤ) (fun n => f ((q:ℤ)*n+B))).re^e/ds =
      (gowersCubePower S B U cut).re^e/da * (da/ds)
    rw [← hAff]
    field_simp [hda.ne', hds.ne']
  have hScale : da/ds ≤ A * (q:ℝ)^(((S:ℝ)+1)/(2:ℝ)^S) := by
    have ht := gowersCubePower_translate_interval S 0 (L:ℤ) B (by omega) (fun _ => 1)
    simp only [zero_add] at ht
    change (gowersCubePower S B ((L:ℤ)+B) (fun _ => 1)).re^e/ds ≤ _
    rw [ht]
    simpa [ds,e,M] using hRatio L q 0 hq hqL
  change normalizedGowers S 1 (M:ℤ) (fun n => f ((q:ℤ)*n+B)) ≤
    (2*A) * (q:ℝ)^(((S:ℝ)+1)/(2:ℝ)^S) * normalizedGowers S B U f
  rw [hNorm]
  calc
    _ ≤ (2 * normalizedGowers S B U f) *
        (A * (q:ℝ)^(((S:ℝ)+1)/(2:ℝ)^S)) :=
      mul_le_mul hRestrict hScale (by positivity)
        (mul_nonneg (by norm_num) (normalizedGowers_nonnegative B U S (by omega) f))
    _ = _ := by ring

/-- KMTT Lemma 2.2 with its natural-number residue parameter. -/
theorem kmttNormalizedDilation : KMTTNormalizedDilation := by
  intro S hS
  obtain ⟨A,hA,hDil⟩ := normalizedGowers_dilation S hS
  exact ⟨A,hA, fun L q b => hDil L q (b:ℤ)⟩

end NilBohr
