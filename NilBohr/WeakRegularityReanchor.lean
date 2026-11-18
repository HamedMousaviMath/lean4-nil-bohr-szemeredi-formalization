import NilBohr.External

open Polynomial
open scoped BigOperators

namespace NilBohr

private theorem hasCoefficients_weaken {C C' : ℝ} {q : ℕ} {P : Polynomial ℤ}
    (hP : HasCoefficients C q P) (hCC' : C ≤ C') :
    HasCoefficients C' q P := by
  obtain ⟨hC, hq, hdeg, hzero, hsmall, a, ha, haC, hlead⟩ := hP
  refine ⟨hC.trans hCC', hq, hdeg, hzero, ?_, a, ha, haC.trans hCC', hlead⟩
  intro j hj hj'
  exact (hsmall j hj hj').trans (mul_le_mul_of_nonneg_right hCC' (abs_nonneg _))

private theorem hasCoefficients_neg {C : ℝ} {q : ℕ} {P : Polynomial ℤ}
    (hP : HasCoefficients C q P) : HasCoefficients C q (-P) := by
  obtain ⟨hC, hq, hd, hzero, hs, a, ha, haC, hlead⟩ := hP
  refine ⟨hC, hq, by simpa using hd, by simp [hzero], ?_, -a, ?_, ?_, ?_⟩
  · intro j hj hj'
    simpa using hs j hj (by simpa using hj')
  · simpa using ha
  · simpa using haC
  · simp [hlead]

private theorem abs_coeff_le_classConst_mul_leading {C : ℝ} {q : ℕ} {P : Polynomial ℤ}
    (hP : HasCoefficients C q P) (j : ℕ) (hj : 1 ≤ j) :
    |(P.coeff j : ℝ)| ≤ C * |(P.leadingCoeff : ℝ)| := by
  obtain ⟨hC, _, _, _, hs, _⟩ := hP
  rcases lt_trichotomy j P.natDegree with h | h | h
  · exact hs j hj h
  · rw [h, coeff_natDegree]
    exact le_mul_of_one_le_left (abs_nonneg _) hC
  · rw [coeff_eq_zero_of_natDegree_lt h, Int.cast_zero, abs_zero]
    exact mul_nonneg (zero_le_one.trans hC) (abs_nonneg _)

private theorem leadingAbs_controlled_of_smaller_degree {C : ℝ} {q : ℕ}
    {P Q : Polynomial ℤ} (hP : HasCoefficients C q P)
    (hQ : HasCoefficients C q Q) (hdeg : Q.natDegree < P.natDegree) :
    |(Q.leadingCoeff : ℝ)| ≤ C * |(P.leadingCoeff : ℝ)| := by
  obtain ⟨hC, hq, _, _, _, a, ha, _, hpa⟩ := hP
  obtain ⟨_, _, _, _, _, b, _, hb, hqb⟩ := hQ
  have hqR : 1 ≤ (q:ℝ) := by exact_mod_cast hq
  have hqR0 := zero_le_one.trans hqR
  have haZ : a ≠ 0 := by
    intro he
    simp [he] at ha
  have haOne : 1 ≤ |(a:ℝ)| := by exact_mod_cast Int.one_le_abs haZ
  have hpow : (q:ℝ)^(Q.natDegree-1) ≤ (q:ℝ)^(P.natDegree-1) :=
    pow_le_pow_right₀ hqR (by omega)
  simp only [hpa, hqb, Int.cast_mul, Int.cast_pow, Int.cast_natCast, abs_mul,
    abs_of_nonneg (pow_nonneg hqR0 _)]
  calc
    _ ≤ C * (q:ℝ)^(Q.natDegree-1) := mul_le_mul_of_nonneg_right hb (pow_nonneg hqR0 _)
    _ ≤ C * (q:ℝ)^(P.natDegree-1) := mul_le_mul_of_nonneg_left hpow (zero_le_one.trans hC)
    _ ≤ C * (|(a:ℝ)| * (q:ℝ)^(P.natDegree-1)) := by
      gcongr
      exact le_mul_of_one_le_left (pow_nonneg hqR0 _) haOne

private theorem hasCoefficients_sub_smaller_degree {C : ℝ} {q : ℕ}
    {P Q : Polynomial ℤ} (hP : HasCoefficients C q P)
    (hQ : HasCoefficients C q Q) (hdeg : Q.natDegree < P.natDegree) :
    HasCoefficients (2*C^2+C) q (P-Q) := by
  have habs := leadingAbs_controlled_of_smaller_degree hP hQ hdeg
  have hnd : (P-Q).natDegree = P.natDegree := natDegree_sub_eq_left_of_natDegree_lt hdeg
  have hlead : (P-Q).leadingCoeff = P.leadingCoeff := by
    rw [← coeff_natDegree (p := P-Q), hnd, coeff_sub, coeff_eq_zero_of_natDegree_lt hdeg,
      sub_zero, coeff_natDegree]
  have hsc := abs_coeff_le_classConst_mul_leading hQ
  obtain ⟨hC, hq, hd, hzero, hs, a, ha, haC, hpa⟩ := hP
  have hCC' : C ≤ 2*C^2+C := by linarith [sq_nonneg C]
  refine ⟨hC.trans hCC', hq, by simpa [hnd] using hd, ?_, ?_, a, ha, haC.trans hCC', ?_⟩
  · rw [coeff_sub, hzero, hQ.2.2.2.1, sub_zero]
  · intro j hj hj'
    rw [coeff_sub, Int.cast_sub, hlead]
    rw [hnd] at hj'
    have hC0 : 0 ≤ C := zero_le_one.trans hC
    calc
      _ ≤ |(P.coeff j : ℝ)| + |(Q.coeff j : ℝ)| := abs_sub _ _
      _ ≤ C * |(P.leadingCoeff : ℝ)| + C * |(Q.leadingCoeff : ℝ)| :=
        add_le_add (hs j hj hj') (hsc j hj)
      _ ≤ C * |(P.leadingCoeff : ℝ)| + C * (C * |(P.leadingCoeff : ℝ)|) :=
        add_le_add_left (mul_le_mul_of_nonneg_left habs hC0) _
      _ = (C^2+C) * |(P.leadingCoeff : ℝ)| := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith [sq_nonneg C]) (abs_nonneg _)
  · simp [hnd, hlead, hpa]

/-- Move the spatial base from the unshifted input to the first shifted
input, interchanging their slots. -/
noncomputable def reanchorPolynomialFamily {ℓ : ℕ} (P : Fin (ℓ+1) → Polynomial ℤ) :
    Fin (ℓ+1) → Polynomial ℤ :=
  fun i => P (Equiv.swap 0 1 i) - P 1

private theorem fin_index_one_ne_zero {ℓ : ℕ} (hℓ : 0 < ℓ) :
    (1 : Fin (ℓ+1)) ≠ 0 := by simpa [Fin.one_eq_zero_iff] using hℓ.ne'

private theorem fin_val_one_of_positive {ℓ : ℕ} (hℓ : 0 < ℓ) :
    (1 : Fin (ℓ+1)).val = 1 := by
  cases ℓ with
  | zero => omega
  | succ ℓ => exact Fin.val_one ℓ

private theorem fin_one_lt_of_ne_zero_of_ne_one {ℓ : ℕ} (hℓ : 0 < ℓ)
    {i : Fin (ℓ+1)} (hi0 : i ≠ 0) (hi1 : i ≠ 1) : 1 < i := by
  have h0 : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
  have h1 : i.val ≠ 1 := fun h => hi1 (Fin.ext (h.trans (fin_val_one_of_positive hℓ).symm))
  show (1 : Fin (ℓ+1)).val < i.val
  rw [fin_val_one_of_positive hℓ]
  omega

/-- Reanchoring preserves each degree in the newly ordered family. -/
theorem reanchorPolynomialFamily_degree {ℓ : ℕ} {P : Fin (ℓ+1) → Polynomial ℤ}
    (hP : FixedPolynomialFamily P) (i : Fin (ℓ+1)) :
    (reanchorPolynomialFamily P i).natDegree = (P i).natDegree := by
  by_cases hi0 : i = 0
  · subst i
    simp [reanchorPolynomialFamily, hP.2.1]
  by_cases hi1 : i = 1
  · subst i
    simp [reanchorPolynomialFamily, hP.2.1]
  have hlt := hP.2.2.2 (fin_one_lt_of_ne_zero_of_ne_one hP.1 hi0 hi1)
  simp only [reanchorPolynomialFamily, Equiv.swap_apply_of_ne_of_ne hi0 hi1]
  exact natDegree_sub_eq_left_of_natDegree_lt hlt

theorem reanchorPolynomialFamily_fixed {ℓ : ℕ} {P : Fin (ℓ+1) → Polynomial ℤ}
    (hP : FixedPolynomialFamily P) : FixedPolynomialFamily (reanchorPolynomialFamily P) := by
  refine ⟨hP.1, by simp [reanchorPolynomialFamily], ?_, ?_⟩
  · intro i
    simp [reanchorPolynomialFamily, hP.2.2.1]
  · intro i j hij
    simpa only [reanchorPolynomialFamily_degree hP] using hP.2.2.2 hij

theorem reanchorPolynomialFamily_coefficients {ℓ q : ℕ} {C : ℝ}
    {P : Fin (ℓ+1) → Polynomial ℤ} (hP : FixedPolynomialFamily P)
    (hCoeff : ∀ i, i ≠ 0 → HasCoefficients C q (P i))
    (i : Fin (ℓ+1)) (hi : i ≠ 0) : HasCoefficients (2*C^2+C) q (reanchorPolynomialFamily P i) := by
  have h₁ := hCoeff 1 (fin_index_one_ne_zero hP.1)
  by_cases hi1 : i = 1
  · subst i
    simpa [reanchorPolynomialFamily, hP.2.1] using
      hasCoefficients_weaken (hasCoefficients_neg h₁) (show C ≤ 2*C^2+C by linarith [sq_nonneg C])
  have hlt := hP.2.2.2 (fin_one_lt_of_ne_zero_of_ne_one hP.1 hi hi1)
  simpa only [reanchorPolynomialFamily, Equiv.swap_apply_of_ne_of_ne hi hi1] using
    hasCoefficients_sub_smaller_degree (hCoeff i hi) h₁ hlt

/-- The finite count is exactly preserved by shifting the base and
interchanging the first two slots. Zero extension justifies both boundaries
of the signed spatial shift. -/
theorem countingForm_reanchorPolynomialFamily {ℓ : ℕ} (N M : ℕ) (I : Finset ℤ)
    (P : Fin (ℓ+1) → Polynomial ℤ) (hzero : P 0 = 0) (v : ℤ → ℂ)
    (f : Fin (ℓ+1) → ℤ → ℂ) (hf₀ : SupportedOn I (f 0))
    (hf₁ : SupportedOn I (f 1)) :
    countingForm N M I (reanchorPolynomialFamily P) v
      (fun i => f (Equiv.swap 0 1 i)) = countingForm N M I P v f := by
  classical
  unfold countingForm
  congr 1
  simp only [Finset.sum_comm (s := I) (t := positiveInterval M)]
  apply Finset.sum_congr rfl
  intro y hy
  let p := (P 1).eval y
  let σ : Equiv.Perm (Fin (ℓ+1)) := Equiv.swap 0 1
  let F (z : ℤ) := v y * ∏ i, f (σ i) (z + (reanchorPolynomialFamily P i).eval y)
  let J := I.image (fun x => x+p)
  have hF₀ : ∀ z, z ∉ I → F z = 0 := by
    intro z hz
    have hz' : f (σ 0) (z + (reanchorPolynomialFamily P 0).eval y) = 0 := by
      simpa [σ, reanchorPolynomialFamily] using hf₁ z hz
    unfold F
    rw [Finset.prod_eq_zero
      (f := fun i : Fin (ℓ+1) => f (σ i) (z + (reanchorPolynomialFamily P i).eval y))
      (Finset.mem_univ (0 : Fin (ℓ+1))) hz', mul_zero]
  have hF₁ : ∀ z, z ∉ J → F z = 0 := by
    intro z hz
    have hz' : z-p ∉ I := by
      intro h
      apply hz
      exact Finset.mem_image.mpr ⟨z-p, h, sub_add_cancel z p⟩
    have hw : f (σ 1) (z + (reanchorPolynomialFamily P 1).eval y) = 0 := by
      simpa [σ, reanchorPolynomialFamily, hzero, p, sub_eq_add_neg] using hf₀ (z-p) hz'
    unfold F
    rw [Finset.prod_eq_zero
      (f := fun i : Fin (ℓ+1) => f (σ i) (z + (reanchorPolynomialFamily P i).eval y))
      (Finset.mem_univ (1 : Fin (ℓ+1))) hw, mul_zero]
  have hsum : (∑ z ∈ I, F z) = ∑ z ∈ J, F z :=
    (Finset.sum_subset Finset.subset_union_left (fun z _ hz => hF₀ z hz)).trans
      (Finset.sum_subset Finset.subset_union_right (fun z _ hz => hF₁ z hz)).symm
  change (∑ z ∈ I, F z) = _
  rw [hsum, Finset.sum_image (fun x _ z _ h => add_right_cancel h)]
  apply Finset.sum_congr rfl
  intro x hx
  unfold F
  congr 1
  calc
    _ = ∏ i, f (σ i) (x + (P (σ i)).eval y) := by
      apply Finset.prod_congr rfl
      intro i hi
      congr 1
      simp only [reanchorPolynomialFamily, eval_sub]
      change x+p + ((P (σ i)).eval y - (P 1).eval y) = x + (P (σ i)).eval y
      dsimp [p]
      ring
    _ = _ := Equiv.prod_comp σ (fun i => f i (x + (P i).eval y))

/-- Apply the inverse theorem to a prescribed input, reanchoring the count
when that input is the original spatial base. Its resolution degree is then
the first shifted degree. -/
theorem exists_localInverse_fixed_coordinate {C : ℝ} {d ℓ b₀ : ℕ} {a A b B : ℝ}
    (hInv : KMTTLocalInverseEstimate (2*C^2+C) d ℓ b₀ a A b B) (_hC : 1 ≤ C)
    {N M q : ℕ} (hN : 0 < N) (hq : 0 < q) (hM : 0 < M)
    (hMmax : M ≤ parameterLength N q d)
    (P : Fin (ℓ+1) → Polynomial ℤ) (hP : FixedPolynomialFamily P)
    (hDeg : (P (Fin.last ℓ)).natDegree = d)
    (hCoeff : ∀ i, i ≠ 0 → HasCoefficients C q (P i))
    (f : Fin (ℓ+1) → ℤ → ℂ)
    (hf : ∀ i, OneBoundedOn (positiveInterval N) (f i))
    (hs : ∀ i, SupportedOn (positiveInterval N) (f i))
    (i : Fin (ℓ+1)) (ρ : ℝ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (hlarge : ρ ≤ ‖countingForm N M (positiveInterval N) P (fun _ => 1) f‖) :
    (M:ℝ) ≤ A * ((q:ℝ)/ρ)^B ∨
      ∃ q' b' : ℕ, 0<q' ∧ 1≤b' ∧ b'≤b₀ ∧ (q':ℝ)≤A*ρ^(-B) ∧
        ∃ φ : ℤ → ℂ, (∀ x, ‖φ x‖≤1) ∧
          a*ρ^b*N ≤ ‖∑ x ∈ positiveInterval N, f i x*φ x‖ ∧
          ∀ x t : ℤ, ‖φ (x+(q':ℤ)*(q:ℤ)^b'*t)-φ x‖ ≤
            A*((q:ℝ)/ρ)^B*(M:ℝ)^(-((if i=0 then (P 1).natDegree else (P i).natDegree):ℝ))*|(t:ℝ)| := by
  by_cases hi : i = 0
  · subst i
    let σ : Equiv.Perm (Fin (ℓ+1)) := Equiv.swap 0 1
    let g := fun j => f (σ j)
    let Q := reanchorPolynomialFamily P
    have hcount : countingForm N M (positiveInterval N) Q (fun _ => 1) g =
        countingForm N M (positiveInterval N) P (fun _ => 1) f :=
      countingForm_reanchorPolynomialFamily N M _ P hP.2.1 _ f (hs 0) (hs 1)
    obtain hsmall | ⟨q',b',hq',hb',hbmax,hqb,hwit⟩ :=
      hInv N M q hN hq hM hMmax Q (reanchorPolynomialFamily_fixed hP)
        (by simpa only [Q, reanchorPolynomialFamily_degree hP] using hDeg)
        (reanchorPolynomialFamily_coefficients hP hCoeff)
        g (fun j => hf (σ j)) (fun j => hs (σ j))
        ρ hρ hρhalf (by simpa only [hcount] using hlarge)
    · exact Or.inl hsmall
    · refine Or.inr ⟨q',b',hq',hb',hbmax,hqb,?_⟩
      simpa [g, σ, Q, reanchorPolynomialFamily_degree hP] using
        hwit 1 (fin_index_one_ne_zero hP.1)
  · have hc : ∀ j, j ≠ 0 → HasCoefficients (2*C^2+C) q (P j) := fun j hj =>
      hasCoefficients_weaken (hCoeff j hj) (by linarith [sq_nonneg C])
    obtain hsmall | ⟨q',b',hq',hb',hbmax,hqb,hwit⟩ :=
      hInv N M q hN hq hM hMmax P hP hDeg hc f hf hs ρ hρ hρhalf hlarge
    · exact Or.inl hsmall
    · exact Or.inr ⟨q',b',hq',hb',hbmax,hqb,by simpa [hi] using hwit i hi⟩

end NilBohr
