import NilBohr.Arithmetic
import NilBohr.Bohr
import NilBohr.IntroFastDensity

/-! Finite part of the fast-approximation obstruction in the introduction.
This isolated module does not assert existence of the approximating sequence
or its eventual density comparison. -/

open scoped BigOperators

namespace NilBohr

noncomputable def introObstructionArc : OpenArc :=
  ⟨1/4, 1/4, by norm_num, by norm_num⟩

/-- The manuscript's choice of `N` keeps the accumulated approximation
error below one throughout the full parameter range. -/
theorem fastApproximationScale_error {β : ℝ} {a r j : ℕ}
    (hlo : 0 ≤ β-(a : ℝ)/r) (hhi : β-(a : ℝ)/r < Real.exp (-((r : ℝ)^j))) :
    (β-(a : ℝ)/r)*(fastApproximationScale r j : ℝ) < 1 := by
  let T := (r : ℝ)^j
  have hT : 0 ≤ T := by dsimp [T]; positivity
  calc
    _ ≤ (β-(a : ℝ)/r)*Real.exp (T/6) := by
      apply mul_le_mul_of_nonneg_left _ hlo
      exact Nat.floor_le (Real.exp_pos _).le
    _ < Real.exp (-T)*Real.exp (T/6) := mul_lt_mul_of_pos_right hhi (Real.exp_pos _)
    _ ≤ 1 := by
      rw [← Real.exp_add, ← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      linarith

/-- At a multiple of the approximating denominator the floor is exact.
The coefficients of the resulting polynomial retain the actual real
parameter beta. -/
theorem fastApproximation_floor {β : ℝ} {a r N n : ℕ}
    (hr : 0 < r) (hn : n ≤ N) (hdiv : r ∣ n)
    (hlo : 0 ≤ β-(a : ℝ)/r) (hsmall : (β-(a : ℝ)/r)*(N : ℝ) < 1) :
    ⌊β*(n : ℝ)⌋ = ((a*(n/r) : ℕ) : ℤ) := by
  obtain ⟨k,hk⟩ := hdiv
  have hq : n/r = k := by
    rw [hk,Nat.mul_comm]
    exact Nat.mul_div_cancel _ hr
  have hdiv' : (a : ℤ)*(n : ℤ) = (r : ℤ)*((a*k : ℕ):ℤ) := by
    rw [show (n : ℤ) = ((r*k : ℕ):ℤ) by exact_mod_cast hk]
    push_cast
    ring
  have hn' : (n : ℝ) ≤ N := by exact_mod_cast hn
  rw [hq]
  apply floor_mul_eq_int_of_small_error β (a : ℤ) (r : ℤ) (n : ℤ)
    ((a*k : ℕ):ℤ) (by exact_mod_cast hr.ne') hdiv'
  · simpa only [Int.cast_natCast] using mul_nonneg hlo (Nat.cast_nonneg n)
  · simpa only [Int.cast_natCast] using
      (mul_le_mul_of_nonneg_left hn' hlo).trans_lt hsmall

theorem fastApproximation_heisenbergPhase {α β : ℝ} {a r N n : ℕ}
    (hr : 0 < r) (hn : n ≤ N) (hdiv : r ∣ n)
    (hlo : 0 ≤ β-(a : ℝ)/r) (hsmall : (β-(a : ℝ)/r)*(N : ℝ) < 1) :
    heisenbergPhase α β (n : ℤ) =
      (-α*β/2)*(n : ℝ) + (α*β/2-α*((a : ℝ)/r))*(n : ℝ)^2 := by
  have hnr : (n : ℝ) ≤ N := by exact_mod_cast hn
  have hlo' : 0 ≤ (β-(a : ℝ)/r)*(n : ℝ) := mul_nonneg hlo (Nat.cast_nonneg n)
  have hhi' := (mul_le_mul_of_nonneg_left hnr hlo).trans_lt hsmall
  rw [heisenbergPhase_rational_residue α β (a : ℤ) (r : ℤ) (n : ℤ)
    (by exact_mod_cast hr.ne') (by exact_mod_cast hdiv)
    (by simpa only [Int.cast_natCast] using hlo') (by simpa only [Int.cast_natCast] using hhi')]
  push_cast
  ring

/-- A largest cell of a finite coloring has at least the average
cardinality, expressed without rounding a natural quotient. -/
theorem exists_large_color_cell {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (D : Finset ℤ) (color : ℤ → ι) :
    ∃ b : ι, (D.card : ℝ) ≤ Fintype.card ι * (((D.filter (fun x => color x=b)).card : ℕ):ℝ) := by
  classical
  let S (b : ι) := D.filter (fun x => color x=b)
  obtain ⟨b,_,hb⟩ := Finset.exists_max_image (Finset.univ : Finset ι) (fun b => (S b).card)
    Finset.univ_nonempty
  refine ⟨b, ?_⟩
  have heq : D.card = ∑ b : ι, (S b).card :=
    Finset.card_eq_sum_card_fiberwise (t := Finset.univ) (f := color)
      (fun _ _ => Finset.mem_univ _)
  have h := (Finset.sum_le_sum (s := (Finset.univ : Finset ι))
    (f := fun b => (S b).card) (g := fun _ => (S b).card) hb)
  rw [← heq,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at h
  exact_mod_cast h

private theorem quarter_lt_norm_of_introObstructionArc {z : ℝ}
    (hz : introObstructionArc.Contains z) : 1/4 < torusNorm z := by
  obtain ⟨v,hv,heq⟩ := hz
  have hv₁ : (1/4 : ℝ) < v := hv.1
  have hv₂ : v < (1/2 : ℝ) := by
    have h := hv.2
    change v < 1/4 + 1/4 at h
    linarith
  have hv₀ : 0 ≤ v := by linarith
  have hNorm : torusNorm v = v := by
    rw [torusNorm_eq,round_eq_zero_iff.mpr ⟨by linarith, hv₂⟩,Int.cast_zero,sub_zero,
      abs_of_nonneg hv₀]
  change 1/4 < ‖(z : Circle)‖
  rw [← heq]
  change 1/4 < torusNorm v
  rwa [hNorm]

/-- The multiples in the spatial interval are an exact image of the
shorter one-based interval. -/
theorem positiveInterval_multiples_eq_image {r N : ℕ} (hr : 0 < r) :
    (positiveInterval N).filter (fun x => (r : ℤ) ∣ x) =
      (positiveInterval (N/r)).image (fun y => (r : ℤ)*y) := by
  ext x
  have hrZ : (0 : ℤ) < r := by exact_mod_cast hr
  constructor
  · intro hx
    obtain ⟨hxI,⟨y,rfl⟩⟩ := Finset.mem_filter.mp hx
    obtain ⟨hx₁,hx₂⟩ := Finset.mem_Icc.mp hxI
    have hy₁ : 1 ≤ y := by
      by_contra! h
      have hy₀ : y ≤ 0 := by omega
      have hh := mul_nonpos_of_nonneg_of_nonpos hrZ.le hy₀
      linarith
    have hcast : (y.toNat : ℤ) = y := Int.toNat_of_nonneg (by omega)
    have hmul : y.toNat*r ≤ N := by
      have hm : (y.toNat : ℤ)*(r : ℤ) ≤ (N : ℤ) := by
        rw [hcast,mul_comm]
        exact hx₂
      exact_mod_cast hm
    have hNat : y.toNat ≤ N/r := (Nat.le_div_iff_mul_le hr).mpr hmul
    have hy₂ : y ≤ ((N/r : ℕ):ℤ) := by
      rw [← hcast]
      exact_mod_cast hNat
    exact Finset.mem_image.mpr ⟨y,Finset.mem_Icc.mpr ⟨hy₁,hy₂⟩,rfl⟩
  · intro hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hy₁,hy₂⟩ := Finset.mem_Icc.mp hy
    have hupper : (r : ℤ)*((N/r : ℕ):ℤ) ≤ (N : ℤ) := by
      exact_mod_cast (Nat.mul_comm r (N/r) ▸ Nat.div_mul_le_self N r)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨?_,?_⟩,dvd_mul_right _ _⟩
    · have h := mul_pos hrZ (show 0 < y by omega)
      omega
    · exact (mul_le_mul_of_nonneg_left hy₂ hrZ.le).trans hupper

/-- The grid of width 1/17 gives an exact finite obstruction. Its cell lies
in the multiples of `r` and has cardinality at least `floor(N/r)/17²`.
The arc exclusion holds for every natural parameter and hence for shifted
primes. -/
theorem exists_intro_rational_obstruction {α β : ℝ} {a r N : ℕ} (hr : 0 < r)
    (hlo : 0 ≤ β-(a : ℝ)/r) (hsmall : (β-(a : ℝ)/r)*(N : ℝ) < 1) :
    ∃ A : Finset ℤ, A ⊆ (positiveInterval N).filter (fun x => (r : ℤ) ∣ x) ∧
      ((N/r : ℕ) : ℝ) ≤ 289*(A.card : ℝ) ∧
      ∀ {x : ℤ} {n : ℕ}, x ∈ A → x+(n : ℤ) ∈ A → x+(n : ℤ)^2 ∈ A →
        ¬ introObstructionArc.Contains (heisenbergPhase α β (n : ℤ)) := by
  let D := (positiveInterval N).filter (fun x => (r : ℤ) ∣ x)
  have hD : D.card = N/r := by
    have hrZ : (r : ℤ) ≠ 0 := by exact_mod_cast hr.ne'
    dsimp [D]
    rw [positiveInterval_multiples_eq_image hr,
      Finset.card_image_of_injective _ (fun x y h => mul_left_cancel₀ hrZ h),
      positiveInterval,Int.card_Icc,add_sub_cancel_right,Int.toNat_natCast]
  let c₁ := -α*β/2
  let c₂ := α*β/2-α*((a : ℝ)/r)
  let color (x : ℤ) : Fin 17 × Fin 17 :=
    ⟨circleBin 17 (by decide) (c₁*(x : ℝ)),circleBin 17 (by decide) (c₂*(x : ℝ))⟩
  obtain ⟨b,hb⟩ := exists_large_color_cell D color
  let A := D.filter (fun x => color x=b)
  have hA : A ⊆ (positiveInterval N).filter (fun x => (r : ℤ) ∣ x) :=
    Finset.filter_subset _ _
  refine ⟨A,hA,?_,?_⟩
  · rw [hD] at hb
    simpa [A] using hb
  · intro x n hx hxn hxn₂ hJ
    have hx' := Finset.mem_filter.mp (hA hx)
    have hxn' := Finset.mem_filter.mp (hA hxn)
    have hn : n ≤ N := by
      have hxlo := (Finset.mem_Icc.mp hx'.1).1
      have hxhi := (Finset.mem_Icc.mp hxn'.1).2
      omega
    have hdiv : r ∣ n := by
      have hDiv := dvd_sub hxn'.2 hx'.2
      have he : x+(n : ℤ)-x = (n : ℤ) := by omega
      rw [he] at hDiv
      exact_mod_cast hDiv
    have hc (z : ℤ) (hz : z ∈ A) : color z=b := (Finset.mem_filter.mp hz).2
    have hc₁ := congrArg Prod.fst ((hc _ hxn).trans (hc _ hx).symm)
    have hc₂ := congrArg Prod.snd ((hc _ hxn₂).trans (hc _ hx).symm)
    have h₁ := norm_circle_sub_lt_of_circleBin_eq (L := 17) (by decide) hc₁
    have h₂ := norm_circle_sub_lt_of_circleBin_eq (L := 17) (by decide) hc₂
    change torusNorm (c₁*((x + (n : ℤ) : ℤ):ℝ)-c₁*(x : ℝ)) < 1/17 at h₁
    change torusNorm (c₂*((x + (n : ℤ)^2 : ℤ):ℝ)-c₂*(x : ℝ)) < 1/17 at h₂
    push_cast at h₁ h₂
    rw [show c₁*((x : ℝ)+(n : ℝ))-c₁*x = c₁*(n : ℝ) by ring] at h₁
    rw [show c₂*((x : ℝ)+(n : ℝ)^2)-c₂*x = c₂*(n : ℝ)^2 by ring] at h₂
    have hPhase : torusNorm (heisenbergPhase α β (n : ℤ)) < 1/8 := by
      rw [fastApproximation_heisenbergPhase hr hn hdiv hlo hsmall]
      change torusNorm (c₁*(n : ℝ)+c₂*(n : ℝ)^2) < _
      exact (torusNorm_add_le _ _).trans_lt (by linarith only [h₁,h₂])
    linarith only [hPhase,quarter_lt_norm_of_introObstructionArc hJ]

/-- At the precise floor scale in the introduction, the finite construction
has density at least `(2 · 17² · r)⁻¹`. -/
theorem exists_fastApproximationScale_obstruction {α β : ℝ} {a r j : ℕ}
    (hr : 0 < r) (hNr : r ≤ fastApproximationScale r j)
    (hlo : 0 ≤ β-(a : ℝ)/r) (hhi : β-(a : ℝ)/r < Real.exp (-((r : ℝ)^j))) :
    let N := fastApproximationScale r j
    ∃ A : Finset ℤ, A ⊆ positiveInterval N ∧
      1/(578*(r : ℝ)) ≤ setDensity A N ∧
      ∀ {x : ℤ} {n : ℕ}, x ∈ A → x+(n : ℤ) ∈ A → x+(n : ℤ)^2 ∈ A →
        ¬ introObstructionArc.Contains (heisenbergPhase α β (n : ℤ)) := by
  let N := fastApproximationScale r j
  obtain ⟨A,hSub,hcard,hAvoid⟩ :=
    exists_intro_rational_obstruction (α := α) hr hlo (fastApproximationScale_error hlo hhi)
  refine ⟨A,hSub.trans (Finset.filter_subset _ _),?_,hAvoid⟩
  have hn : 0 < N := hr.trans_le hNr
  have hnR : (0 : ℝ) < N := by exact_mod_cast hn
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hq : 1 ≤ N/r := (Nat.le_div_iff_mul_le hr).mpr (by simpa using hNr)
  have hN : (N : ℝ) ≤ 2*((N/r : ℕ):ℝ)*(r : ℝ) := by
    have hLt := (Nat.div_lt_iff_lt_mul hr).mp (show N/r < N/r+1 from Nat.lt_succ_self _)
    have hGe : (N/r+1) ≤ 2*(N/r) := by omega
    exact_mod_cast hLt.le.trans (Nat.mul_le_mul_right r hGe)
  apply (le_div_iff₀ hnR).mpr
  have hmul := mul_le_mul_of_nonneg_right hcard hrR.le
  calc
    _ = (N : ℝ)/(578*(r : ℝ)) := by ring
    _ ≤ _ := (div_le_iff₀ (show 0 < 578*(r : ℝ) by positivity)).mpr (by
      nlinarith only [hN,hmul])

end NilBohr
