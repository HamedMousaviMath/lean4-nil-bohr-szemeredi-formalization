import NilBohr.External

/-! Prime-model comparison in Proposition 4.1.

The arithmetic weights use the Cramér and Siegel models of KMTT §2.2.
The three analytic inputs correspond to KMTT Lemmas 2.2, 3.1 and 4.3(i),
arXiv:2608.19525v1. The basic normalized Gowers inequalities are explicit
premises as well, since the current project defines the cube sums without
developing the general Gowers–Cauchy–Schwarz theorem.
-/

open Filter
open scoped Topology BigOperators ComplexConjugate

namespace NilBohr

/-- KMTT's Cramér modulus. The factor eight is part of the model definition. -/
def cramerModulus (Q : ℕ) : ℕ := 8 * ∏ p ∈ primesThrough Q, p

noncomputable def mangoldtWeight (n : ℤ) : ℂ :=
  (ArithmeticFunction.vonMangoldt n.toNat : ℝ)

noncomputable def cramerWeight (Q : ℕ) (n : ℤ) : ℂ :=
  if n.toNat.Coprime (cramerModulus Q) then
    (((cramerModulus Q : ℕ) : ℝ) / (cramerModulus Q).totient : ℝ)
  else 0

/-- The exceptional-character data in KMTT Definition 2.3, at cutoff Q.
The conductors 1 and 2 have no primitive nonprincipal character. The threshold
is expressed after multiplying by the positive quantity `log Q`. -/
structure KMTTExceptionalZero (Q : ℕ) where
  conductor : ℕ
  conductor_ge : 3 ≤ conductor
  conductor_le : conductor ≤ Q
  character : DirichletCharacter ℂ conductor
  primitive : character.IsPrimitive
  real_character : ∀ x, (character x).im = 0
  beta : ℝ
  beta_pos : 0 < beta
  beta_lt_one : beta < 1
  zero : letI : NeZero conductor := ⟨by omega⟩
         character.LFunction (beta : ℂ) = 0
  threshold : (1 - beta) * Real.log Q ≤ (1 / 1000 : ℝ)

noncomputable def siegelWeight (Q : ℕ) (n : ℤ) : ℂ := by
  classical
  exact if hz : Nonempty (KMTTExceptionalZero Q) then
    let z := Classical.choice hz
    cramerWeight Q n * (1 - (((n.toNat : ℝ) ^ (z.beta - 1) : ℝ) : ℂ) * z.character (n : ZMod z.conductor))
    else cramerWeight Q n

theorem no_kmtt_exceptional_zero (hBanks : BanksRealZeroBound) (Q : ℕ) :
    ¬ Nonempty (KMTTExceptionalZero Q) := by
  rintro ⟨z⟩
  letI : NeZero z.conductor := ⟨by have := z.conductor_ge; omega⟩
  exact exclude_exceptional_model_zero hBanks z.conductor_ge z.conductor_le
    z.character z.primitive z.real_character z.beta_pos z.beta_lt_one z.zero z.threshold

theorem siegelWeight_eq_cramerWeight (hBanks : BanksRealZeroBound) (Q : ℕ) :
    siegelWeight Q = cramerWeight Q := by
  funext n
  simp [siegelWeight, no_kmtt_exceptional_zero hBanks Q]

/-- Normalized dilation (KMTT Lemma 2.2). The ambient interval includes
both endpoints `b` and `L+b`, as in the source. -/
def KMTTNormalizedDilation : Prop :=
  ∀ S : ℕ, 2 ≤ S → ∃ A : ℝ, 0 < A ∧
    ∀ (L q b : ℕ), 0 < q → q ≤ L → ∀ f : ℤ → ℂ,
      normalizedGowers S 1 (L / q : ℕ) (fun n => f ((q : ℤ) * n + (b : ℤ))) ≤
        A * (q : ℝ)^(((S : ℝ) + 1) / (2 : ℝ)^S) *
          normalizedGowers S (b : ℤ) ((L : ℤ) + (b : ℤ)) f

/-- KMTT Lemma 3.1 with independent model and Gowers-norm scales X and Y. -/
def KMTTAmbientPrimeModel (c₀ : ℝ) : Prop :=
  ∀ S : ℕ, 2 ≤ S → ∃ c A : ℝ, 0 < c ∧ 0 < A ∧
    ∀ X Y : ℕ, 3 ≤ X → 3 ≤ Y →
      Real.exp ((Real.log (Real.log (Y : ℝ))) ^ (1 / c)) ≤ cramerCutoff c₀ X →
      (cramerCutoff c₀ X : ℝ) ≤ Real.exp ((Real.log (Y : ℝ)) ^ (1 / 10 : ℝ)) →
      normalizedGowers S 1 (Y : ℤ)
        (fun n => mangoldtWeight n - siegelWeight (cramerCutoff c₀ X) n) ≤
        A * Real.exp (-(Real.log (cramerCutoff c₀ X)) ^ c)

/-- The full scale window (21) in the relative comparison. -/
def RelativeScaleWindow (d N M : ℕ) : Prop :=
  (N : ℝ) ^ (1 / (d : ℝ)) *
    Real.exp (-(d : ℝ) * Real.sqrt (Real.log N)) ≤ M ∧
  (M : ℝ) ≤ (N : ℝ) ^ (1 / (d : ℝ))

noncomputable def totientNormalize (q : ℕ) : ℝ := (q.totient : ℝ) / q

noncomputable def relativeCramerWeight (Q q : ℕ) (b n : ℤ) : ℂ :=
  (totientNormalize q : ℂ) * cramerWeight Q ((q : ℤ) * n + b)

/-- KMTT Lemma 4.3(i), specialized to the full interval M. The general
form permits an additional interval cutoff J, and this is its J=[M] case. -/
def KMTTRelativeCramer (c₀ : ℝ) : Prop :=
  ∀ S d : ℕ, 2 ≤ S → 0 < d →
    ∃ (c η A : ℝ) (N₀ : ℕ), 0 < c ∧ c ≤ 1 / 10 ∧ 0 < η ∧ 0 < A ∧
      ∀ N q w M : ℕ, 3 ≤ N → N₀ ≤ N → RelativeModulus c₀ c 2 N q w →
        RelativeScaleWindow d N M → ∀ b : ℤ, 1 ≤ b → b ≤ (q : ℤ) →
        b.natAbs.Coprime q →
        normalizedGowers S 1 (M : ℤ)
          (fun n => relativeCramerWeight (cramerCutoff c₀ N) q b n - 1) ≤
            A * (w : ℝ) ^ (-η)

private theorem sum_directions_at (L U x : ℤ) (hLU : L ≤ U)
    (hx : x ∈ Finset.Icc L U) (F : ℤ → ℂ)
    (hF : ∀ y, y ∉ Finset.Icc L U → F y = 0) :
    let W := (U-L).toNat
    (∑ j : Fin (2*W+1), F (x+(j.val : ℤ)-(W : ℤ))) = ∑ y ∈ Finset.Icc L U, F y := by
  dsimp only
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
    (∑ j : Fin (2*W+1), F (x+(j.val : ℤ)-(W : ℤ))) =
        ∑ y ∈ J, F y := by
      apply Finset.sum_bij (fun j _ => x+(j.val : ℤ)-(W : ℤ))
      · intro j hj
        apply Finset.mem_Icc.mpr
        have := j.isLt
        omega
      · intro i hi j hj he
        apply Fin.ext
        omega
      · intro y hy
        have hyy := Finset.mem_Icc.mp hy
        let j := (y-x+(W : ℤ)).toNat
        have hj : (j : ℤ) = y-x+(W : ℤ) := Int.toNat_of_nonneg (by omega)
        refine ⟨⟨j, by omega⟩, Finset.mem_univ _, ?_⟩
        dsimp
        omega
      · intros
        rfl
    _ = ∑ y ∈ Finset.Icc L U, F y := (Finset.sum_subset hJ (fun y _ hy => hF y hy)).symm

def gowersDirectionsHere (L U : ℤ) (S : ℕ)
    (h : Fin S → Fin (2*(U-L).toNat+1)) : List ℤ :=
  List.ofFn fun j => ((h j).val : ℤ) - ((U-L).toNat : ℤ)

/-- The finite Gowers cube power is a sum of squares when its order is
positive. The proof groups the first direction by its second endpoint. -/
theorem gowersCubePower_succ_eq_sum_sq (L U : ℤ) (hLU : L ≤ U) (S : ℕ) (f : ℤ → ℂ) :
    gowersCubePower (S+1) L U f =
      (∑ tail : Fin S → Fin (2*(U-L).toNat+1),
        ((‖∑ x ∈ Finset.Icc L U,
          cubeProduct (gowersDirectionsHere L U S tail) (zeroOutside L U f) x‖^2 : ℝ) : ℂ)) := by
  classical
  let W := (U-L).toNat
  let I := Finset.Icc L U
  let G (tail : Fin S → Fin (2*W+1)) (x : ℤ) :=
    cubeProduct (gowersDirectionsHere L U S tail) (zeroOutside L U f) x
  change (∑ x ∈ I, ∑ h : Fin (S+1) → Fin (2*W+1),
      cubeProduct (gowersDirectionsHere L U (S+1) h) (zeroOutside L U f) x) =
    ∑ tail : Fin S → Fin (2*W+1), ((‖∑ x ∈ I, G tail x‖^2 : ℝ) : ℂ)
  have hrow (x : ℤ) :
      (∑ h : Fin (S+1) → Fin (2*W+1),
        cubeProduct (gowersDirectionsHere L U (S+1) h) (zeroOutside L U f) x) =
      ∑ tail : Fin S → Fin (2*W+1), ∑ j : Fin (2*W+1),
        G tail x * conj (G tail (x+(j.val : ℤ)-(W : ℤ))) := by
    rw [Finset.sum_comm]
    symm
    let F (p : Fin (2*W+1) × (Fin S → Fin (2*W+1))) :=
      G p.2 x * conj (G p.2 (x+(p.1.val : ℤ)-(W : ℤ)))
    calc
      _ = ∑ p, F p := (Fintype.sum_prod_type F).symm
      _ = _ := by
        apply Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (S+1) => Fin (2*W+1)))
        intro p
        simp only [F, Fin.consEquiv_apply, gowersDirectionsHere, List.ofFn_succ, Fin.cons_zero,
          Fin.cons_succ, cubeProduct]
        simp [G, gowersDirectionsHere, W, sub_eq_add_neg, add_assoc]
  rw [show (∑ x ∈ I, ∑ h : Fin (S+1) → Fin (2*W+1),
      cubeProduct (gowersDirectionsHere L U (S+1) h) (zeroOutside L U f) x) =
      ∑ x ∈ I, ∑ tail : Fin S → Fin (2*W+1), ∑ j : Fin (2*W+1),
        G tail x * conj (G tail (x+(j.val : ℤ)-(W : ℤ))) from
    Finset.sum_congr rfl (fun x _ => hrow x)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun tail _ => ?_
  have hGzero : ∀ y, y ∉ I → G tail y = 0 := by
    intro y hy
    by_cases hn : G tail y = 0
    · exact hn
    · have hb := cubeProduct_nonzero_implies_bounds L U f (gowersDirectionsHere L U S tail) y hn
      exact False.elim (hy (Finset.mem_Icc.mpr ⟨hb.1, hb.2.1⟩))
  have hRows (x : ℤ) (hx : x ∈ I) :
      (∑ j : Fin (2*W+1), G tail x * conj (G tail (x+(j.val : ℤ)-(W : ℤ)))) =
      ∑ y ∈ I, G tail x * conj (G tail y) := by
    exact sum_directions_at L U x hLU hx (fun y => G tail x * conj (G tail y))
      (fun y hy => by simp [hGzero y hy])
  rw [Finset.sum_congr rfl hRows]
  simp_rw [← Finset.mul_sum, ← map_sum]
  rw [← Finset.sum_mul, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem gowersCubePower_re_nonnegative (L U : ℤ) (S : ℕ) (hS : 1 ≤ S) (f : ℤ → ℂ) :
    0 ≤ (gowersCubePower S L U f).re := by
  by_cases hLU : L ≤ U
  · cases S with
    | zero => omega
    | succ S =>
      rw [gowersCubePower_succ_eq_sum_sq L U hLU S f]
      change 0 ≤ Complex.reAddGroupHom _
      rw [map_sum]
      apply Finset.sum_nonneg
      intro i hi
      exact sq_nonneg _
  · have hi : Finset.Icc L U = ∅ := Finset.Icc_eq_empty hLU
    simp [gowersCubePower, hi]

/-- The finite normalized Gowers quantity is nonnegative at positive order. -/
theorem normalizedGowers_nonnegative (L U : ℤ) (S : ℕ) (hS : 1 ≤ S) (f : ℤ → ℂ) :
    0 ≤ normalizedGowers S L U f := by
  unfold normalizedGowers
  exact div_nonneg (Real.rpow_nonneg (gowersCubePower_re_nonnegative L U S hS f) _)
    (Real.rpow_nonneg (gowersCubePower_re_nonnegative L U S hS _) _)


private theorem cubeProduct_real_scale (A : ℝ) (steps : List ℤ) (f : ℤ → ℂ) (x : ℤ) :
    cubeProduct steps (fun n => (A : ℂ) * f n) x =
      (A : ℂ)^(2^steps.length : ℕ) * cubeProduct steps f x := by
  induction steps generalizing x with
  | nil => simp [cubeProduct]
  | cons t ts ih =>
    simp only [cubeProduct, ih, map_mul, map_pow, Complex.conj_ofReal, List.length_cons]
    rw [pow_succ (2 : ℕ), pow_mul]
    ring

private theorem cubePower_real_scale (L U : ℤ) (S : ℕ) (A : ℝ) (f : ℤ → ℂ) :
    gowersCubePower S L U (fun n => (A : ℂ) * f n) =
      (A : ℂ)^(2^S : ℕ) * gowersCubePower S L U f := by
  have hzero : zeroOutside L U (fun n => (A : ℂ) * f n) =
      (fun n => (A : ℂ) * zeroOutside L U f n) := by
    funext n
    unfold zeroOutside
    split_ifs <;> simp
  change (∑ x ∈ Finset.Icc L U, ∑ h : Fin S → Fin (2*(U-L).toNat+1),
      cubeProduct (gowersDirectionsHere L U S h) (zeroOutside L U (fun n => (A : ℂ)*f n)) x) =
    (A : ℂ)^(2^S : ℕ) * (∑ x ∈ Finset.Icc L U, ∑ h : Fin S → Fin (2*(U-L).toNat+1),
      cubeProduct (gowersDirectionsHere L U S h) (zeroOutside L U f) x)
  rw [hzero]
  simp [cubeProduct_real_scale, gowersDirectionsHere, Finset.mul_sum]

/-- Positive real homogeneity for the explicit finite normalization. -/
theorem normalizedGowers_real_scale (L U : ℤ) (S : ℕ) (hS : 1 ≤ S)
    (A : ℝ) (hA : 0 ≤ A) (f : ℤ → ℂ) :
    normalizedGowers S L U (fun n => (A : ℂ) * f n) = A * normalizedGowers S L U f := by
  unfold normalizedGowers
  rw [cubePower_real_scale, ← Complex.ofReal_pow, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Real.mul_rpow (pow_nonneg hA _) (gowersCubePower_re_nonnegative L U S hS f),
    ← Real.rpow_natCast_mul hA]
  have hExponent : ((2^S : ℕ) : ℝ) * ((2 : ℝ)^S)⁻¹ = 1 := by
    push_cast
    exact mul_inv_cancel₀ (by positivity)
  rw [hExponent, Real.rpow_one, mul_div_assoc]


/-- At order one, the normalized cube formula is the norm of the exact
finite mean on the positive interval. -/
theorem normalizedGowers_one_eq_norm_mean (M : ℕ) (hM : 0 < M) (f : ℤ → ℂ) :
    normalizedGowers 1 1 (M : ℤ) f =
      ‖(∑ y ∈ positiveInterval M, f y) / (M : ℂ)‖ := by
  letI : Unique (Fin 0 → Fin (2*((M : ℤ)-1).toNat+1)) :=
    ⟨⟨fun i => Fin.elim0 i⟩, fun f => funext fun i => Fin.elim0 i⟩
  have hOne (g : ℤ → ℂ) : gowersCubePower 1 1 (M : ℤ) g =
      ((‖∑ y ∈ positiveInterval M, g y‖^2 : ℝ) : ℂ) := by
    have h := gowersCubePower_succ_eq_sum_sq 1 (M : ℤ) (by exact_mod_cast hM) 0 g
    simp only [zero_add, Fintype.sum_unique, gowersDirectionsHere, List.ofFn_zero,
      cubeProduct] at h
    rw [h]
    have hSum : (∑ y ∈ positiveInterval M, zeroOutside 1 (M : ℤ) g y) =
        ∑ y ∈ positiveInterval M, g y := by
      refine Finset.sum_congr rfl fun y hy => ?_
      exact if_pos hy
    rw [show Finset.Icc 1 (M : ℤ) = positiveInterval M by rfl, hSum]
  have hPow (s : ℝ) (hs : 0 ≤ s) : (s^2)^(((2 : ℝ)^1)⁻¹) = s := by
    rw [pow_one, ← one_div, ← Real.sqrt_eq_rpow, Real.sqrt_sq hs]
  unfold normalizedGowers
  rw [hOne f, hOne (fun _ => 1), Complex.ofReal_re, Complex.ofReal_re,
    hPow _ (norm_nonneg _), hPow _ (norm_nonneg _), Finset.sum_const,
    card_positiveInterval, nsmul_eq_mul, mul_one, norm_div]

/-- Standard consequences of the Gowers–Cauchy–Schwarz inequality in the
normalization of KMTT §2.3. A separate bound for the mean allows the exact
normalizing constants of each order. -/
structure NormalizedGowersLaws (S : ℕ) : Prop where
  triangle : ∀ (L U : ℤ), L ≤ U → ∀ f g : ℤ → ℂ,
    normalizedGowers S L U (fun n => f n + g n) ≤
      normalizedGowers S L U f + normalizedGowers S L U g
  meanBound : ∃ D : ℝ, 0 < D ∧ ∀ M : ℕ, 0 < M → ∀ f : ℤ → ℂ,
    ‖(∑ y ∈ positiveInterval M, f y) / (M : ℂ)‖ ≤
      D * normalizedGowers S 1 (M : ℤ) f

/-- The adjacent-order monotonicity stated in KMTT §2.3. The implicit constant
depends on the order and is uniform over all positive interval lengths. -/
def NormalizedGowersAdjacentMonotonicity : Prop :=
  ∀ s : ℕ, 1 ≤ s → ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 0 < M → ∀ f : ℤ → ℂ,
    normalizedGowers s 1 (M : ℤ) f ≤ C * normalizedGowers (s+1) 1 (M : ℤ) f

/-- Derive the mean estimate from the standard adjacent-order comparison,
using the exact order-one identity for the project normalization. -/
theorem normalizedGowers_meanBound_of_adjacent
    (hMono : NormalizedGowersAdjacentMonotonicity) (S : ℕ) (hS : 1 ≤ S) :
    ∃ D : ℝ, 0 < D ∧ ∀ M : ℕ, 0 < M → ∀ f : ℤ → ℂ,
      ‖(∑ y ∈ positiveInterval M, f y) / (M : ℂ)‖ ≤ D * normalizedGowers S 1 (M : ℤ) f := by
  induction S with
  | zero => omega
  | succ s ih =>
    by_cases hz : s = 0
    · subst s
      exact ⟨1, one_pos, fun M hM f => by
        rw [one_mul, normalizedGowers_one_eq_norm_mean M hM f]⟩
    · have hs : 1 ≤ s := by omega
      obtain ⟨D, hD, hMean⟩ := ih hs
      obtain ⟨C, hC, hStep⟩ := hMono s hs
      refine ⟨D*C, mul_pos hD hC, ?_⟩
      intro M hM f
      simpa only [mul_assoc] using ((hMean M hM f).trans
        (mul_le_mul_of_nonneg_left (hStep M hM f) hD.le))

/-- Supply the remaining Gowers inputs in their standard triangle and
adjacent-order forms. -/
theorem NormalizedGowersLaws.of_triangle_and_adjacent
    {S : ℕ} (hS : 1 ≤ S)
    (hTriangle : ∀ (L U : ℤ), L ≤ U → ∀ f g : ℤ → ℂ,
      normalizedGowers S L U (fun n => f n + g n) ≤
        normalizedGowers S L U f + normalizedGowers S L U g)
    (hMono : NormalizedGowersAdjacentMonotonicity) :
    NormalizedGowersLaws S :=
  ⟨hTriangle, normalizedGowers_meanBound_of_adjacent hMono S hS⟩

theorem totientNormalize_nonneg (q : ℕ) : 0 ≤ totientNormalize q := by
  unfold totientNormalize
  positivity

theorem totientNormalize_le_one {q : ℕ} (hq : 0 < q) : totientNormalize q ≤ 1 := by
  unfold totientNormalize
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  exact (div_le_one hqr).mpr (by exact_mod_cast Nat.totient_le q)

theorem lambdaModulus_cast_eq (q : ℕ) (n : ℤ) :
    (lambdaModulus q n : ℂ) =
      (totientNormalize q : ℂ) * mangoldtWeight ((q : ℤ) * n + 1) := by
  simp [lambdaModulus, mangoldtWeight, totientNormalize]

/-- The estimate (51) at the two independent scales, after Banks eliminates
the exceptional branch of the model. -/
theorem ambient_cramer_bound_of_kmtt (c₀ : ℝ) (hBanks : BanksRealZeroBound)
    (hAmbient : KMTTAmbientPrimeModel c₀) (S : ℕ) (hS : 2 ≤ S) :
    ∃ c A : ℝ, 0 < c ∧ 0 < A ∧
      ∀ N Y : ℕ, 3 ≤ N → 3 ≤ Y →
        Real.exp ((Real.log (Real.log (Y : ℝ))) ^ (1 / c)) ≤ cramerCutoff c₀ N →
        (cramerCutoff c₀ N : ℝ) ≤ Real.exp ((Real.log (Y : ℝ)) ^ (1 / 10 : ℝ)) →
        normalizedGowers S 1 (Y : ℤ)
          (fun n => mangoldtWeight n - cramerWeight (cramerCutoff c₀ N) n) ≤
          A * Real.exp (-(Real.log (cramerCutoff c₀ N)) ^ c) := by
  obtain ⟨c, A, hc, hA, h⟩ := hAmbient S hS
  refine ⟨c, A, hc, hA, ?_⟩
  intro N Y hN hY hlow hhigh
  simpa only [siegelWeight_eq_cramerWeight hBanks] using h N Y hN hY hlow hhigh

/-- The finite passage to the exact normalized progression and ambient
endpoint used in Proposition 4.1. -/
theorem relative_cramer_error_le (hDil : KMTTNormalizedDilation)
    (S : ℕ) (hS : 2 ≤ S) :
    ∃ A : ℝ, 0 < A ∧ ∀ Q q M : ℕ, 0 < q → 0 < M →
      normalizedGowers S 1 (M : ℤ)
        (fun y => (lambdaModulus q y : ℂ) - relativeCramerWeight Q q 1 y) ≤
          A * (q : ℝ)^(((S : ℝ) + 1) / (2 : ℝ)^S) *
            normalizedGowers S 1 ((q * M + 1 : ℕ) : ℤ)
              (fun n => mangoldtWeight n - cramerWeight Q n) := by
  obtain ⟨A, hA, hD⟩ := hDil S hS
  refine ⟨A, hA, ?_⟩
  intro Q q M hq hM
  have hs₁ : 1 ≤ S := by omega
  have hd := hD (q * M) q 1 hq (Nat.le_mul_of_pos_right _ hM)
    (fun n => mangoldtWeight n - cramerWeight Q n)
  have he (y : ℤ) : (lambdaModulus q y : ℂ) - relativeCramerWeight Q q 1 y =
      (totientNormalize q : ℂ) *
        (mangoldtWeight ((q : ℤ) * y + 1) - cramerWeight Q ((q : ℤ) * y + 1)) := by
    rw [lambdaModulus_cast_eq, relativeCramerWeight, mul_sub]
  simp_rw [he]
  rw [normalizedGowers_real_scale 1 (M : ℤ) S hs₁ _ (totientNormalize_nonneg q)]
  refine (mul_le_of_le_one_left (normalizedGowers_nonnegative _ _ S hs₁ _)
    (totientNormalize_le_one hq)).trans ?_
  simpa [Nat.mul_div_right _ hq] using hd


private theorem eventually_mul_rpow_le_rpow {a b C : ℝ} (hab : a < b) :
    ∀ᶠ t : ℝ in atTop, C * t^a ≤ t^b := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (tendsto_rpow_atTop (sub_pos.mpr hab)).eventually_ge_atTop C] with t ht hC
  have ht' : 0 < t := lt_of_lt_of_le zero_lt_one ht
  calc
    C * t^a ≤ t^(b-a) * t^a := mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg ht'.le _)
    _ = t^((b-a)+a) := (Real.rpow_add ht' _ _).symm
    _ = t^b := by ring_nf

private theorem eventually_log_add_const_le_rpow {a : ℝ} (ha : 0 < a) (C : ℝ) :
    ∀ᶠ t : ℝ in atTop, Real.log t + C ≤ t^a := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (isLittleO_log_rpow_atTop ha).bound (by norm_num : 0 < (1 / 2 : ℝ)),
    (tendsto_rpow_atTop ha).eventually_ge_atTop (2 * C)] with t ht hlog hpow
  have hlog' : Real.log t ≤ (1 / 2 : ℝ) * t^a := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg ht),
      abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ t) a)] using hlog
  linarith

private theorem tendsto_log_natCast_atTop : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

theorem cramerCutoff_log_bounds {c₀ : ℝ} (hc₀ : 0 ≤ c₀) {N : ℕ}
    (hN : 1 ≤ Real.log (N : ℝ)) :
    0 < (cramerCutoff c₀ N : ℝ) ∧
    (Real.log (N : ℝ))^c₀ ≤ Real.log (cramerCutoff c₀ N) ∧
    Real.log (cramerCutoff c₀ N) ≤ 2 * (Real.log (N : ℝ))^c₀ := by
  let t := (Real.log (N : ℝ))^c₀
  have ht : 1 ≤ t := Real.one_le_rpow hN hc₀
  have hQlo : Real.exp t ≤ (cramerCutoff c₀ N : ℝ) := Nat.le_ceil _
  have hQpos := (Real.exp_pos t).trans_le hQlo
  have hQup : (cramerCutoff c₀ N : ℝ) ≤ 2 * Real.exp t :=
    Nat.ceil_le_two_mul (by
      have : 1 ≤ Real.exp t := Real.one_le_exp (by linarith)
      linarith)
  refine ⟨hQpos, ?_, ?_⟩
  · have hh := Real.log_le_log (Real.exp_pos t) hQlo
    rwa [Real.log_exp] at hh
  · have hh := Real.log_le_log hQpos hQup
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.exp_ne_zero t),
      Real.log_exp] at hh
    have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    change Real.log (cramerCutoff c₀ N) ≤ 2 * t
    linarith

/-- The two-scale window in KMTT Lemma 3.1, uniformly for the interval
scale Y whose logarithm is between the stated multiples of log N. -/
theorem eventually_cramerCutoff_compatible {c₀ c a : ℝ} (hc₀ : 0 < c₀)
    (hc₀' : c₀ < 1 / 11) (hc : 0 < c) (ha : 0 < a) :
    ∀ᶠ N : ℕ in atTop, ∀ Y : ℕ,
      1 ≤ Real.log (Y : ℝ) →
      Real.log (N : ℝ) / a ≤ Real.log (Y : ℝ) →
      Real.log (Y : ℝ) ≤ 3 * Real.log (N : ℝ) →
        Real.exp ((Real.log (Real.log (Y : ℝ))) ^ (1 / c)) ≤ cramerCutoff c₀ N ∧
        (cramerCutoff c₀ N : ℝ) ≤ Real.exp ((Real.log (Y : ℝ)) ^ (1 / 10 : ℝ)) := by
  have hdom := eventually_mul_rpow_le_rpow (a := c₀) (b := (1 / 10 : ℝ))
    (C := 2 * a^(1 / 10 : ℝ)) (by linarith)
  have hlogdom := eventually_log_add_const_le_rpow (mul_pos hc₀ hc) (Real.log 3)
  filter_upwards [tendsto_log_natCast_atTop.eventually_ge_atTop 1,
    tendsto_log_natCast_atTop.eventually hdom, tendsto_log_natCast_atTop.eventually hlogdom] with
    N hNt hNdom hNlog
  intro Y hYpos hYlo hYhi
  let t := Real.log (N : ℝ)
  have htpos : 0 < t := by dsimp [t]; linarith
  obtain ⟨hQpos, hQlo, hQhi⟩ := cramerCutoff_log_bounds hc₀.le hNt
  have hLpos : 0 < Real.log (Y : ℝ) := by linarith
  have hloglog : Real.log (Real.log (Y : ℝ)) ≤ t^(c₀ * c) := by
    have hh := Real.log_le_log hLpos hYhi
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) htpos.ne'] at hh
    linarith
  constructor
  · have hh := Real.rpow_le_rpow (Real.log_nonneg hYpos) hloglog
      (div_nonneg zero_le_one hc.le)
    rw [← Real.rpow_mul htpos.le] at hh
    have hexp : (c₀ * c) * (1 / c) = c₀ := by field_simp
    rw [hexp] at hh
    rw [← Real.exp_log hQpos]
    exact Real.exp_le_exp.mpr (hh.trans hQlo)
  · apply (Real.log_le_iff_le_exp hQpos).mp
    refine hQhi.trans ?_
    have hpow := Real.rpow_le_rpow (div_nonneg htpos.le ha.le) hYlo
      (by norm_num : 0 ≤ (1 / 10 : ℝ))
    apply le_trans _ hpow
    rw [Real.div_rpow htpos.le ha.le]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos ha _)).mpr
    convert hNdom using 1
    ring

/-- The ambient scale qM+1 lies in the range where the two-scale KMTT
lemma can be applied. Both logarithmic comparisons are uniform in q,w,M. -/
theorem eventually_relative_ambient_scale {d : ℕ} (hd : 0 < d) {c₀ cRel : ℝ}
    (hc₀ : 0 < c₀) (hc₀' : c₀ < 1 / 11) (_hcRel : 0 < cRel) (hcRel' : cRel ≤ 1 / 10)
    (w₀ : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ q w M : ℕ,
      RelativeModulus c₀ cRel w₀ N q w → RelativeScaleWindow d N M →
      0 < M ∧ 3 ≤ q*M+1 ∧ 1 ≤ Real.log (q*M+1 : ℕ) ∧
      Real.log (N : ℝ) / (2 * (d : ℝ)) ≤ Real.log (q*M+1 : ℕ) ∧
      Real.log (q*M+1 : ℕ) ≤ 3 * Real.log (N : ℝ) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hAbsorb := eventually_mul_rpow_le_rpow (a := c₀) (b := 1) (C := 2) (by linarith)
  have hsqrt := eventually_mul_rpow_le_rpow (a := (1 / 2 : ℝ)) (b := 1)
    (C := 2 * (d : ℝ) * d) (by norm_num)
  filter_upwards [eventually_ge_atTop (3 : ℕ),
    tendsto_log_natCast_atTop.eventually_ge_atTop 1,
    tendsto_log_natCast_atTop.eventually_ge_atTop (2 * (d : ℝ) * max 1 (Real.log 3)),
    tendsto_log_natCast_atTop.eventually hAbsorb, tendsto_log_natCast_atTop.eventually hsqrt]
    with N hN hNt hbig habs hs
  intro q w M hRel hWindow
  let t := Real.log (N : ℝ)
  have ht : 1 ≤ t := hNt
  have htpos : 0 < t := by linarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hq := hRel.2.1
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hMpow : 0 < (N : ℝ) ^ (1 / (d : ℝ)) := Real.rpow_pos_of_pos hNpos _
  have hMR : (0 : ℝ) < M := (mul_pos hMpow (Real.exp_pos _)).trans_le hWindow.1
  have hM : 0 < M := by exact_mod_cast hMR
  obtain ⟨_, hQl, hQh⟩ := cramerCutoff_log_bounds hc₀.le hNt
  let L := Real.log (cramerCutoff c₀ N : ℝ)
  have hL : 1 ≤ L := (Real.one_le_rpow ht hc₀.le).trans hQl
  have hsmall : L^(2*cRel) ≤ L := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hL (show 2*cRel ≤ 1 by linarith))
  have hqsq : (w : ℝ)^2 ≤ L^(2*cRel) := by
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg w) hRel.2.2.1 2
    calc
      (w : ℝ)^2 ≤ (L^cRel)^2 := hh
      _ = L^(2*cRel) := by
        rw [mul_comm, Real.rpow_mul (by linarith : 0 ≤ L)]
        norm_num
  have hqlog : Real.log (q : ℝ) ≤ t := by
    have hh := hRel.2.2.2.2.2.trans (hqsq.trans (hsmall.trans hQh))
    exact hh.trans (by simpa only [Real.rpow_one] using habs)
  have hMhigh := Real.log_le_log hMR hWindow.2
  rw [Real.log_rpow hNpos] at hMhigh
  have hMlo := Real.log_le_log (mul_pos hMpow (Real.exp_pos _)) hWindow.1
  rw [Real.log_mul hMpow.ne' (Real.exp_ne_zero _), Real.log_rpow hNpos,
    Real.log_exp] at hMlo
  have hs' : 2 * (d : ℝ) * d * Real.sqrt t ≤ t := by
    simpa only [Real.rpow_one, Real.sqrt_eq_rpow] using hs
  have hMfloor : t / (2 * (d : ℝ)) ≤ Real.log (M : ℝ) := by
    apply (div_le_iff₀ (by positivity : (0:ℝ) < 2 * (d : ℝ))).mpr
    have hm := mul_le_mul_of_nonneg_right hMlo (show 0 ≤ 2 * (d : ℝ) by positivity)
    have htEq : (1 / (d : ℝ) * t + -(d : ℝ) * Real.sqrt t) * (2 * (d : ℝ)) =
        2*t - 2 * (d : ℝ) * d * Real.sqrt t := by field_simp; ring
    rw [htEq] at hm
    linarith
  have hYlower : t / (2 * (d : ℝ)) ≤ Real.log (q*M+1 : ℕ) :=
    hMfloor.trans (Real.log_le_log hMR (by
      exact_mod_cast (Nat.le_mul_of_pos_left M hq).trans (Nat.le_succ _)))
  have hYlog : max 1 (Real.log 3) ≤ Real.log (q*M+1 : ℕ) := by
    refine ((le_div_iff₀ (by positivity : (0:ℝ) < 2 * (d : ℝ))).mpr ?_).trans hYlower
    simpa [mul_comm] using hbig
  have hYge : 3 ≤ q*M+1 := by
    have hh := (le_max_right 1 (Real.log 3)).trans hYlog
    have hh' := (Real.strictMonoOn_log.le_iff_le
      (show (3 : ℝ) ∈ Set.Ioi 0 by norm_num)
      (show (((q*M+1 : ℕ) : ℝ)) ∈ Set.Ioi 0 by
        change (0 : ℝ) < ((q*M+1 : ℕ) : ℝ)
        positivity)).mp hh
    exact_mod_cast hh'
  have hYhi : Real.log (q*M+1 : ℕ) ≤ 3*t := by
    have hYcmp : (q*M+1 : ℕ) ≤ 2*(q*M) := by
      have hn : 0 < q*M := Nat.mul_pos hq hM
      omega
    have hh := Real.log_le_log (by positivity : (0:ℝ) < ((q*M+1 : ℕ) : ℝ))
      (by exact_mod_cast hYcmp : ((q*M+1 : ℕ) : ℝ) ≤ (2 : ℝ) * ((q : ℝ)*(M : ℝ)))
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (mul_pos hqR hMR).ne',
      Real.log_mul hqR.ne' hMR.ne'] at hh
    have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    have hMle : Real.log (M : ℝ) ≤ t := hMhigh.trans (by
      have hdone : (1 : ℝ) ≤ d := by exact_mod_cast hd
      have := mul_le_mul_of_nonneg_right ((div_le_one hdR).mpr hdone) htpos.le
      simpa [t] using this)
    linarith
  exact ⟨hM, hYge, (le_max_left _ _).trans hYlog, hYlower, hYhi⟩


private theorem eventually_dilation_absorption {a c cRel : ℝ} (ha : 0 ≤ a)
    (hc : 0 < c) (hcRel : 0 < cRel) (hgap : 2*cRel < c) :
    ∀ᶠ L : ℝ in atTop, ∀ q w : ℕ, 0 < q → 1 ≤ w →
      (w : ℝ) ≤ L^cRel → Real.log (q : ℝ) ≤ (w : ℝ)^2 →
      (q : ℝ)^a * Real.exp (-(L^c)) ≤ (w : ℝ)^(-1 : ℝ) := by
  have hdom := eventually_mul_rpow_le_rpow (a := 2*cRel) (b := c)
    (C := 2*a) hgap
  have hlog := (isLittleO_log_rpow_atTop hc).bound
    (show 0 < 1 / (2*cRel) by positivity)
  filter_upwards [eventually_ge_atTop (1 : ℝ), hdom, hlog] with L hL hD hlogL
  intro q w hq hw hW hQ
  have hLpos : 0 < L := by linarith
  have hwp : (0 : ℝ) < w := by exact_mod_cast (show 0 < w by omega)
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq
  have hqPow : Real.log (q : ℝ) ≤ L^(2*cRel) := by
    refine hQ.trans ?_
    calc
      (w : ℝ)^2 ≤ (L^cRel)^2 := pow_le_pow_left₀ hwp.le hW 2
      _ = L^(2*cRel) := by
        rw [mul_comm, Real.rpow_mul hLpos.le]
        norm_num
  have hwLog := Real.log_le_log hwp hW
  rw [Real.log_rpow hLpos] at hwLog
  have hLlog : 2*cRel * Real.log L ≤ L^c := by
    have hh : Real.log L ≤ 1 / (2*cRel) * L^c := by
      simpa [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hL),
        abs_of_nonneg (Real.rpow_nonneg hLpos.le c)] using hlogL
    have hMul := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 2*cRel)
    rwa [← mul_assoc, mul_one_div_cancel (by positivity : 2*cRel ≠ 0), one_mul] at hMul
  rw [Real.rpow_def_of_pos hqp, Real.rpow_def_of_pos hwp, ← Real.exp_add,
    Real.exp_le_exp]
  have hqA := mul_le_mul_of_nonneg_right hqPow ha
  linarith [hD, hLlog, hwLog, hqA]

private theorem eventually_log_cramerCutoff_ge {c₀ : ℝ} (hc₀ : 0 < c₀) (L₀ : ℝ) :
    ∀ᶠ N : ℕ in atTop, L₀ ≤ Real.log (cramerCutoff c₀ N : ℝ) := by
  filter_upwards [tendsto_log_natCast_atTop.eventually_ge_atTop 1,
    ((tendsto_rpow_atTop hc₀).comp tendsto_log_natCast_atTop).eventually_ge_atTop L₀]
    with N hN hL
  exact hL.trans (cramerCutoff_log_bounds hc₀.le hN).2.1

/-- The target of Proposition 4.1, including the first-moment consequence. -/
def HighOrderRelativePrimeUniformity (c₀ : ℝ) (d S : ℕ) : Prop :=
  ∃ (cRel η C : ℝ) (w₀ N₀ : ℕ), 0 < cRel ∧ 0 < η ∧ 0 < C ∧ 16 ≤ w₀ ∧
    ∀ N q w M : ℕ, N₀ ≤ N → RelativeModulus c₀ cRel w₀ N q w →
      RelativeScaleWindow d N M →
      normalizedGowers S 1 (M : ℤ) (fun y => (lambdaModulus q y : ℂ) - 1) ≤ C * (w : ℝ)^(-η) ∧
      ‖(∑ y ∈ positiveInterval M, (lambdaModulus q y : ℂ)) / (M : ℂ) - 1‖ ≤ C * (w : ℝ)^(-η)

/-- Proposition 4.1 from the quoted prime-model estimates and standard
normalized Gowers laws. All choices of small exponent and all scale
thresholds are uniform in (q,w,M). -/
theorem high_order_relative_prime_of_kmtt {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hc₀' : c₀ < 1 / 11) (hBanks : BanksRealZeroBound)
    (hAmbient : KMTTAmbientPrimeModel c₀) (hDilation : KMTTNormalizedDilation)
    (hRelative : KMTTRelativeCramer c₀) {d S : ℕ} (hd : 0 < d) (hS : 2 ≤ S)
    (hG : NormalizedGowersLaws S) :
    HighOrderRelativePrimeUniformity c₀ d S := by
  obtain ⟨c, A, hc, hA, hAmbient'⟩ := ambient_cramer_bound_of_kmtt c₀ hBanks hAmbient S hS
  obtain ⟨D, hD, hDilation'⟩ := relative_cramer_error_le hDilation S hS
  obtain ⟨cK, ηK, B, Nₖ, hcK, hcK₁, hηK, hB, hRelative'⟩ := hRelative S d hS hd
  obtain ⟨E, hE, hMean⟩ := hG.meanBound
  let cRel := min cK (c/4)
  let η := min ηK 1
  let a := ((S : ℝ) + 1) / (2 : ℝ)^S
  have ha : 0 ≤ a := by positivity
  have hcRel : 0 < cRel := lt_min hcK (by positivity)
  have hcRel₁ : cRel ≤ 1 / 10 := (min_le_left _ _).trans hcK₁
  have hη : 0 < η := lt_min hηK zero_lt_one
  have hη₁ : η ≤ 1 := min_le_right _ _
  have hηK' : η ≤ ηK := min_le_left _ _
  have hgap : 2 * cRel < c := by
    have h : cRel ≤ c/4 := min_le_right _ _
    linarith
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp (eventually_dilation_absorption ha hc hcRel hgap)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hEventually : ∀ᶠ N : ℕ in atTop,
      ∀ q w M : ℕ, RelativeModulus c₀ cRel 16 N q w → RelativeScaleWindow d N M →
      normalizedGowers S 1 (M : ℤ) (fun y => (lambdaModulus q y : ℂ) - 1) ≤
        ((D*A+B)*(E+1)) * (w : ℝ)^(-η) ∧
      ‖(∑ y ∈ positiveInterval M, (lambdaModulus q y : ℂ)) / (M : ℂ) - 1‖ ≤
        ((D*A+B)*(E+1)) * (w : ℝ)^(-η) := by
    filter_upwards [eventually_ge_atTop (3 : ℕ), eventually_ge_atTop Nₖ,
      tendsto_log_natCast_atTop.eventually_ge_atTop 1,
      eventually_log_cramerCutoff_ge hc₀ L₀,
      eventually_relative_ambient_scale hd hc₀ hc₀' hcRel hcRel₁ 16,
      eventually_cramerCutoff_compatible hc₀ hc₀' hc (show 0 < 2 * (d : ℝ) by positivity)]
      with N hN hNk hNt hL hScl hCompatible
    intro q w M hMod hWindow
    let Q := cramerCutoff c₀ N
    let Y := q*M+1
    have hq := hMod.2.1
    have hw : 16 ≤ w := hMod.1
    have hw1 : 1 ≤ w := by omega
    have hwR : (1 : ℝ) ≤ w := by exact_mod_cast hw1
    obtain ⟨hM, hY, hYlog, hYlo, hYhi⟩ := hScl q w M hMod hWindow
    have hmZ : (1 : ℤ) ≤ M := by exact_mod_cast hM
    obtain ⟨hQlo, hQhi⟩ := hCompatible Y hYlog hYlo hYhi
    have hAest := hAmbient' N Y hN hY hQlo hQhi
    have hDlimit := hL₀ (Real.log (Q : ℝ)) hL q w hq hw1 hMod.2.2.1 hMod.2.2.2.2.2
    have hLone : 1 ≤ Real.log (Q : ℝ) :=
      (Real.one_le_rpow hNt hc₀.le).trans (cramerCutoff_log_bounds hc₀.le hNt).2.1
    have hModK : RelativeModulus c₀ cK 2 N q w :=
      ⟨by omega, hq, hMod.2.2.1.trans
        (Real.rpow_le_rpow_of_exponent_le hLone (min_le_left _ _)),
        hMod.2.2.2⟩
    have hBEst := hRelative' N q w M hN hNk hModK hWindow 1 le_rfl
      (by exact_mod_cast hq) (by simp)
    have hDilEst := hDilation' Q q M hq hM
    have hsmall : normalizedGowers S 1 (M : ℤ)
        (fun y => (lambdaModulus q y : ℂ) - relativeCramerWeight Q q 1 y) ≤
        D*A*(w : ℝ)^(-1 : ℝ) := by
      apply hDilEst.trans
      calc
        D * (q : ℝ)^a * normalizedGowers S 1 (Y : ℤ)
            (fun n => mangoldtWeight n - cramerWeight Q n) ≤
          D * (q : ℝ)^a * (A * Real.exp (-(Real.log Q)^c)) := by
            apply mul_le_mul_of_nonneg_left hAest
            exact mul_nonneg hD.le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        _ = D*A*((q : ℝ)^a * Real.exp (-(Real.log Q)^c)) := by ring
        _ ≤ D*A*(w : ℝ)^(-1 : ℝ) := mul_le_mul_of_nonneg_left hDlimit (mul_nonneg hD.le hA.le)
    have hSplit (n : ℤ) : (lambdaModulus q n : ℂ) - 1 =
        ((lambdaModulus q n : ℂ) - relativeCramerWeight Q q 1 n) +
        (relativeCramerWeight Q q 1 n - 1) := by ring
    have hUnif : normalizedGowers S 1 (M : ℤ) (fun y => (lambdaModulus q y : ℂ) - 1) ≤
        (D*A+B) * (w : ℝ)^(-η) := by
      simp_rw [hSplit]
      refine (hG.triangle 1 (M : ℤ) hmZ _ _).trans
        ((add_le_add hsmall hBEst).trans ?_)
      rw [add_mul]
      exact add_le_add
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hwR (by linarith)) (by positivity))
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hwR (by linarith)) hB.le)
    have hUnifNonneg : 0 ≤ (D*A+B) * (w : ℝ)^(-η) := by positivity
    have hMne : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
    have hAvg := hMean M hM (fun y => (lambdaModulus q y : ℂ) - 1)
    simp only [Finset.sum_sub_distrib, Finset.sum_const, card_positiveInterval, nsmul_eq_mul,
      mul_one, sub_div, div_self hMne] at hAvg
    refine ⟨hUnif.trans ?_, hAvg.trans ((mul_le_mul_of_nonneg_left hUnif hE.le).trans ?_)⟩
    · have h := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ E+1 by linarith) hUnifNonneg
      convert h using 1 <;> ring
    · have h := mul_le_mul_of_nonneg_right (show E ≤ E+1 by linarith) hUnifNonneg
      convert h using 1
      ring
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hEventually
  exact ⟨cRel, η, (D*A+B)*(E+1), 16, N₀, hcRel, hη, by positivity, le_rfl,
    fun N q w M hN => hN₀ N hN q w M⟩


/-- The same-scale ambient estimate (66) used in the prime local phase
argument. Its exponent is the product of the two fixed positive
cutoff exponents. -/
theorem ambient_cramer_self_scale_of_kmtt {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hc₀' : c₀ < 1/11) (hBanks : BanksRealZeroBound)
    (hAmbient : KMTTAmbientPrimeModel c₀) {S : ℕ} (hS : 2 ≤ S) :
    ∃ c A : ℝ, 0 < c ∧ 0 < A ∧
      ∀ᶠ N : ℕ in atTop,
        normalizedGowers S 1 (N : ℤ)
          (fun n => mangoldtWeight n - cramerWeight (cramerCutoff c₀ N) n) ≤
          A * Real.exp (-((Real.log (N : ℝ)) ^ c)) := by
  obtain ⟨c, A, hc, hA, hAmb⟩ := ambient_cramer_bound_of_kmtt c₀ hBanks hAmbient S hS
  refine ⟨c₀*c, A, mul_pos hc₀ hc, hA, ?_⟩
  filter_upwards [eventually_ge_atTop (3 : ℕ), tendsto_log_natCast_atTop.eventually_ge_atTop 1,
    eventually_cramerCutoff_compatible hc₀ hc₀' hc (a := 1) one_pos]
    with N hN hlog hCompat
  have hlog₀ : 0 ≤ Real.log (N : ℝ) := by linarith
  obtain ⟨hlo, hhi⟩ := hCompat N hlog (by simp)
    (by linarith : Real.log (N : ℝ) ≤ 3*Real.log (N : ℝ))
  apply (hAmb N N hN hN hlo hhi).trans
  apply mul_le_mul_of_nonneg_left _ hA.le
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  rw [Real.rpow_mul hlog₀]
  exact Real.rpow_le_rpow (Real.rpow_nonneg hlog₀ _)
    (cramerCutoff_log_bounds hc₀.le hlog).2.1 hc.le

theorem eventually_small_modulus_log {c₀ cRel : ℝ} (hc₀ : 0 < c₀)
    (hc₀' : c₀ < 1 / 11) (hcRel : cRel ≤ 1 / 10) (w₀ : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ q w : ℕ, RelativeModulus c₀ cRel w₀ N q w →
      Real.log (q : ℝ) ≤ Real.sqrt (Real.log (N : ℝ)) / 2 := by
  have hDom := eventually_mul_rpow_le_rpow (a := c₀*(1/5)) (b := 1/2) (C := 4)
    (by linarith)
  filter_upwards [tendsto_log_natCast_atTop.eventually_ge_atTop 1,
    tendsto_log_natCast_atTop.eventually hDom] with N hlog hNdom
  intro q w hMod
  let L := Real.log (cramerCutoff c₀ N : ℝ)
  let t := Real.log (N : ℝ)
  have ht : 0 ≤ t := by dsimp [t]; linarith
  obtain ⟨_, hQlo, hQhi⟩ := cramerCutoff_log_bounds hc₀.le hlog
  have hLone : 1 ≤ L := (Real.one_le_rpow hlog hc₀.le).trans hQlo
  have hL : 0 ≤ L := by linarith
  have hw := hMod.2.2.1
  have hq := hMod.2.2.2.2.2
  calc
    Real.log (q : ℝ) ≤ (w : ℝ)^2 := hq
    _ ≤ (L^cRel)^2 := pow_le_pow_left₀ (Nat.cast_nonneg w) hw 2
    _ = L^(2*cRel) := by rw [mul_comm, Real.rpow_mul hL]; norm_num
    _ ≤ L^(1/5 : ℝ) := Real.rpow_le_rpow_of_exponent_le hLone (by linarith)
    _ ≤ (2*t^c₀)^(1/5 : ℝ) := Real.rpow_le_rpow hL hQhi (by norm_num)
    _ ≤ 2*t^(c₀*(1/5)) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Real.rpow_nonneg ht _),
        ← Real.rpow_mul ht]
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg ht _)
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
          (by norm_num : (1/5 : ℝ) ≤ 1)
    _ ≤ Real.sqrt t / 2 := by
      rw [Real.sqrt_eq_rpow]
      linarith

/-- The paper's floor-defined parameter length satisfies the full relative
window for all sufficiently large N, uniformly in the admissible modulus. -/
theorem eventually_parameterLength_relativeScaleWindow {c₀ cRel : ℝ}
    (hc₀ : 0 < c₀) (hc₀' : c₀ < 1 / 11) (hcRel : cRel ≤ 1/10)
    {d : ℕ} (hd : 0 < d) (w₀ : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ q w : ℕ, RelativeModulus c₀ cRel w₀ N q w →
      RelativeScaleWindow d N (parameterLength N q d) := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hd₁ : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hSqrtDom := eventually_mul_rpow_le_rpow (C := (d : ℝ)) (a := 1/2) (b := 1)
    (by norm_num)
  filter_upwards [eventually_ge_atTop (3 : ℕ), tendsto_log_natCast_atTop.eventually_ge_atTop 1,
    tendsto_log_natCast_atTop.eventually_ge_atTop (2*(d : ℝ)*Real.log 2),
    ((tendsto_rpow_atTop (show 0 < (1/2 : ℝ) by norm_num)).comp
      tendsto_log_natCast_atTop).eventually_ge_atTop (2*Real.log 2),
    tendsto_log_natCast_atTop.eventually hSqrtDom,
    eventually_small_modulus_log hc₀ hc₀' hcRel w₀]
    with N hN hlog hNbig hSqrtBig hSqrt hSmall
  intro q w hMod
  let t := Real.log (N : ℝ)
  let Q := (q : ℝ)^ (d-1)
  let V := ((N : ℝ) / Q)^((d : ℝ)⁻¹)
  let M := parameterLength N q d
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hq : 0 < q := hMod.2.1
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hqR' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hQ : 0 < Q := pow_pos hqR _
  have hV : 0 < V := Real.rpow_pos_of_pos (div_pos hNpos hQ) _
  have hQ₁ : 1 ≤ Q := one_le_pow₀ hqR'
  have hlogV : Real.log V = (t - ((d-1 : ℕ) : ℝ)*Real.log (q : ℝ))/(d : ℝ) := by
    dsimp only [V]
    rw [Real.log_rpow (div_pos hNpos hQ), Real.log_div hNpos.ne' hQ.ne']
    have hlogQ : Real.log Q = ((d-1 : ℕ) : ℝ) * Real.log (q : ℝ) := Real.log_pow _ _
    rw [hlogQ, div_eq_mul_inv, mul_comm]
  have hqLog : Real.log (q : ℝ) ≤ Real.sqrt t / 2 := hSmall q w hMod
  have hqLog₀ : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hqR'
  have hlogVlower : t/(d : ℝ) - Real.sqrt t/2 ≤ Real.log V := by
    have hRatio : ((d-1 : ℕ) : ℝ) / (d : ℝ) ≤ 1 :=
      (div_le_one hdR).mpr (by exact_mod_cast Nat.sub_le d 1)
    have hComp := mul_le_mul_of_nonneg_right hRatio hqLog₀
    rw [hlogV, sub_div]
    have hFact : ((d-1 : ℕ) : ℝ)*Real.log (q : ℝ)/(d : ℝ) ≤
        Real.log (q : ℝ) := by simpa [div_mul_eq_mul_div] using hComp
    linarith
  have hVlog₂ : Real.log 2 ≤ Real.log V := by
    have hh : (d : ℝ)*Real.sqrt t ≤ t := by
      simpa only [Real.sqrt_eq_rpow, Real.rpow_one] using hSqrt
    have hh' := (le_div_iff₀ hdR).mpr
      (show Real.sqrt t * (d : ℝ) ≤ t by simpa only [mul_comm] using hh)
    have hdiv : 2*Real.log 2 ≤ t/(d : ℝ) := by
      apply (le_div_iff₀ hdR).mpr
      convert hNbig using 1
      ring
    linarith
  have hTwo : (2 : ℝ) ≤ V :=
    (Real.strictMonoOn_log.le_iff_le (by norm_num : (2 : ℝ) ∈ Set.Ioi 0) hV).mp hVlog₂
  have hFloor : V / 2 ≤ (M : ℝ) := by
    have hlt : V < (M : ℝ) + 1 := Nat.lt_floor_add_one V
    linarith
  constructor
  · have hp : 0 < (N : ℝ)^(1/(d : ℝ)) := Real.rpow_pos_of_pos hNpos _
    have hLogTarget : Real.log ((N : ℝ)^(1/(d : ℝ)) *
        Real.exp (-(d : ℝ)*Real.sqrt t)) ≤ Real.log (V/2) := by
      rw [Real.log_mul hp.ne' (Real.exp_ne_zero _), Real.log_rpow hNpos, Real.log_exp,
        Real.log_div hV.ne' (by norm_num : (2 : ℝ) ≠ 0)]
      have hSqrtBig' : 2*Real.log 2 ≤ Real.sqrt t := by
        simpa only [Real.sqrt_eq_rpow] using hSqrtBig
      have hOne := mul_le_mul_of_nonneg_right hd₁ (Real.sqrt_nonneg t)
      have he : 1/(d : ℝ) * Real.log (N : ℝ) = t/(d : ℝ) := by
        dsimp [t]
        ring
      rw [he]
      linarith
    exact ((Real.strictMonoOn_log.le_iff_le
      (mul_pos hp (Real.exp_pos _)) (div_pos hV (by norm_num))).mp hLogTarget).trans hFloor
  · have hFloor' : (M : ℝ) ≤ V := Nat.floor_le hV.le
    refine hFloor'.trans ?_
    rw [one_div]
    exact Real.rpow_le_rpow (div_nonneg hNpos.le hQ.le) (div_le_self hNpos.le hQ₁)
      (inv_nonneg.mpr hdR.le)


/-- An arbitrary fixed logarithmic saving for the same-scale difference.
This comparison is uniform in the averaging interval's length. -/
theorem ambient_cramer_log_saving_of_kmtt {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hc₀' : c₀ < 1 / 11) (hBanks : BanksRealZeroBound)
    (hAmbient : KMTTAmbientPrimeModel c₀) {S : ℕ} (hS : 2 ≤ S)
    {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      normalizedGowers S 1 (N : ℤ)
        (fun n => mangoldtWeight n - cramerWeight (cramerCutoff c₀ N) n) ≤
        C * (Real.log (N : ℝ))^(-A) := by
  obtain ⟨c, C, hc, hC, hEstimate⟩ := ambient_cramer_self_scale_of_kmtt hc₀ hc₀' hBanks hAmbient hS
  refine ⟨C, hC, ?_⟩
  have hAsymp := (isLittleO_log_rpow_atTop hc).bound
    (show 0 < A⁻¹ by positivity)
  filter_upwards [hEstimate, tendsto_log_natCast_atTop.eventually_ge_atTop 1,
    tendsto_log_natCast_atTop.eventually hAsymp] with N hb hN hdom
  let t := Real.log (N : ℝ)
  have ht : 0 < t := by dsimp [t]; linarith
  have hlog : Real.log t ≤ A⁻¹ * t^c := by
    simpa [t, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hN),
      abs_of_nonneg (Real.rpow_nonneg ht.le c)] using hdom
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  change Real.exp (-(t^c)) ≤ t^(-A)
  nth_rw 2 [Real.rpow_def_of_pos ht]
  rw [Real.exp_le_exp]
  have h := mul_le_mul_of_nonneg_left hlog hA.le
  rw [← mul_assoc, mul_inv_cancel₀ hA.ne', one_mul] at h
  linarith

end NilBohr
