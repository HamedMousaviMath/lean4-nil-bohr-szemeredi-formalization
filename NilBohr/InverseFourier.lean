import NilBohr.Differencing
import NilBohr.TwoInput
import Mathlib.Analysis.Fourier.ZMod

/-! The finite Fourier extraction and local Plancherel steps in Lemma 5.1. -/

open MeasureTheory ComplexConjugate
open scoped BigOperators

namespace NilBohr

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- Fourier sum of the input on a progression (a+L T) in the progression
coordinate (t). -/
noncomputable def localFourier (f : ℤ → ℂ) (T : Finset ℤ) (a L : ℤ)
    (θ : Circle) : ℂ :=
  ∑ t ∈ T, f (a + L * t) * fourier t θ

/-- The correlation of the multiplicative difference with a character in
the progression coordinate. -/
noncomputable def localDifferenceCorrelation (f : ℤ → ℂ) (T : Finset ℤ) (a L : ℤ)
    (ω : Circle) (h : ℤ) : ℂ :=
  ∑ t ∈ T, spatialMultiplicativeDifference f h (a + L * t) * fourier t ω

private theorem norm_fourier_character (t : ℤ) (θ : Circle) : ‖fourier t θ‖ = 1 := by
  rw [fourier_apply]
  exact _root_.Circle.norm_coe _

private theorem fourier_neg_frequency (t : ℤ) (θ : Circle) :
    fourier t (-θ) = conj (fourier t θ) := by
  rw [← fourier_neg]
  simp

private theorem fourier_add_frequency (t : ℤ) (θ ξ : Circle) :
    fourier t (θ + ξ) = fourier t θ * fourier t ξ := by
  simp only [fourier_apply, smul_add, AddCircle.toCircle_add, _root_.Circle.coe_mul]

private theorem fourier_smul_frequency (t L : ℤ) (ξ : Circle) :
    fourier t (L • ξ) = fourier (L * t) ξ := by
  simp only [fourier_apply, smul_smul, mul_comm t L]

private theorem sum_shift_transform (X H : Finset ℤ) (f : ℤ → ℂ)
    (hf : SupportedOn X f) (x : ℤ) (hCover : ∀ y ∈ X, y - x ∈ H) (ξ : Circle) :
    (∑ h ∈ H, f (x + h) * fourier (-h) ξ) =
      fourier x ξ * spatialFourier X f (-1) ξ := by
  have hSubset : X.image (fun y => y - x) ⊆ H := by
    intro h hh
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hh
    exact hCover y hy
  have hRestrict :
      (∑ h ∈ X.image (fun y => y - x), f (x + h) * fourier (-h) ξ) =
      (∑ h ∈ H, f (x + h) * fourier (-h) ξ) := by
    apply Finset.sum_subset hSubset
    intro h hh hnot
    have hx : x + h ∉ X := by
      intro hx
      exact hnot (Finset.mem_image.mpr ⟨x + h, hx, by omega⟩)
    simp [hf _ hx]
  rw [← hRestrict, Finset.sum_image]
  · unfold spatialFourier
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    rw [show x + (y - x) = y by omega,
      show -(y - x) = x + -1 * y by omega, fourier_add]
    ring
  · intro u hu v hv huv
    omega

/-- Fourier transform of the differentiated block correlation. The shift
summation may use any finite set containing every possible difference. -/
theorem spatialFourier_localDifferenceCorrelation (X H T : Finset ℤ)
    (f : ℤ → ℂ) (hf : SupportedOn X f) (a L : ℤ)
    (hCover : ∀ y ∈ X, ∀ t ∈ T, y - (a + L * t) ∈ H) (ω ξ : Circle) :
    spatialFourier H (localDifferenceCorrelation f T a L ω) (-1) ξ =
      spatialFourier X f (-1) ξ * (fourier a ξ *
        conj (localFourier f T a L (-(ω + L • ξ)))) := by
  conv_lhs => unfold spatialFourier
  simp only [localDifferenceCorrelation, Finset.sum_mul, spatialMultiplicativeDifference,
    neg_one_mul]
  rw [Finset.sum_comm]
  simp only [localFourier, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [show (∑ h ∈ H, f (a + L * t + h) * conj (f (a + L * t)) * fourier t ω *
        fourier (-h) ξ) =
      (conj (f (a + L * t)) * fourier t ω) *
        ∑ h ∈ H, f (a + L * t + h) * fourier (-h) ξ by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro h hh
          ring]
  rw [sum_shift_transform X H f hf (a + L * t) (fun y hy => hCover y hy t ht) ξ,
    map_mul, fourier_neg_frequency, starRingEnd_self_apply, fourier_add_frequency,
    fourier_smul_frequency, fourier_add]
  ring

/-- The local Plancherel bound in (31). The constant `S` can be chosen as
the maximum of `‖localFourier‖` by the extreme value theorem. -/
theorem localDifferenceCorrelation_plancherel (X H T : Finset ℤ)
    (f : ℤ → ℂ) (hf : SupportedOn X f) (a L : ℤ)
    (hCover : ∀ y ∈ X, ∀ t ∈ T, y - (a + L * t) ∈ H)
    (ω : Circle) (S : ℝ) (hS : ∀ θ, ‖localFourier f T a L θ‖ ≤ S) :
    (∑ h ∈ H, ‖localDifferenceCorrelation f T a L ω h‖ ^ 2) ≤
      S ^ 2 * ∑ x ∈ X, ‖f x‖ ^ 2 := by
  let g := localDifferenceCorrelation f T a L ω
  have hg : SupportedOn H g := by
    intro h hh
    unfold g localDifferenceCorrelation
    apply Finset.sum_eq_zero
    intro t ht
    have hnot : a + L * t + h ∉ X := by
      intro hy
      apply hh
      simpa using hCover (a + L * t + h) hy t ht
    simp [spatialMultiplicativeDifference, hf _ hnot]
  rw [← integral_norm_spatialFourier_sq H g (-1) (by norm_num) hg,
    ← integral_norm_spatialFourier_sq X f (-1) (by norm_num) hf, ← integral_const_mul]
  have hCont (Y : Finset ℤ) (F : ℤ → ℂ) : Continuous (spatialFourier Y F (-1)) := by
    unfold spatialFourier
    exact continuous_finset_sum _ (fun _ _ => continuous_const.mul (fourier _).continuous)
  have hInt {G : Type} [NormedAddCommGroup G] {F : Circle → G}
      (hF : Continuous F) : Integrable F normalizedCircleMeasure :=
    hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  apply integral_mono (hInt ((hCont H g).norm.pow 2))
    (hInt (continuous_const.mul ((hCont X f).norm.pow 2)))
  intro ξ
  dsimp only [g]
  rw [spatialFourier_localDifferenceCorrelation X H T f hf a L hCover ω ξ,
    norm_mul, norm_mul, norm_fourier_character, one_mul, Complex.norm_conj, mul_pow,
    mul_comm]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) (hS _) 2) (sq_nonneg _)


/-- The maximum defining the local Fourier norm is attained on the circle. -/
theorem exists_localFourier_maximizer (f : ℤ → ℂ) (T : Finset ℤ) (a L : ℤ) :
    ∃ θ : Circle, ∀ ξ : Circle, ‖localFourier f T a L ξ‖ ≤ ‖localFourier f T a L θ‖ := by
  have hCont : Continuous (localFourier f T a L) := by
    unfold localFourier
    exact continuous_finset_sum _ (fun _ _ => continuous_const.mul (fourier _).continuous)
  obtain ⟨θ, -, hθ⟩ := isCompact_univ.exists_isMaxOn
    (Set.univ_nonempty (α := Circle)) hCont.norm.continuousOn
  exact ⟨θ, fun ξ => hθ (Set.mem_univ ξ)⟩

/-- The elementary bound on the maximum used after local Plancherel. -/
theorem norm_localFourier_le_card (f : ℤ → ℂ) (T : Finset ℤ) (a L : ℤ)
    (hf : ∀ t ∈ T, ‖f (a + L * t)‖ ≤ 1) (θ : Circle) :
    ‖localFourier f T a L θ‖ ≤ (T.card : ℝ) := by
  unfold localFourier
  refine (norm_sum_le _ _).trans ?_
  simpa only [norm_mul, norm_fourier_character, mul_one, Finset.sum_const,
    nsmul_eq_mul] using Finset.sum_le_sum (g := fun _ => (1 : ℝ)) hf

/-- The circle frequency (m/q) represented by a residue class (m). -/
noncomputable def rationalCircleFrequency {q : ℕ} (m : ZMod q) : Circle :=
  (((m.val : ℝ) / (q : ℝ)) : Circle)

theorem stdAddChar_mul_intCast_eq_fourier {q : ℕ} [NeZero q] (m : ZMod q) (t : ℤ) :
    ZMod.stdAddChar (m * (t : ZMod q)) = fourier t (rationalCircleFrequency m) := by
  have he : m * (t : ZMod q) = ((((m.val : ℤ) * t) : ℤ) : ZMod q) := by
    push_cast
    rw [ZMod.natCast_zmod_val]
  rw [he, ZMod.stdAddChar_coe, rationalCircleFrequency, fourier_coe_apply]
  push_cast
  congr 1
  ring

/-- Normalized Fourier inversion on the finite cyclic group. A bounded
function on `ZMod q` produces coefficients of modulus at most one. -/
theorem exists_cyclic_fourier_coefficients {q : ℕ} [NeZero q]
    (Φ : ZMod q → ℂ) (hΦ : ∀ z, ‖Φ z‖ ≤ 1) :
    ∃ c : ZMod q → ℂ, (∀ m, ‖c m‖ ≤ 1) ∧
      ∀ t : ℤ, Φ (t : ZMod q) =
        ∑ m, c m * fourier t (rationalCircleFrequency m) := by
  let c : ZMod q → ℂ := fun m => (q : ℂ)⁻¹ * ZMod.dft Φ m
  refine ⟨c, ?_, ?_⟩
  · intro m
    have hs : ‖ZMod.dft Φ m‖ ≤ (q : ℝ) := by
      rw [ZMod.dft_apply]
      refine (norm_sum_le _ _).trans ?_
      have hb (j : ZMod q) : ‖ZMod.stdAddChar (-(j * m)) • Φ j‖ ≤ 1 := by
        simp only [smul_eq_mul, norm_mul, ZMod.stdAddChar_apply, _root_.Circle.norm_coe, one_mul]
        exact hΦ j
      simpa only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, ZMod.card, mul_one] using
        Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hb j)
    have hq : (0 : ℝ) < (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
    dsimp only [c]
    rw [norm_mul, norm_inv, Complex.norm_natCast, ← div_eq_inv_mul]
    exact (div_le_iff₀ hq).mpr (by simpa using hs)
  · intro t
    conv_lhs => rw [← (ZMod.dft (N := q) (E := ℂ)).symm_apply_apply Φ]
    rw [ZMod.invDFT_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro m hm
    simp only [smul_eq_mul, c, stdAddChar_mul_intCast_eq_fourier]
    ring

/-- Freeze a slowly varying function at a representative in each of the
(q') residue classes of the progression coordinate. The representative
is allowed to lie at the progression origin, since the original witness is
defined on all of (mathbb Z). -/
theorem periodic_block_approximation (φ : ℤ → ℂ) (a L : ℤ) (V q : ℕ)
    (hq : 0 < q) (hφ : ∀ x, ‖φ x‖ ≤ 1) (D : ℝ) (hD : 0 ≤ D)
    (hLip : ∀ x j : ℤ, ‖φ (x + (q : ℤ) * L * j) - φ x‖ ≤ D * |(j : ℝ)|) :
    ∃ Φ : ZMod q → ℂ, (∀ z, ‖Φ z‖ ≤ 1) ∧
      ∀ t ∈ positiveInterval V,
        ‖φ (a + L * t) - Φ (t : ZMod q)‖ ≤ D * ((V : ℝ) / (q : ℝ)) := by
  let Φ : ZMod q → ℂ := fun z => φ (a + L * (z.val : ℤ))
  letI : NeZero q := ⟨hq.ne'⟩
  refine ⟨Φ, fun z => hφ _, ?_⟩
  intro t ht
  obtain ⟨ht₁, ht₂⟩ := Finset.mem_Icc.mp ht
  have hqInt : (0 : ℤ) < q := by exact_mod_cast hq
  have hqReal : (0 : ℝ) < q := by exact_mod_cast hq
  have ht₀ : 0 ≤ t := by omega
  have hdiv : 0 ≤ t / (q : ℤ) := Int.ediv_nonneg ht₀ hqInt.le
  have hval : (((t : ZMod q).val : ℕ) : ℤ) = t % (q : ℤ) := by
    rw [ZMod.val_intCast]
  have hEq : a + L * t = a + L * (t % (q : ℤ)) + (q : ℤ) * L * (t / (q : ℤ)) := by
    calc
      a + L * t = a + L * (t % (q : ℤ) + q * (t / (q : ℤ))) := by rw [Int.emod_add_ediv]
      _ = _ := by ring
  have hdivision : ((t / (q : ℤ) : ℤ) : ℝ) ≤ (V : ℝ) / (q : ℝ) := by
    apply (le_div_iff₀ hqReal).mpr
    have hmod := Int.emod_nonneg t hqInt.ne'
    have htEq := Int.emod_add_ediv t (q : ℤ)
    have hle : (t / (q : ℤ)) * (q : ℤ) ≤ (V : ℤ) := by nlinarith
    exact_mod_cast hle
  rw [hEq, show Φ (t : ZMod q) = φ (a + L * (t % (q : ℤ))) by simp only [Φ, hval]]
  refine (hLip _ _).trans (mul_le_mul_of_nonneg_left ?_ hD)
  rwa [abs_of_nonneg (by exact_mod_cast hdiv)]


/-- A single differentiated correlation against a weight with a small
modular Lipschitz constant yields one rational frequency across the blocks.
The explicit loss is the total number of sampled positions times the
pointwise approximation error. -/
theorem exists_rational_frequency_of_periodic_blocks {ι : Type*} (A : Finset ι)
    (a : ι → ℤ) (L : ℤ) (V q : ℕ) (hq : 0 < q)
    (f φ : ℤ → ℂ) (h : ℤ) (hf : ∀ x, ‖f x‖ ≤ 1) (hφ : ∀ x, ‖φ x‖ ≤ 1)
    (D R : ℝ) (hD : 0 ≤ D)
    (hLip : ∀ x j : ℤ, ‖φ (x + (q : ℤ) * L * j) - φ x‖ ≤ D * |(j : ℝ)|)
    (hCorr : R ≤ ‖∑ i ∈ A, ∑ t ∈ positiveInterval V,
      spatialMultiplicativeDifference f h (a i + L * t) * φ (a i + L * t)‖) :
    ∃ m : ZMod q, (R - (A.card : ℝ) * V * (D * ((V : ℝ) / q))) / q ≤
      ∑ i ∈ A, ‖localDifferenceCorrelation f (positiveInterval V) (a i) L
        (rationalCircleFrequency m) h‖ := by
  classical
  letI : NeZero q := ⟨hq.ne'⟩
  let T := positiveInterval V
  let B := fun i t => spatialMultiplicativeDifference f h (a i + L * t)
  let E := D * ((V : ℝ) / q)
  choose Φ hΦ hApprox using
    fun i : ι => periodic_block_approximation φ (a i) L V q hq hφ D hD hLip
  choose c hcNorm hcFormula using fun i : ι => exists_cyclic_fourier_coefficients (Φ i) (hΦ i)
  let Z := ∑ i ∈ A, ∑ t ∈ T, B i t * φ (a i + L * t)
  let Z' := ∑ i ∈ A, ∑ t ∈ T, B i t * Φ i (t : ZMod q)
  have hB (i : ι) (t : ℤ) : ‖B i t‖ ≤ 1 := by
    unfold B spatialMultiplicativeDifference
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_one₀ (hf _) (norm_nonneg _) (hf _)
  have hError : ‖Z - Z'‖ ≤ (A.card : ℝ) * V * E := by
    unfold Z Z'
    simp only [← Finset.sum_sub_distrib, ← mul_sub]
    refine (norm_sum_le _ _).trans ?_
    trans ∑ _i ∈ A, ∑ _t ∈ T, E
    · apply Finset.sum_le_sum
      intro i hi
      refine (norm_sum_le _ _).trans ?_
      apply Finset.sum_le_sum
      intro t ht
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hB i t) |>.trans (hApprox i t ht)
    · simp [T, positiveInterval, Int.card_Icc, nsmul_eq_mul, mul_assoc]
  have hLower : R - (A.card : ℝ) * V * E ≤ ‖Z'‖ := by
    have ht := norm_add_le (Z - Z') Z'
    rw [sub_add_cancel] at ht
    change R ≤ ‖Z‖ at hCorr
    linarith
  let W : ZMod q → ℝ := fun m =>
    ∑ i ∈ A, ‖localDifferenceCorrelation f T (a i) L (rationalCircleFrequency m) h‖
  have hExpand (i : ι) : (∑ t ∈ T, B i t * Φ i (t : ZMod q)) =
      ∑ m : ZMod q, c i m * localDifferenceCorrelation f T (a i) L
        (rationalCircleFrequency m) h := by
    simp_rw [hcFormula i, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m hm
    unfold localDifferenceCorrelation
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    unfold B
    ring
  have hUpper : ‖Z'‖ ≤ ∑ m : ZMod q, W m := by
    unfold Z'
    simp_rw [hExpand]
    refine (norm_sum_le _ _).trans ?_
    trans ∑ i ∈ A, ∑ m : ZMod q,
        ‖localDifferenceCorrelation f T (a i) L (rationalCircleFrequency m) h‖
    · apply Finset.sum_le_sum
      intro i hi
      refine (norm_sum_le _ _).trans ?_
      apply Finset.sum_le_sum
      intro m hm
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hcNorm i m)
    · exact le_of_eq (Finset.sum_comm)
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ W Finset.univ_nonempty
  refine ⟨m, (div_le_iff₀ (by exact_mod_cast hq : (0 : ℝ) < q)).mpr ?_⟩
  refine (hLower.trans hUpper).trans ?_
  simpa only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, ZMod.card, mul_comm] using
    Finset.sum_le_sum (s := Finset.univ) (fun z hz => hm z hz)

/-- The finite set of candidate rational frequencies for denominators at
most (Q). Frequencies are circle elements, so repeated representations
are counted only once. -/
noncomputable def boundedRationalFrequencies (Q : ℕ) : Finset Circle :=
  ((Finset.range Q) ×ˢ (Finset.Icc 1 Q)).image
    (fun z : ℕ × ℕ => (((z.1 : ℝ) / (z.2 : ℝ)) : Circle))

theorem rationalCircleFrequency_mem_bounded (Q q : ℕ) (hq : 0 < q) (hqQ : q ≤ Q)
    (m : ZMod q) : rationalCircleFrequency m ∈ boundedRationalFrequencies Q := by
  letI : NeZero q := ⟨hq.ne'⟩
  apply Finset.mem_image.mpr
  refine ⟨(m.val, q), ?_, rfl⟩
  exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (m.val_lt.trans_le hqQ),
    Finset.mem_Icc.mpr ⟨hq, hqQ⟩⟩

theorem card_boundedRationalFrequencies_le (Q : ℕ) :
    (boundedRationalFrequencies Q).card ≤ Q ^ 2 := by
  unfold boundedRationalFrequencies
  refine Finset.card_image_le.trans ?_
  rw [Finset.card_product, Finset.card_range, Nat.card_Icc]
  simp [pow_two]

/-- Pigeonhole among finitely many candidate frequencies, retaining all
shifts assigned to the maximizing frequency. -/
theorem exists_common_frequency {ι Ω : Type*} (H : Finset ι) (F : Finset Ω)
    (hH : H.Nonempty) (P : ι → Ω → Prop)
    (hP : ∀ h ∈ H, ∃ ω ∈ F, P h ω) :
    ∃ ω ∈ F, ∃ G ⊆ H, (∀ h ∈ G, P h ω) ∧ H.card ≤ F.card * G.card := by
  classical
  have hExists : ∀ h : H, ∃ ω ∈ F, P h ω := fun h => hP h h.property
  choose g hgMem hg using hExists
  have hF : F.Nonempty := by
    obtain ⟨h, hh⟩ := hH
    exact ⟨g ⟨h, hh⟩, hgMem ⟨h, hh⟩⟩
  let score := fun ω : Ω => (H.attach.filter (fun h => g h = ω)).card
  obtain ⟨ω, hω, hMax⟩ := Finset.exists_max_image F score hF
  let G := (H.attach.filter (fun h => g h = ω)).image Subtype.val
  have hCard : G.card = score ω := Finset.card_image_of_injective _ Subtype.val_injective
  refine ⟨ω, hω, G, ?_, ?_, ?_⟩
  · intro h hh
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hh
    exact j.property
  · intro h hh
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hh
    rw [← (Finset.mem_filter.mp hj).2]
    exact hg j
  · calc
      H.card = ∑ ω' ∈ F, score ω' := by
        simpa only [score, Finset.card_attach] using
          Finset.card_eq_sum_card_fiberwise (s := H.attach) (t := F) (f := g)
            (fun ⟨h, hh⟩ _ => hgMem ⟨h, hh⟩)
      _ ≤ ∑ _ω' ∈ F, score ω := Finset.sum_le_sum (fun j hj => hMax j hj)
      _ = F.card * G.card := by simp [hCard]


/-- Combine a common differentiated frequency with local Plancherel and
Cauchy--Schwarz. The local frequency in the conclusion is optimized separately
on every progression, as in the proof of Lemma 5.1. -/
theorem exists_localFourier_mass_of_common_frequency {ι : Type*}
    (A : Finset ι) (X H G : Finset ℤ) (hG : G ⊆ H) (hGne : G.Nonempty)
    (f : ℤ → ℂ) (hf : SupportedOn X f) (a : ι → ℤ) (L : ℤ) (V : ℕ)
    (hCover : ∀ i ∈ A, ∀ y ∈ X, ∀ t ∈ positiveInterval V,
      y - (a i + L * t) ∈ H)
    (hunit : ∀ x, ‖f x‖ ≤ 1) (ω : Circle) (R : ℝ) (hR : 0 ≤ R)
    (hCorr : ∀ h ∈ G, R ≤ ∑ i ∈ A,
      ‖localDifferenceCorrelation f (positiveInterval V) (a i) L ω h‖) :
    ∃ θ : ι → Circle, (∀ i ξ, ‖localFourier f (positiveInterval V) (a i) L ξ‖ ≤
      ‖localFourier f (positiveInterval V) (a i) L (θ i)‖) ∧
      (G.card : ℝ) * R ^ 2 ≤ (A.card : ℝ) * (∑ x ∈ X, ‖f x‖ ^ 2) * (V : ℝ) *
        (∑ i ∈ A, ‖localFourier f (positiveInterval V) (a i) L (θ i)‖) := by
  classical
  choose θ hθ using fun i : ι => exists_localFourier_maximizer f (positiveInterval V) (a i) L
  refine ⟨θ, hθ, ?_⟩
  let C := fun h i => ‖localDifferenceCorrelation f (positiveInterval V) (a i) L ω h‖
  let S := fun i => ‖localFourier f (positiveInterval V) (a i) L (θ i)‖
  let E := ∑ x ∈ X, ‖f x‖ ^ 2
  have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hs (i : ι) : S i ≤ (V : ℝ) := by
    have hi := norm_localFourier_le_card f (positiveInterval V) (a i) L
      (fun _ _ => hunit _) (θ i)
    simpa [S, positiveInterval, Int.card_Icc] using hi
  have hLower : (G.card : ℝ) * R ≤ ∑ p ∈ G ×ˢ A, C p.1 p.2 := by
    rw [Finset.sum_product]
    simpa only [Finset.sum_const, nsmul_eq_mul] using
      Finset.sum_le_sum (s := G) (fun h hh => hCorr h hh)
  have hCS : (∑ p ∈ G ×ˢ A, C p.1 p.2) ^ 2 ≤
      ((G.card : ℝ) * (A.card : ℝ)) * ∑ p ∈ G ×ˢ A, (C p.1 p.2) ^ 2 := by
    simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one,
      Finset.card_product, Nat.cast_mul] using
      Finset.sum_mul_sq_le_sq_mul_sq (G ×ˢ A) (fun _ => (1 : ℝ)) (fun p => C p.1 p.2)
  have hUpper : (∑ p ∈ G ×ˢ A, (C p.1 p.2) ^ 2) ≤ E * V * ∑ i ∈ A, S i := by
    rw [Finset.sum_product, Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    calc
      _ ≤ ∑ h ∈ H, (C h i) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hG (fun _ _ _ => sq_nonneg _)
      _ ≤ (S i) ^ 2 * E :=
        localDifferenceCorrelation_plancherel X H (positiveInterval V) f hf (a i) L
          (hCover i hi) ω (S i) (hθ i)
      _ ≤ E * (V : ℝ) * S i := by
        have h := mul_le_mul_of_nonneg_right (hs i) (show 0 ≤ S i from norm_nonneg _)
        have h' := mul_le_mul_of_nonneg_left h hE
        simpa only [pow_two, mul_assoc, mul_left_comm, mul_comm] using h'
  have hcard : (0 : ℝ) < (G.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hGne
  have hProd : 0 ≤ (G.card : ℝ) * R := mul_nonneg hcard.le hR
  have hTail :=
    (pow_le_pow_left₀ hProd hLower 2).trans (hCS.trans
      (mul_le_mul_of_nonneg_left hUpper (by positivity)))
  change (G.card : ℝ) * R ^ 2 ≤ (A.card : ℝ) * E * V * ∑ i ∈ A, S i
  apply le_of_mul_le_mul_left _ hcard
  calc
    (G.card : ℝ) * ((G.card : ℝ) * R ^ 2) = ((G.card : ℝ) * R) ^ 2 := by ring
    _ ≤ ((G.card : ℝ) * (A.card : ℝ)) * (E * V * ∑ i ∈ A, S i) := hTail
    _ = _ := by ring

/-- Choose a unit scalar with the conjugate phase of a complex number, so
that multiplication makes the number equal to its nonnegative modulus. -/
theorem exists_phase_mul_eq_norm (z : ℂ) :
    ∃ γ : ℝ, z * phase γ = (‖z‖ : ℂ) := by
  refine ⟨-Complex.arg z / (2 * Real.pi), ?_⟩
  have h : z = (‖z‖ : ℂ) * Complex.exp ((z.arg : ℂ) * Complex.I) :=
    (Complex.norm_mul_exp_arg_mul_I z).symm
  have hγ : phase (-z.arg / (2 * Real.pi)) = Complex.exp (-((z.arg : ℂ) * Complex.I)) := by
    unfold phase
    push_cast
    congr 1
    field_simp [ne_of_gt Real.pi_pos]
    ring
  rw [hγ]
  calc
    z * Complex.exp (-((z.arg : ℂ) * Complex.I)) =
      (‖z‖ : ℂ) * Complex.exp ((z.arg : ℂ) * Complex.I) *
        Complex.exp (-((z.arg : ℂ) * Complex.I)) :=
      congrArg (· * Complex.exp (-((z.arg : ℂ) * Complex.I))) h
    _ = (‖z‖ : ℂ) := by rw [mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]

/-- Align the complex phase on each block and express its local correlation
as a real slope and intercept in the spatial variable. -/
theorem exists_local_phase_with_maximizing_correlation (f : ℤ → ℂ) (V : ℕ)
    (a L : ℤ) (hL : L ≠ 0) (θ : Circle) :
    ∃ b γ : ℝ,
      (∑ t ∈ positiveInterval V,
        f (a + L * t) * phase (b * ((a + L * t : ℤ) : ℝ) + γ)) =
      (‖localFourier f (positiveInterval V) a L θ‖ : ℂ) := by
  obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective θ
  obtain ⟨γ, hg⟩ := exists_phase_mul_eq_norm (localFourier f (positiveInterval V) a L (s : Circle))
  refine ⟨s / L, γ - (s / L) * a, ?_⟩
  have hLR : (L : ℝ) ≠ 0 := by exact_mod_cast hL
  have hArg (t : ℤ) : s / (L : ℝ) * ((a + L * t : ℤ) : ℝ) +
      (γ - s / (L : ℝ) * a) = s * t + γ := by
    push_cast
    field_simp
    ring
  have hChar (t : ℤ) : phase (s * t) = fourier t (s : Circle) := by
    rw [phase, fourier_coe_apply]
    push_cast
    congr 1
    ring
  calc
    _ = (∑ t ∈ positiveInterval V, f (a + L * t) * fourier t (s : Circle)) * phase γ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro t ht
      rw [hArg, phase_add, hChar, mul_assoc]
    _ = _ := hg


/-- The block and residue of an integer. Subtracting one aligns the block
with `[1,LV]` and labels its residues from zero. -/
def localBlockCoordinates (L V : ℕ) (x : ℤ) : ℤ × ℤ :=
  ((x - 1) / ((L : ℤ) * V), (x - 1) % (L : ℤ))

/-- The origin of the progression numbered by a block and a residue. -/
def localBlockOrigin (L V : ℕ) (p : ℤ × ℤ) : ℤ :=
  (L : ℤ) * V * p.1 + p.2 + 1 - L

/-- The occupied block/residue pairs. Their progressions are retained in
full, even at the ends of the support. -/
def occupiedLocalBlocks (X : Finset ℤ) (L V : ℕ) : Finset (ℤ × ℤ) :=
  X.image (localBlockCoordinates L V)

theorem localBlockCoordinates_of_parameter {L V : ℕ} (hL : 0 < L)
    (p : ℤ × ℤ) (hp : 0 ≤ p.2 ∧ p.2 < (L : ℤ)) {t : ℤ}
    (ht : t ∈ positiveInterval V) :
    localBlockCoordinates L V (localBlockOrigin L V p + (L : ℤ) * t) = p := by
  obtain ⟨j,r⟩ := p
  obtain ⟨ht₁,ht₂⟩ := Finset.mem_Icc.mp ht
  have hLz : (0 : ℤ) < L := by exact_mod_cast hL
  have hVz : (0 : ℤ) < V := by omega
  have hw : (0 : ℤ) < (L : ℤ) * V := mul_pos hLz hVz
  have hb₀ : 0 ≤ r + (L : ℤ) * (t - 1) := by
    nlinarith only [hp.1, mul_nonneg hLz.le (show 0 ≤ t - 1 by omega)]
  have hb₁ : r + (L : ℤ) * (t - 1) < (L : ℤ) * V := by
    have hmul := mul_le_mul_of_nonneg_left ht₂ hLz.le
    nlinarith only [hp.2, hmul]
  have he : localBlockOrigin L V (j,r) + (L : ℤ) * t - 1 =
      (r + (L : ℤ) * (t - 1)) + ((L : ℤ) * V) * j := by
    unfold localBlockOrigin
    simp only [Prod.fst, Prod.snd]
    ring
  unfold localBlockCoordinates
  rw [he]
  congr 1
  · rw [Int.add_mul_ediv_left _ _ hw.ne', Int.ediv_eq_zero_of_lt hb₀ hb₁, zero_add]
  · rw [show r + (L : ℤ) * (t - 1) + ((L : ℤ) * V) * j =
      r + (L : ℤ) * (t - 1 + (V : ℤ) * j) by ring,
      Int.add_mul_emod_self_left, Int.emod_eq_of_lt hp.1 hp.2]

theorem occupiedLocalBlocks_residue {X : Finset ℤ} {L V : ℕ} (hL : 0 < L)
    {p : ℤ × ℤ} (hp : p ∈ occupiedLocalBlocks X L V) :
    0 ≤ p.2 ∧ p.2 < (L : ℤ) := by
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
  have hLz : (0 : ℤ) < L := by exact_mod_cast hL
  exact ⟨Int.emod_nonneg _ hLz.ne', Int.emod_lt_of_pos _ hLz⟩

/-- Every integer is represented on exactly the progression located by its
block and residue, with parameter in `[1,V]`. -/
theorem exists_localBlock_parameter (x : ℤ) {L V : ℕ} (hL : 0 < L) (hV : 0 < V) :
    ∃ t ∈ positiveInterval V,
      localBlockOrigin L V (localBlockCoordinates L V x) + (L : ℤ) * t = x := by
  let w : ℤ := (L : ℤ) * V
  let n : ℤ := x - 1
  let j := n / w
  let r := n % w
  have hLz : (0 : ℤ) < L := by exact_mod_cast hL
  have hVz : (0 : ℤ) < V := by exact_mod_cast hV
  have hw : 0 < w := mul_pos hLz hVz
  have hr₀ : 0 ≤ r := Int.emod_nonneg n hw.ne'
  have hr₁ : r < w := Int.emod_lt_of_pos n hw
  have hdiv₀ : 0 ≤ r / (L : ℤ) := Int.ediv_nonneg hr₀ hLz.le
  have hdiv₁ : r / (L : ℤ) < (V : ℤ) := by
    apply (Int.ediv_lt_iff_lt_mul hLz).mpr
    exact mul_comm (L : ℤ) (V : ℤ) ▸ hr₁
  have hmod : r % (L : ℤ) = n % (L : ℤ) :=
    Int.emod_emod_of_dvd n (dvd_mul_right _ _)
  refine ⟨r / (L : ℤ) + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
  have he := Int.emod_add_ediv n w
  have hr := Int.emod_add_ediv r (L : ℤ)
  change r + w * j = n at he
  dsimp only [localBlockOrigin, localBlockCoordinates]
  change w * j + n % (L : ℤ) + 1 - ↑L + ↑L * (r / ↑L + 1) = x
  rw [← hmod]
  linarith [show n = x - 1 by rfl]

/-- Including complete boundary progressions costs at most two full spatial
blocks. This bound has exactly the factor `1 / V` required in Lemma 5.1. -/
theorem occupiedLocalBlocks_card_mul_le {X : Finset ℤ} {lo hi : ℤ} (hlo : lo ≤ hi)
    (hX : X ⊆ Finset.Icc lo hi) {L V : ℕ} (hL : 0 < L) (hV : 0 < V) :
    ((occupiedLocalBlocks X L V).card : ℤ) * (V : ℤ) ≤ hi - lo + 2 * ((L : ℤ) * V) := by
  let w : ℤ := (L : ℤ) * V
  let j₀ := (lo - 1) / w
  let j₁ := (hi - 1) / w
  have hLz : (0 : ℤ) < L := by exact_mod_cast hL
  have hVz : (0 : ℤ) < V := by exact_mod_cast hV
  have hw : 0 < w := mul_pos hLz hVz
  have hSub : occupiedLocalBlocks X L V ⊆ Finset.Icc j₀ j₁ ×ˢ Finset.Ico 0 (L : ℤ) := by
    intro p hp
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hx₀,hx₁⟩ := Finset.mem_Icc.mp (hX hx)
    refine Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨?_,?_⟩,
      Finset.mem_Ico.mpr ⟨Int.emod_nonneg _ hLz.ne', Int.emod_lt_of_pos _ hLz⟩⟩
    · exact Int.ediv_le_ediv hw (by omega)
    · exact Int.ediv_le_ediv hw (by omega)
  have hJ : j₀ ≤ j₁ := Int.ediv_le_ediv hw (by omega)
  have hJcard : ((Finset.Icc j₀ j₁).card : ℤ) = j₁ + 1 - j₀ := by
    rw [Int.card_Icc, Int.toNat_of_nonneg (by omega)]
  have hRcard : ((Finset.Ico 0 (L : ℤ)).card : ℤ) = (L : ℤ) := by simp [Int.card_Ico]
  have hN := Finset.card_le_card hSub
  have hZ : ((occupiedLocalBlocks X L V).card : ℤ) ≤ (j₁ + 1 - j₀) * (L : ℤ) := by
    rw [Finset.card_product] at hN
    have hZ' : ((occupiedLocalBlocks X L V).card : ℤ) ≤
        ((Finset.Icc j₀ j₁).card : ℤ) * ((Finset.Ico 0 (L : ℤ)).card : ℤ) := by
      exact_mod_cast hN
    rwa [hJcard,hRcard] at hZ'
  change ((occupiedLocalBlocks X L V).card : ℤ) * (V : ℤ) ≤ hi - lo + 2 * w
  refine (mul_le_mul_of_nonneg_right hZ hVz.le).trans ?_
  have hdecomp₀ := Int.emod_add_ediv (lo - 1) w
  have hdecomp₁ := Int.emod_add_ediv (hi - 1) w
  change (lo - 1) % w + w * j₀ = lo - 1 at hdecomp₀
  change (hi - 1) % w + w * j₁ = hi - 1 at hdecomp₁
  rw [mul_assoc ((j₁ + 1 - j₀) : ℤ)]
  change (j₁ + 1 - j₀) * w ≤ hi - lo + 2 * w
  nlinarith only [hdecomp₀, hdecomp₁, Int.emod_lt_of_pos (lo - 1) hw,
    Int.emod_nonneg (hi - 1) hw.ne']

/-- Finite spatial summation over the occupied block progressions, with
zero values permitted in the enlarged boundary progression. -/
theorem sum_occupiedLocalBlocks {X : Finset ℤ} (g : ℤ → ℂ) (hg : SupportedOn X g)
    {L V : ℕ} (hL : 0 < L) (hV : 0 < V) :
    (∑ x ∈ X, g x) = ∑ p ∈ occupiedLocalBlocks X L V, ∑ t ∈ positiveInterval V,
      g (localBlockOrigin L V p + (L : ℤ) * t) := by
  let A := occupiedLocalBlocks X L V
  let position := fun z : (ℤ × ℤ) × ℤ => localBlockOrigin L V z.1 + (L : ℤ) * z.2
  let U := (A ×ˢ positiveInterval V).image position
  have hSub : X ⊆ U := by
    intro x hx
    obtain ⟨t,ht,hxt⟩ := exists_localBlock_parameter x hL hV
    exact Finset.mem_image.mpr ⟨(localBlockCoordinates L V x,t),
      Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hx,ht⟩, hxt⟩
  have hInj : Set.InjOn position ↑(A ×ˢ positiveInterval V) := by
    intro p hp r hr he
    obtain ⟨hpA,hpt⟩ := Finset.mem_product.mp hp
    obtain ⟨hrA,hrt⟩ := Finset.mem_product.mp hr
    have hcoord₁ := localBlockCoordinates_of_parameter hL p.1 (occupiedLocalBlocks_residue hL hpA) hpt
    have hcoord₂ := localBlockCoordinates_of_parameter hL r.1 (occupiedLocalBlocks_residue hL hrA) hrt
    have hsame : p.1 = r.1 := hcoord₁.symm.trans ((congrArg (localBlockCoordinates L V) he).trans hcoord₂)
    apply Prod.ext hsame
    dsimp only [position] at he
    rw [hsame] at he
    have hLz : (L : ℤ) ≠ 0 := by exact_mod_cast hL.ne'
    exact mul_left_cancel₀ hLz (by linarith)
  trans ∑ x ∈ U, g x
  · exact Finset.sum_subset hSub (fun x _ hx => hg x hx)
  · dsimp only [U]
    rw [Finset.sum_image hInj, Finset.sum_product]


/-- A function given by a linear phase on each standard spatial
block and residue class. -/
noncomputable def localBlockPhase (L V : ℕ) (b γ : (ℤ × ℤ) → ℝ)
    (x : ℤ) : ℂ :=
  phase (b (localBlockCoordinates L V x) * (x : ℝ) + γ (localBlockCoordinates L V x))

theorem localBlockPhase_eq_on_window {L V : ℕ} (hL : 0 < L) (hV : 0 < V)
    (b γ : (ℤ × ℤ) → ℝ) (j r x : ℤ)
    (hx₁ : (j - 1) * ((L : ℤ) * V) < x) (hx₂ : x ≤ j * ((L : ℤ) * V))
    (hm : x ≡ r [ZMOD (L : ℤ)]) :
    localBlockPhase L V b γ x =
      phase (b (j - 1, (r - 1) % (L : ℤ)) * (x : ℝ) + γ (j - 1, (r - 1) % (L : ℤ))) := by
  have hLz : (0 : ℤ) < L := by exact_mod_cast hL
  have hVz : (0 : ℤ) < V := by exact_mod_cast hV
  have hw : 0 < (L : ℤ) * V := mul_pos hLz hVz
  have hDiv : (x - 1) / ((L : ℤ) * V) = j - 1 := by
    apply le_antisymm
    · have h := (Int.ediv_lt_iff_lt_mul hw).mpr (show x - 1 < j * ((L : ℤ) * V) by omega)
      omega
    · exact (Int.le_ediv_iff_mul_le hw).mpr (by omega)
  have he : (x - 1) % (L : ℤ) = (r - 1) % (L : ℤ) := hm.sub_right 1
  simp only [localBlockPhase, localBlockCoordinates, hDiv, he]

theorem norm_localBlockPhase (L V : ℕ) (b γ : (ℤ × ℤ) → ℝ) (x : ℤ) :
    ‖localBlockPhase L V b γ x‖ = 1 := by simp [localBlockPhase]

private theorem exists_shift_support {ι : Type*} (A : Finset ι)
    (X G T : Finset ℤ) (a : ι → ℤ) (L : ℤ) :
    ∃ H : Finset ℤ, G ⊆ H ∧ ∀ i ∈ A, ∀ y ∈ X, ∀ t ∈ T, y - (a i + L * t) ∈ H := by
  let Y := (A ×ˢ T).image (fun z : ι × ℤ => a z.1 + L * z.2)
  let F := (X ×ˢ Y).image (fun z : ℤ × ℤ => z.1 - z.2)
  refine ⟨G ∪ F, Finset.subset_union_left, ?_⟩
  intro i hi y hy t ht
  have hY : a i + L * t ∈ Y := by
    dsimp only [Y]
    exact Finset.mem_image.mpr ⟨(i,t), Finset.mem_product.mpr ⟨hi,ht⟩, rfl⟩
  apply Finset.mem_union_right
  dsimp only [F]
  exact Finset.mem_image.mpr ⟨(y, a i + L * t), Finset.mem_product.mpr ⟨hy,hY⟩, rfl⟩

set_option maxHeartbeats 1000000 in
/-- A common differentiated frequency yields a linear phase separately on
each fixed spatial progression. -/
theorem exists_localBlockPhase_of_fixed_frequency
    (X G : Finset ℤ) (hG : G.Nonempty) (f : ℤ → ℂ)
    (hf : SupportedOn X f) (hunit : ∀ x, ‖f x‖ ≤ 1)
    {L V : ℕ} (hL : 0 < L) (hV : 0 < V) (ω : Circle) (r : ℝ) (hr : 0 ≤ r)
    (hCorr : ∀ h ∈ G, r ≤ ∑ i ∈ occupiedLocalBlocks X L V,
      ‖localDifferenceCorrelation f (positiveInterval V) (localBlockOrigin L V i) (L : ℤ) ω h‖) :
    ∃ b γ : (ℤ × ℤ) → ℝ,
      (G.card : ℝ) * r^2 ≤ (X.card : ℝ) *
        ((occupiedLocalBlocks X L V).card : ℝ) * V *
        ‖∑ x ∈ X, f x * localBlockPhase L V b γ x‖ := by
  classical
  let A := occupiedLocalBlocks X L V
  let a := localBlockOrigin L V
  obtain ⟨H,hGH,hCover⟩ := exists_shift_support A X G (positiveInterval V) a (L : ℤ)
  obtain ⟨θ,hθ,hM⟩ := exists_localFourier_mass_of_common_frequency A X H G
    hGH hG f hf a (L : ℤ) V hCover hunit ω r hr hCorr
  choose b γ hAlign using fun i => exists_local_phase_with_maximizing_correlation f V
    (a i) (L : ℤ) (by exact_mod_cast hL.ne') (θ i)
  refine ⟨b,γ,?_⟩
  have hEnergy : (∑ x ∈ X, ‖f x‖ ^ 2) ≤ (X.card : ℝ) := by
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using
      Finset.sum_le_sum (s := X) (g := fun _ => (1 : ℝ))
        (fun x _ => by simpa using pow_le_pow_left₀ (norm_nonneg (f x)) (hunit x) 2)
  let S := ∑ i ∈ A, ‖localFourier f (positiveInterval V) (a i) (L : ℤ) (θ i)‖
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hSum : (∑ x ∈ X, f x * localBlockPhase L V b γ x) = (S : ℂ) := by
    have hSpt : SupportedOn X (fun x => f x * localBlockPhase L V b γ x) := by
      intro x hx
      simp [hf _ hx]
    rw [sum_occupiedLocalBlocks _ hSpt hL hV]
    push_cast [S]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← hAlign i]
    apply Finset.sum_congr rfl
    intro t ht
    simp only [localBlockPhase, a,
      localBlockCoordinates_of_parameter hL i (occupiedLocalBlocks_residue hL hi) ht]
  have hNorm : ‖∑ x ∈ X, f x * localBlockPhase L V b γ x‖ = S := by
    simp [hSum, abs_of_nonneg hS]
  rw [hNorm]
  calc
    _ ≤ (A.card : ℝ) * (∑ x ∈ X, ‖f x‖^2) * V * S := hM
    _ ≤ _ := by
      change _ ≤ (X.card : ℝ) * (A.card : ℝ) * V * S
      rw [mul_comm (X.card : ℝ)]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hEnergy (Nat.cast_nonneg _))
          (Nat.cast_nonneg _)) hS

set_option maxHeartbeats 1000000 in
/-- The finite result of the modular Lipschitz inverse input in Lemma 5.1.
From a uniform lower correlation bound on a finite set of shifts, this
constructs a genuine blockwise linear phase. The theorem supplies the
entire finite proof after the unweighted inverse theorem, without any
asymptotic estimates the caller must absorb. -/
theorem exists_localBlockPhase_of_modular_correlations
    (X G : Finset ℤ) (hG : G.Nonempty) (f : ℤ → ℂ)
    (hf : SupportedOn X f) (hunit : ∀ x, ‖f x‖ ≤ 1)
    {L V Q : ℕ} (hL : 0 < L) (hV : 0 < V) (hQ : 0 < Q)
    (D R : ℝ) (hD : 0 ≤ D) (hR : 0 ≤ R)
    (hError : ((occupiedLocalBlocks X L V).card : ℝ) * V * (D * (V : ℝ)) ≤ R / 2)
    (hCorr : ∀ h ∈ G, ∃ (q : ℕ), 0 < q ∧ q ≤ Q ∧
      ∃ φ : ℤ → ℂ, (∀ x, ‖φ x‖ ≤ 1) ∧
        (∀ x t : ℤ, ‖φ (x + (q : ℤ) * (L : ℤ) * t) - φ x‖ ≤ D * |(t : ℝ)|) ∧
        R ≤ ‖∑ x ∈ X, spatialMultiplicativeDifference f h x * φ x‖) :
    ∃ b γ : (ℤ × ℤ) → ℝ,
      (G.card : ℝ) * R ^ 2 ≤ 4 * (Q : ℝ) ^ 4 * (X.card : ℝ) *
        ((occupiedLocalBlocks X L V).card : ℝ) * V *
        ‖∑ x ∈ X, f x * localBlockPhase L V b γ x‖ := by
  classical
  let A := occupiedLocalBlocks X L V
  let a := localBlockOrigin L V
  let c := fun h ω => ∑ i ∈ A, ‖localDifferenceCorrelation f (positiveInterval V) (a i) (L : ℤ) ω h‖
  let r := R / (2 * (Q : ℝ))
  have hQReal : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hr : 0 ≤ r := div_nonneg hR (by positivity)
  have hOne : ∀ h ∈ G, ∃ ω ∈ boundedRationalFrequencies Q, r ≤ c h ω := by
    intro h hh
    obtain ⟨q,hq,hqQ,φ,hφ,hLip,hF⟩ := hCorr h hh
    have hSupport : SupportedOn X (fun x => spatialMultiplicativeDifference f h x * φ x) := by
      intro x hx
      simp [spatialMultiplicativeDifference, hf _ hx]
    rw [sum_occupiedLocalBlocks _ hSupport hL hV] at hF
    obtain ⟨m,hm⟩ := exists_rational_frequency_of_periodic_blocks A a (L : ℤ) V q hq f φ h hunit hφ
      D R hD hLip hF
    refine ⟨rationalCircleFrequency m, rationalCircleFrequency_mem_bounded Q q hq hqQ m, ?_⟩
    refine le_trans ?_ hm
    have hqReal : (0 : ℝ) < q := by exact_mod_cast hq
    have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hqQReal : (q : ℝ) ≤ Q := by exact_mod_cast hqQ
    have hError' : (A.card : ℝ) * V * (D * ((V : ℝ) / q)) ≤ R / 2 := by
      refine le_trans ?_ hError
      gcongr
      exact div_le_self (Nat.cast_nonneg _) hqOne
    apply (le_div_iff₀ hqReal).mpr
    have hmultiply : r * (q : ℝ) ≤ R / 2 := by
      calc
        r * (q : ℝ) ≤ r * Q := mul_le_mul_of_nonneg_left hqQReal hr
        _ = R / 2 := by
          dsimp [r]
          field_simp
          ring
    linarith
  obtain ⟨ω, -, G', hG'sub, hCorr', hCard⟩ :=
    exists_common_frequency G (boundedRationalFrequencies Q) hG (fun h ω => r ≤ c h ω) hOne
  have hG' : G'.Nonempty := by
    by_cases hn : G' = ∅
    · simp only [hn, Finset.card_empty, mul_zero] at hCard
      exact (not_le_of_gt (Finset.card_pos.mpr hG) hCard).elim
    · exact Finset.nonempty_iff_ne_empty.mpr hn
  obtain ⟨b,γ,hMass⟩ := exists_localBlockPhase_of_fixed_frequency X G' hG' f hf hunit
    hL hV ω r hr hCorr'
  refine ⟨b,γ,?_⟩
  let S := ‖∑ x ∈ X, f x * localBlockPhase L V b γ x‖
  have hCard' : (G.card : ℝ) ≤ (Q : ℝ)^2 * (G'.card : ℝ) := by
    have hN : G.card ≤ Q^2 * G'.card :=
      hCard.trans (Nat.mul_le_mul_right _ (card_boundedRationalFrequencies_le Q))
    exact_mod_cast hN
  have hScale : (G.card : ℝ) * r^2 ≤ (Q : ℝ)^2 * ((A.card : ℝ) * (X.card : ℝ) * V * S) := by
    calc
      _ ≤ ((Q : ℝ)^2 * (G'.card : ℝ)) * r^2 := mul_le_mul_of_nonneg_right hCard' (sq_nonneg _)
      _ = (Q : ℝ)^2 * ((G'.card : ℝ) * r^2) := by ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        exact hMass.trans_eq (by ring)
  have hFinal := mul_le_mul_of_nonneg_left hScale (show 0 ≤ 4 * (Q : ℝ)^2 by positivity)
  change (G.card : ℝ) * R ^ 2 ≤
    4 * (Q : ℝ) ^ 4 * (X.card : ℝ) * (A.card : ℝ) * V * S
  calc
    _ = 4 * (Q : ℝ)^2 * ((G.card : ℝ) * r^2) := by
      dsimp [r]
      field_simp
      ring
    _ ≤ _ := hFinal.trans_eq (by ring)


/-- Raising the spatial step from (q^b) to (q^B) multiplies the
modular Lipschitz constant by (q^{B-b}). -/
theorem promote_modular_lipschitz (φ : ℤ → ℂ) {q q' b B : ℕ} (hb : b ≤ B) (A : ℝ)
    (hφ : ∀ x t : ℤ,
      ‖φ (x + (q' : ℤ) * (q : ℤ) ^ b * t) - φ x‖ ≤ A * |(t : ℝ)|) :
    ∀ x t : ℤ, ‖φ (x + (q' : ℤ) * ((q ^ B : ℕ) : ℤ) * t) - φ x‖ ≤
      (A * (q : ℝ) ^ (B - b)) * |(t : ℝ)| := by
  intro x t
  have hB : b + (B - b) = B := Nat.add_sub_of_le hb
  have hp : (q : ℤ)^B = (q : ℤ)^b * (q : ℤ)^(B - b) := by
    rw [← pow_add, hB]
  rw [Nat.cast_pow, hp, ← mul_assoc (q' : ℤ), mul_assoc ((q' : ℤ) * ((q : ℤ) ^ b))]
  simpa only [Int.cast_mul, Int.cast_pow, Int.cast_natCast, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ (q : ℝ) ^ (B - b)), mul_assoc] using
    hφ x ((q : ℤ) ^ (B - b) * t)

theorem occupiedLocalBlocks_spatial_card_mul_le (C : ℝ) (N L V : ℕ)
    (hC : 0 ≤ C) (hL : 0 < L) (hV : 0 < V) (hLV : L * V ≤ N) :
    ((occupiedLocalBlocks (spatialInterval C N) L V).card : ℝ) * (V : ℝ) ≤
      (2 * C + 2) * (N : ℝ) := by
  let lo : ℤ := ⌈-C * (N : ℝ)⌉
  let hi : ℤ := ⌊ C * (N : ℝ)⌋
  have hlo : lo ≤ 0 := Int.ceil_le.mpr (by
    simp only [Int.cast_zero]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hC) (Nat.cast_nonneg _))
  have hhi : 0 ≤ hi := Int.le_floor.mpr (by
    simp only [Int.cast_zero]
    exact mul_nonneg hC (Nat.cast_nonneg _))
  have hc := occupiedLocalBlocks_card_mul_le (hlo.trans hhi)
    (show spatialInterval C N ⊆ Finset.Icc lo hi by rfl) hL hV
  have hcR : ((occupiedLocalBlocks (spatialInterval C N) L V).card : ℝ) * (V : ℝ) ≤
      (hi : ℝ) - (lo : ℝ) + 2 * ((L : ℝ) * (V : ℝ)) := by exact_mod_cast hc
  have hlow := Int.le_ceil (-C * (N : ℝ))
  have hhigh := Int.floor_le (C * (N : ℝ))
  have hw : (L : ℝ) * (V : ℝ) ≤ (N : ℝ) := by exact_mod_cast hLV
  exact hcR.trans (by linarith)

theorem spatialInterval_real_card_le (C : ℝ) (N : ℕ) (hC : 0 ≤ C) (hN : 0 < N) :
    ((spatialInterval C N).card : ℝ) ≤ (2 * C + 1) * (N : ℝ) := by
  let lo : ℤ := ⌈-C * (N : ℝ)⌉
  let hi : ℤ := ⌊ C * (N : ℝ)⌋
  have hlo : lo ≤ 0 := Int.ceil_le.mpr (by
    simp only [Int.cast_zero]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hC) (Nat.cast_nonneg _))
  have hhi : 0 ≤ hi := Int.le_floor.mpr (by
    simp only [Int.cast_zero]
    exact mul_nonneg hC (Nat.cast_nonneg _))
  have hCrd : ((spatialInterval C N).card : ℤ) = hi + 1 - lo := by
    change ((Finset.Icc lo hi).card : ℤ) = hi + 1 - lo
    rw [Int.card_Icc, Int.toNat_of_nonneg (by omega)]
  have hCrdR : ((spatialInterval C N).card : ℝ) = (hi : ℝ) + 1 - (lo : ℝ) := by exact_mod_cast hCrd
  have hlow := Int.le_ceil (-C * (N : ℝ))
  have hhigh := Int.floor_le (C * (N : ℝ))
  have hN' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  linarith

end NilBohr
