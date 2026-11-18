import NilBohr.SpatialInverseInput
import NilBohr.External

/-! Application of the quoted unweighted inverse theorem after spatial
differencing. This produces the almost periodic functions in Lemma 5.1. -/

open scoped BigOperators
open Polynomial

namespace NilBohr

theorem card_spatialInterval_bounds {C : ℝ} {N : ℕ} (hC : 1 ≤ C) (hN : 0 < N) :
    N ≤ (spatialInterval C N).card ∧
      ((spatialInterval C N).card : ℝ) ≤ 3 * C * N := by
  let l := ⌈-C * (N : ℝ)⌉
  let u := ⌊C * (N : ℝ)⌋
  have hCN : (N : ℝ) ≤ C * N := by simpa using (mul_le_mul_of_nonneg_right hC
    (Nat.cast_nonneg N))
  have hl : l ≤ 1 := Int.ceil_le.mpr (by push_cast; linarith)
  have hu : (N : ℤ) ≤ u := Int.le_floor.mpr (by simpa using hCN)
  have hS : positiveInterval N ⊆ spatialInterval C N := by
    intro x hx
    obtain ⟨h₁,h₂⟩ := Finset.mem_Icc.mp hx
    exact Finset.mem_Icc.mpr ⟨hl.trans h₁,h₂.trans hu⟩
  refine ⟨?_, ?_⟩
  · have h := Finset.card_le_card hS
    have hc : (positiveInterval N).card = N := by simp [positiveInterval, Int.card_Icc]
    simpa only [hc] using h
  · change ((Finset.Icc l u).card : ℝ) ≤ 3 * C * N
    have hpos : 0 ≤ u + 1 - l := by omega
    rw [Int.card_Icc]
    have he : (((u + 1 - l).toNat : ℕ) : ℤ) = u + 1 - l := Int.toNat_of_nonneg hpos
    have heR : (((u + 1 - l).toNat : ℕ) : ℝ) = (u : ℝ) + 1 - l := by exact_mod_cast he
    have hupper : (u : ℝ) ≤ C * N := Int.floor_le _
    have hlower : -C * (N : ℝ) ≤ l := Int.le_ceil _
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    rw [heR]
    linarith

theorem card_spatialDifferences_le {C : ℝ} {N : ℕ} (hC : 1 ≤ C) (hN : 0 < N) :
    ((spatialDifferenceSupport (spatialInterval C N)).card : ℝ) ≤ 6 * C * N := by
  let l := ⌈-C * (N : ℝ)⌉
  let u := ⌊C * (N : ℝ)⌋
  have hCN : (N : ℝ) ≤ C * N := by simpa using (mul_le_mul_of_nonneg_right hC
    (Nat.cast_nonneg N))
  have hl : l ≤ 1 := Int.ceil_le.mpr (by push_cast; linarith)
  have hu : (N : ℤ) ≤ u := Int.le_floor.mpr (by simpa using hCN)
  have hsub : spatialDifferenceSupport (spatialInterval C N) ⊆ Finset.Icc (l-u) (u-l) := by
    intro x hx
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨h₁,h₂⟩ := Finset.mem_product.mp hp
    obtain ⟨h₁,h₁'⟩ := Finset.mem_Icc.mp h₁
    obtain ⟨h₂,h₂'⟩ := Finset.mem_Icc.mp h₂
    change l ≤ p.1 at h₁; change p.1 ≤ u at h₁'
    change l ≤ p.2 at h₂; change p.2 ≤ u at h₂'
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  refine (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans ?_
  have hpos : 0 ≤ u - l + 1 - (l-u) := by omega
  rw [Int.card_Icc]
  have he : (((u - l + 1 - (l-u)).toNat : ℕ) : ℤ) = u - l + 1 - (l-u) := Int.toNat_of_nonneg hpos
  have heR : (((u - l + 1 - (l-u)).toNat : ℕ) : ℝ) = (u : ℝ) - l + 1 - (l-u : ℤ) := by
    exact_mod_cast he
  have hupper : (u : ℝ) ≤ C * N := Int.floor_le _
  have hlower : -C * (N : ℝ) ≤ l := Int.le_ceil _
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rw [heR]
  push_cast
  linarith

theorem spatialInterval_translate_to_positive {C : ℝ} {N : ℕ} (hC : 1 ≤ C) (hN : 0 < N) :
    (spatialInterval C N).image (fun x => x - (⌈-C * (N : ℝ)⌉ - 1)) =
      positiveInterval (spatialInterval C N).card := by
  let l := ⌈-C * (N : ℝ)⌉
  let u := ⌊C * (N : ℝ)⌋
  have hCN : (N : ℝ) ≤ C * N := by simpa using (mul_le_mul_of_nonneg_right hC
    (Nat.cast_nonneg N))
  have hl : l ≤ 1 := Int.ceil_le.mpr (by push_cast; linarith)
  have hu : (N : ℤ) ≤ u := Int.le_floor.mpr (by simpa using hCN)
  change (Finset.Icc l u).image (fun x => x - (l-1)) = positiveInterval (Finset.Icc l u).card
  rw [Int.card_Icc]
  ext z
  simp only [Finset.mem_image, Finset.mem_Icc, positiveInterval, Int.toNat_of_nonneg
    (show 0 ≤ u+1-l by omega)]
  constructor
  · rintro ⟨x, ⟨hx, hxu⟩, rfl⟩
    omega
  · intro hz
    exact ⟨z+l-1, ⟨by omega, by omega⟩, by omega⟩

theorem parameterLength_mono_space {N N' q d : ℕ} (hN : N ≤ N') :
    parameterLength N q d ≤ parameterLength N' q d := by
  unfold parameterLength
  apply Nat.floor_mono
  apply Real.rpow_le_rpow (by positivity) _ (by positivity)
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hN) (by positivity)

theorem norm_countingForm_change_normalization {k : ℕ} {N N' M : ℕ}
    (hN : 0 < N) (hN' : 0 < N') (hM : 0 < M)
    (X : Finset ℤ) (P : Fin k → Polynomial ℤ) (v : ℤ → ℂ)
    (f : Fin k → ℤ → ℂ) :
    ‖countingForm N' M X P v f‖ = (N : ℝ) / N' * ‖countingForm N M X P v f‖ := by
  simp only [countingForm, norm_div, norm_mul, Complex.norm_natCast]
  field_simp
  ring

/-- Correlations along many spatial differences, at a fixed common bound
on the exponent of the base modulus. The small-scale alternative is
in the parameter length. -/
def DifferenceWitnessEstimate (C : ℝ) (d ℓ b₀ : ℕ) (a A b B : ℝ) : Prop :=
  ∀ (N M q : ℕ), 0 < N → 0 < q → 0 < M → M ≤ parameterLength N q d →
    ∀ P : Fin (ℓ + 1) → Polynomial ℤ, FixedPolynomialFamily P →
    (P (Fin.last ℓ)).natDegree = d →
    (∀ i, i ≠ 0 → HasCoefficients C q (P i)) →
    ∀ (v : ℤ → ℂ) (f : Fin (ℓ + 1) → ℤ → ℂ),
    OneBoundedOn (positiveInterval M) v →
    (∀ i, OneBoundedOn (spatialInterval C N) (f i)) →
    (∀ i, SupportedOn (spatialInterval C N) (f i)) →
    ∀ δ : ℝ, 0 < δ → δ < 1/2 →
    δ ≤ ‖countingForm N M (spatialInterval C N) P v f‖ →
    let ρ := δ^2 / (2*(6*C)^2)
    (M : ℝ) ≤ A*((q : ℝ)/ρ)^B ∨
    ∃ Y : Finset ℤ, Y ⊆ spatialDifferenceSupport (spatialInterval C N) ∧
      δ^2 * N / (2*(6*C)) ≤ (Y.card : ℝ) ∧
      ∀ h ∈ Y, ∃ (q' b' : ℕ),
        0 < q' ∧ 1 ≤ b' ∧ b' ≤ b₀ ∧ (q' : ℝ) ≤ A * ρ^(-B) ∧
        ∀ i, i ≠ 0 → ∃ φ : ℤ → ℂ, (∀ x, ‖φ x‖ ≤ 1) ∧
          a * ρ^b * N ≤ ‖∑ x ∈ spatialInterval C N,
            spatialMultiplicativeDifference (f i) h x * φ x‖ ∧
          ∀ x t : ℤ, ‖φ (x + (q' : ℤ) * (q : ℤ)^b' * t) - φ x‖ ≤
            A * ((q : ℝ) / ρ)^B * (M : ℝ) ^ (-((P i).natDegree : ℝ)) * |(t : ℝ)|

/-- Obtain spatial difference correlations without changing the bound on
the modulus exponent supplied by the unweighted KMTT inverse theorem. -/
theorem difference_witnesses_of_inverse_with_exponent {C : ℝ} (hC : 1 ≤ C)
    {d ℓ b₀ : ℕ} (hInv : KMTTLocalInverseWithExponent C d ℓ b₀) :
    ∃ a A b B : ℝ, 0 < a ∧ 0 < A ∧ 0 < b ∧ 0 < B ∧
      DifferenceWitnessEstimate C d ℓ b₀ a A b B := by
  obtain ⟨a, A, b, B, ha, hA, hb, hB, hInv⟩ := hInv
  refine ⟨a, A, b, B, ha, hA, hb, hB, ?_⟩
  intro N M q hN hq hM hMscale P hP htop hcoeff v f hv hf hSupp δ hδ hδ' hLarge ρ
  classical
  let S := spatialInterval C N
  let K := 6*C
  have hK : 1 ≤ K := by dsimp [K]; linarith
  have hS₁ : N ≤ S.card := (card_spatialInterval_bounds hC hN).1
  have hS₂ : (S.card : ℝ) ≤ K*N := by
    have := (card_spatialInterval_bounds hC hN).2
    change (S.card : ℝ) ≤ K*N
    dsimp [K]
    linarith [mul_nonneg (show 0 ≤ C by linarith) (Nat.cast_nonneg N)]
  have hSpos : 0 < S.card := hN.trans_le hS₁
  have hFull : ∀ i x, ‖f i x‖ ≤ 1 := fun i => oneBounded_of_supported (hf i) (hSupp i)
  obtain ⟨Y,hYS,hY,hDiff⟩ := compare_large_weighted_to_differenced hN hM S P hP.2.1 f
    (hSupp 0) hFull v hv hδ (by linarith : 0 < K) (card_spatialDifferences_le hC hN) hS₂ hLarge
  by_cases hSmall : (M : ℝ) ≤ A*((q : ℝ)/ρ)^B
  · exact Or.inl hSmall
  refine Or.inr ⟨Y,hYS,hY,?_⟩
  intro h hh
  let shift := ⌈-C*(N : ℝ)⌉-1
  let g := fun i => spatialMultiplicativeDifference (f i) h
  let g' := fun i z => g i (z+shift)
  have hSimage : S.image (fun x => x-shift) = positiveInterval S.card :=
    spatialInterval_translate_to_positive hC hN
  have h_g' : ∀ i, OneBoundedOn (positiveInterval S.card) (g' i) := by
    intro i x _
    dsimp [g',g]
    rw [spatialMultiplicativeDifference, norm_mul, Complex.norm_conj]
    exact mul_le_one₀ (hFull i _) (norm_nonneg _) (hFull i _)
  have hS_g' : ∀ i, SupportedOn (positiveInterval S.card) (g' i) := by
    intro i z hz
    have hz' : z+shift ∉ S := by
      intro hz'
      exact hz (hSimage ▸ Finset.mem_image.mpr ⟨z+shift,hz',by omega⟩)
    simp [g', g, spatialMultiplicativeDifference, hSupp i _ hz']
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρ' : ρ < 1/2 := by
    change δ^2 / (2*K^2) < 1/2
    apply (div_lt_iff₀ (by positivity)).2
    have h₁ : δ^2 < 1 := by nlinarith
    have h₂ : (1 : ℝ) ≤ K^2 := by nlinarith
    linarith
  have hCount : ρ ≤ ‖countingForm S.card M (positiveInterval S.card) P (fun _ => 1) g'‖ := by
    rw [← hSimage, countingForm_translate_window S.card M S P (fun _ => 1) g shift,
      norm_countingForm_change_normalization hN hSpos hM]
    have hratio : (1 : ℝ)/K ≤ (N : ℝ)/S.card := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      simpa [mul_comm] using hS₂
    refine le_trans ?_ (mul_le_mul hratio (hDiff h hh) (by positivity) (by positivity))
    change δ^2 / (2*K^2) ≤ 1/K * (δ^2/(2*K))
    apply le_of_eq
    field_simp
    ring
  obtain ⟨q',b',hq',hb'₁,hb'₂,hq'B,hφ⟩ :=
    (hInv S.card M q hSpos hq hM (hMscale.trans (parameterLength_mono_space hS₁)) P hP htop
      hcoeff g' h_g' hS_g' ρ hρ hρ' hCount).resolve_left hSmall
  refine ⟨q',b',hq',hb'₁,hb'₂,hq'B,?_⟩
  intro i hi
  obtain ⟨φ,hφ₁,hφ₂,hφ₃⟩ := hφ i hi
  refine ⟨fun x => φ (x-shift), fun x => hφ₁ _, ?_, ?_⟩
  · have hEq : (∑ z ∈ positiveInterval S.card, g' i z * φ z) =
        ∑ x ∈ S, g i x * φ (x-shift) := by
      rw [← hSimage, Finset.sum_image (by intro x _ y _ he; omega)]
      simp [g']
    rw [hEq] at hφ₂
    exact (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hS₁) (by positivity)).trans hφ₂
  · intro x t
    simpa only [add_sub_assoc, sub_add_eq_add_sub] using hφ₃ (x-shift) t


/-- A large weighted count supplies the exact KMTT Lipschitz correlations
for many spatial differences, with the exponent selected by the KMTT
input. -/
theorem difference_witnesses_of_large_count (hInv : KMTTLocalInverse)
    {C : ℝ} (hC : 1 ≤ C) {d ℓ : ℕ} (hℓ : 0 < ℓ) :
    ∃ (a A b B : ℝ) (b₀ : ℕ), 0 < a ∧ 0 < A ∧ 0 < b ∧ 0 < B ∧
      DifferenceWitnessEstimate C d ℓ b₀ a A b B := by
  obtain ⟨a, A, b, B, b₀, ha, hA, hb, hB, hInv⟩ := hInv C d ℓ hC hℓ
  obtain ⟨a', A', b', B', ha', hA', hb', hB', hDiff⟩ :=
    difference_witnesses_of_inverse_with_exponent hC
      (show KMTTLocalInverseWithExponent C d ℓ b₀ from ⟨a, A, b, B, ha, hA, hb, hB, hInv⟩)
  exact ⟨a', A', b', B', b₀, ha', hA', hb', hB', hDiff⟩

end NilBohr
