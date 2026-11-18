import NilBohr.PhaseReplacement

/-! Residue-class splitting after the spatial linear phases have been selected. -/

open scoped BigOperators
open Polynomial

namespace NilBohr

theorem conj_phase (x : ℝ) : (starRingEnd ℂ) (phase x) = phase (-x) := by
  unfold phase
  rw [← Complex.exp_conj]
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
  congr 1
  ring

private theorem residue_fiber_eq_progression (l r : ℤ) (L : ℕ) (a : ℤ)
    (ha : a ∈ (Finset.Icc l r).image (fun y => y % (L : ℤ))) :
    ((Finset.Icc l r).filter (fun y => y % (L : ℤ) = a)) = localProgression l r a L := by
  classical
  obtain ⟨y,_,hy⟩ := Finset.mem_image.mp ha
  have ha' : a % (L : ℤ) = a := by rw [← hy, Int.emod_emod]
  ext x
  simp [localProgression, Int.ModEq, ha']

/-- On a retained parameter interval the shifted phases stay in fixed spatial
blocks. Splitting into parameter residues gives the weighted convex bound
in the proof of the local generalized von Neumann theorem. -/
theorem norm_shifted_phase_sum_le_by_progressions {k : ℕ}
    (P : Fin k → Polynomial ℤ) (d L : ℕ) (hL : 0 < L)
    (hdeg : ∀ i, (P i).natDegree ≤ d)
    (U : Finset ℤ) (x l r : ℤ) (v : ℤ → ℂ)
    (V : Fin k → ℕ) (hV : ∀ i, 0 < V i)
    (b γ : Fin k → (ℤ × ℤ) → ℝ) (j : Fin k → ℤ)
    (hBlock : ∀ y ∈ Finset.Icc l r, ∀ i,
      (j i-1) * ((L : ℤ) * V i) < x + (P i).eval y ∧
      x + (P i).eval y ≤ j i * ((L : ℤ) * V i) ∧ x + (P i).eval y ∈ U)
    (E : ℝ)
    (hTest : ∀ a : ℤ, (localProgression l r a L).Nonempty →
      phaseNorm (d+1) (localProgression l r a L) v ≤ E) :
    ‖∑ y ∈ Finset.Icc l r, v y *
      ∏ i, supportedBlockPhase U L (V i) (b i) (γ i) (x + (P i).eval y)‖ ≤
      ((Finset.Icc l r).card : ℝ) * E := by
  let I := Finset.Icc l r
  let R := I.image (fun y => y % (L : ℤ))
  let f := fun y => v y *
    ∏ i, supportedBlockPhase U L (V i) (b i) (γ i) (x + (P i).eval y)
  let fiber := fun a => I.filter (fun y => y % (L : ℤ) = a)
  have hSplit : (∑ y ∈ I, f y) = ∑ a ∈ R, ∑ y ∈ fiber a, f y :=
    (Finset.sum_fiberwise_of_maps_to
      (fun y hy => Finset.mem_image_of_mem (fun y => y % (L : ℤ)) hy) f).symm
  have hCard : I.card = ∑ a ∈ R, (fiber a).card := by
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using
      (Finset.sum_fiberwise_of_maps_to
        (fun y hy => Finset.mem_image_of_mem (fun y => y % (L : ℤ)) hy)
        (fun _ => (1 : ℕ))).symm
  change ‖∑ y ∈ I, f y‖ ≤ (I.card : ℝ) * E
  rw [hSplit,hCard,Nat.cast_sum,Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
  intro a ha
  have hQ : fiber a = localProgression l r a L := residue_fiber_eq_progression l r L a ha
  have ha' : (localProgression l r a L).Nonempty := by
    rw [← hQ]
    obtain ⟨y,hy,he⟩ := Finset.mem_image.mp ha
    exact ⟨y,Finset.mem_filter.mpr ⟨hy,he⟩⟩
  let z := fun i : Fin k => x + (P i).eval a
  let key := fun i : Fin k => (j i - 1,(z i - 1) % (L : ℤ))
  have hv : ∀ y ∈ localProgression l r a L, ∀ i,
      supportedBlockPhase U L (V i) (b i) (γ i) (x + (P i).eval y) =
        phase ((-b i (key i)) * ((x + (P i).eval y : ℤ) : ℝ) + (-γ i (key i))) := by
    intro y hy i
    obtain ⟨hyI,hyC⟩ := Finset.mem_filter.mp hy
    obtain ⟨hlo,hhi,hUy⟩ := hBlock y hyI i
    have hmod : x + (P i).eval y ≡ z i [ZMOD (L : ℤ)] :=
      (Int.ModEq.refl x).add (eval_modEq (P i) _ y a hyC)
    rw [supportedBlockPhase, if_pos hUy,
      localBlockPhase_eq_on_window hL (hV i) (b i) (γ i) (j i) (z i)
        (x + (P i).eval y) hlo hhi hmod, conj_phase]
    simp [key, neg_add, neg_mul, add_comm]
  have hN : (0 : ℝ) < (localProgression l r a L).card :=
    Nat.cast_pos.mpr (Finset.card_pos.mpr ha')
  have hb := (norm_local_phase_product_average_le P d hdeg x (localProgression l r a L) v
    (fun i => supportedBlockPhase U L (V i) (b i) (γ i))
    (fun i => -b i (key i)) (fun i => -γ i (key i)) hv).trans (hTest a ha')
  rw [norm_div, Complex.norm_natCast] at hb
  rw [hQ]
  simpa [f,mul_comm] using (div_le_iff₀ hN).mp hb

/-- The retained part of the count is bounded by the largest local phase
test, multiplied by the spatial-cardinality factor. Each interval is
counted with its actual length. -/
theorem norm_retained_count_le {ι : Type*} {N M k : ℕ} (hN : 0 < N) (hM : 0 < M)
    (S : Finset ι) (X U : Finset ℤ) (good : ι → Finset ℤ)
    (low high : ι → ℤ) (P : Fin k → Polynomial ℤ)
    (d L : ℕ) (hL : 0 < L) (hdeg : ∀ i, (P i).natDegree ≤ d)
    (v f₀ : ℤ → ℂ) (V : Fin k → ℕ) (hV : ∀ i, 0 < V i)
    (b γ : Fin k → (ℤ × ℤ) → ℝ) (E : ℝ) (hE : 0 ≤ E)
    (hg : ∀ t ∈ S, good t ⊆ X) (hf : ∀ x ∈ X, ‖f₀ x‖ ≤ 1)
    (hlength : (∑ t ∈ S, (Finset.Icc (low t) (high t)).card) ≤ M)
    (hBlocks : ∀ t ∈ S, ∀ x ∈ good t, ∃ j : Fin k → ℤ,
      ∀ y ∈ Finset.Icc (low t) (high t), ∀ i,
        (j i-1) * ((L : ℤ) * V i) < x + (P i).eval y ∧
        x + (P i).eval y ≤ j i * ((L : ℤ) * V i) ∧ x + (P i).eval y ∈ U)
    (htest : ∀ t ∈ S, ∀ a, (localProgression (low t) (high t) a L).Nonempty →
      phaseNorm (d+1) (localProgression (low t) (high t) a L) v ≤ E) :
    ‖(∑ t ∈ S, ∑ x ∈ good t, f₀ x *
      (∑ y ∈ Finset.Icc (low t) (high t), v y *
        ∏ i, supportedBlockPhase U L (V i) (b i) (γ i) (x + (P i).eval y))) /
      ((N : ℂ) * (M : ℂ))‖ ≤ (X.card : ℝ) / N * E := by
  rw [norm_div,norm_mul,Complex.norm_natCast,Complex.norm_natCast]
  apply (div_le_iff₀ (by positivity)).mpr
  apply le_trans (norm_sum_le _ _)
  apply le_trans (Finset.sum_le_sum (fun t _ => norm_sum_le _ _))
  have hEach (t : ι) (ht : t ∈ S) (x : ℤ) (hx : x ∈ good t) :
      ‖f₀ x * (∑ y ∈ Finset.Icc (low t) (high t), v y *
        ∏ i, supportedBlockPhase U L (V i) (b i) (γ i) (x + (P i).eval y))‖ ≤
      ((Finset.Icc (low t) (high t)).card : ℝ) * E := by
    obtain ⟨j,hj⟩ := hBlocks t ht x hx
    rw [norm_mul]
    have h := norm_shifted_phase_sum_le_by_progressions P d L hL hdeg U x (low t) (high t)
      v V hV b γ j hj E (htest t ht)
    simpa only [one_mul] using mul_le_mul (hf x (hg t ht hx)) h (norm_nonneg _) zero_le_one
  calc
    _ ≤ ∑ t ∈ S, ∑ _x ∈ good t, ((Finset.Icc (low t) (high t)).card : ℝ) * E :=
      Finset.sum_le_sum (fun t ht => Finset.sum_le_sum (fun x hx => hEach t ht x hx))
    _ ≤ ∑ t ∈ S, (X.card : ℝ) * (((Finset.Icc (low t) (high t)).card : ℝ) * E) := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      exact Finset.sum_le_sum (fun t ht => mul_le_mul_of_nonneg_right
        (Nat.cast_le.mpr (Finset.card_le_card (hg t ht))) (by positivity))
    _ = (X.card : ℝ) * (∑ t ∈ S, ((Finset.Icc (low t) (high t)).card : ℝ)) * E := by
      simp_rw [← mul_assoc, ← Finset.sum_mul, Finset.mul_sum]
    _ ≤ (X.card : ℝ) * M * E :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by exact_mod_cast hlength)
        (Nat.cast_nonneg _)) hE
    _ = (X.card : ℝ) / N * E * ((N : ℝ) * M) := by field_simp; ring

end NilBohr
