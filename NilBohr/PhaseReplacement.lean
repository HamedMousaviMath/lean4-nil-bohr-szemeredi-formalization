import NilBohr.DualReplacement
import NilBohr.InverseFourier

/-! Replacing each shifted input by a blockwise phase through its dual. -/

open scoped BigOperators
open Polynomial

namespace NilBohr

noncomputable def supportedBlockPhase (U : Finset ℤ) (L V : ℕ)
    (b γ : (ℤ × ℤ) → ℝ) (x : ℤ) : ℂ :=
  if x ∈ U then (starRingEnd ℂ) (localBlockPhase L V b γ x) else 0

theorem norm_supportedBlockPhase_le (U : Finset ℤ) (L V : ℕ)
    (b γ : (ℤ × ℤ) → ℝ) (x : ℤ) :
    ‖supportedBlockPhase U L V b γ x‖ ≤ 1 := by
  unfold supportedBlockPhase
  split_ifs <;> simp [Complex.norm_conj, norm_localBlockPhase]

theorem supportedOn_supportedBlockPhase (U : Finset ℤ) (L V : ℕ)
    (b γ : (ℤ × ℤ) → ℝ) :
    SupportedOn U (supportedBlockPhase U L V b γ) := by
  intro x hx
  simp [supportedBlockPhase, hx]

theorem norm_countingForm_replace_supported_phase {k N M : ℕ}
    (X U : Finset ℤ) (P : Fin k → Polynomial ℤ) (v : ℤ → ℂ)
    (f : Fin k → ℤ → ℂ) (i : Fin k) (L V : ℕ) (b γ : (ℤ × ℤ) → ℝ)
    (hZ : ∀ x ∈ X, ∀ y ∈ positiveInterval M, x + (P i).eval y ∈ U) :
    ‖countingForm N M X P v (Function.update f i (supportedBlockPhase U L V b γ))‖ =
      ‖∑ z ∈ U, (starRingEnd ℂ) (countDual M X P v f i z) *
        localBlockPhase L V b γ z‖ / (N : ℝ) := by
  apply Eq.trans _ (norm_countingForm_replace_phase X U P v f i _ hZ)
  congr 1
  rw [countingForm_update_eq_dual X U P v f i _ hZ,
    countingForm_update_eq_dual X U P v f i _ hZ]
  congr 1
  exact Finset.sum_congr rfl (fun z hz => by simp [supportedBlockPhase, hz])

/-- For any specified sequence of lower bounds, use the inverse result on
the conjugate dual at each stage. The anchor input is kept unchanged, and
all profiles are defined globally before they are truncated.
The hypothesis `hInv` is the local inverse step at the stated finite scales. -/
theorem replace_shifted_inputs_by_phases {k N M : ℕ} (hN : 0 < N)
    (X U : Finset ℤ) (P : Fin (k + 1) → Polynomial ℤ) (v : ℤ → ℂ)
    (f : Fin (k + 1) → ℤ → ℂ) (L : ℕ)
    (hZ : ∀ i : Fin (k + 1), i ≠ 0 →
      ∀ x ∈ X, ∀ y ∈ positiveInterval M, x + (P i).eval y ∈ U)
    (hf : ∀ i z, ‖f i z‖ ≤ 1) (hfSupp : ∀ i, SupportedOn U (f i))
    (hv : OneBoundedOn (positiveInterval M) v) {K : ℝ} (hK : 0 < K)
    (hcard : (U.card : ℝ) ≤ K * N) (r : ℕ → ℝ) (hr : ∀ j, 0 ≤ r j)
    (h₀ : r 0 ≤ ‖countingForm N M X P v f‖) (lengthCondition : Fin (k + 1) → ℕ → Prop)
    (hInv : ∀ (j : ℕ), j < k → ∀ (g : Fin (k + 1) → ℤ → ℂ),
      g 0 = f 0 → (∀ i z, ‖g i z‖ ≤ 1) → (∀ i, SupportedOn U (g i)) →
        (r j)^2 / K ≤ ‖countingForm N M X P v g‖ →
      ∀ i, i ≠ 0 → ∃ (V : ℕ) (b γ : (ℤ × ℤ) → ℝ), lengthCondition i V ∧
        (r (j+1)) * (N : ℝ) ≤ ‖∑ z ∈ U, g i z * localBlockPhase L V b γ z‖) :
    ∃ g : Fin (k + 1) → ℤ → ℂ, g 0 = f 0 ∧
      (∀ i z, ‖g i z‖ ≤ 1) ∧ (∀ i, SupportedOn U (g i)) ∧
      r k ≤ ‖countingForm N M X P v g‖ ∧
      ∀ i, i ≠ 0 → ∃ (V : ℕ) (b γ : (ℤ × ℤ) → ℝ), lengthCondition i V ∧
        g i = supportedBlockPhase U L V b γ := by
  let E : Finset (Fin (k + 1)) := Finset.univ.erase 0
  have hEcard : E.card = k := by simp [E]
  have ih : ∀ G : Finset (Fin (k + 1)), G ⊆ E →
      ∃ g : Fin (k + 1) → ℤ → ℂ, g 0 = f 0 ∧
        (∀ i z, ‖g i z‖ ≤ 1) ∧ (∀ i, SupportedOn U (g i)) ∧
        r G.card ≤ ‖countingForm N M X P v g‖ ∧
        ∀ i ∈ G, ∃ (V : ℕ) (b γ : (ℤ × ℤ) → ℝ), lengthCondition i V ∧
          g i = supportedBlockPhase U L V b γ := by
    classical
    intro G
    induction G using Finset.induction_on with
    | empty => exact fun _ => ⟨f,rfl,hf,hfSupp,h₀,by simp⟩
    | insert i G hne IH =>
      intro hsub
      obtain ⟨g,hg₀,hg,hgs,hT,hG⟩ := IH ((Finset.subset_insert _ _).trans hsub)
      have hi : i ≠ 0 := (Finset.mem_erase.mp (hsub (Finset.mem_insert_self _ _))).1
      let D := countDual M X P v g i
      let F := Function.update g i (fun z => (starRingEnd ℂ) (D z))
      have hF₀ : F 0 = f 0 := by simp [F, Function.update_of_ne (Ne.symm hi),hg₀]
      have hF (j : Fin (k+1)) (z : ℤ) : ‖F j z‖ ≤ 1 := by
        by_cases he : j = i
        · subst j
          simpa [F,Complex.norm_conj] using norm_countDual_le_one M X P v g i hv hg z
        · simpa [F,Function.update_of_ne he] using hg j z
      have hFS (j : Fin (k+1)) : SupportedOn U (F j) := by
        intro z hz
        by_cases he : j = i
        · subst j
          simp [F,D,countDual_support M X U P v g i (hZ i hi) z hz]
        · simpa [F,Function.update_of_ne he] using hgs j z hz
      have hLow : (r G.card)^2 / K ≤ ‖countingForm N M X P v F‖ := by
        refine (div_le_div_of_nonneg_right (pow_le_pow_left₀ (hr _) hT 2) hK.le).trans ?_
        exact countingForm_update_conj_dual_lower hN X U P v g i (hZ i hi)
          (fun z _ => hg i z) hK hcard
      have hStage : G.card < k := by
        have h := Finset.card_le_card hsub
        rwa [Finset.card_insert_of_not_mem hne, hEcard, Nat.add_one_le_iff] at h
      obtain ⟨V,b,γ,hL,hR⟩ := hInv G.card hStage F hF₀ hF hFS hLow i hi
      let g' := Function.update g i (supportedBlockPhase U L V b γ)
      have hg'₀ : g' 0 = f 0 := by simp [g',Function.update_of_ne (Ne.symm hi),hg₀]
      have hg' (j : Fin (k+1)) (z : ℤ) : ‖g' j z‖ ≤ 1 := by
        by_cases he : j = i
        · subst j
          simpa [g'] using norm_supportedBlockPhase_le U L V b γ z
        · simpa [g',Function.update_of_ne he] using hg j z
      have hg'S (j : Fin (k+1)) : SupportedOn U (g' j) := by
        by_cases he : j = i
        · subst j
          simpa [g'] using supportedOn_supportedBlockPhase U L V b γ
        · simpa [g',Function.update_of_ne he] using hgs j
      have hg'T : r (insert i G).card ≤ ‖countingForm N M X P v g'‖ := by
        rw [Finset.card_insert_of_not_mem hne, show g' = _ from rfl,
          norm_countingForm_replace_supported_phase X U P v g i L V b γ (hZ i hi),
          le_div_iff₀ (by positivity)]
        simpa [F,D] using hR
      refine ⟨g',hg'₀,hg',hg'S,hg'T,?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with he | hj
      · subst j
        exact ⟨V,b,γ,hL,by simp [g']⟩
      · obtain ⟨W,b',γ',hL',hphase⟩ := hG j hj
        have he : j ≠ i := fun he => hne (he ▸ hj)
        exact ⟨W,b',γ',hL',by simpa [g',Function.update_of_ne he] using hphase⟩
  obtain ⟨g,hg₀,hg,hgs,hT,hG⟩ := ih E (fun _ h => h)
  refine ⟨g,hg₀,hg,hgs,by simpa only [hEcard] using hT,?_⟩
  exact fun i hi => hG i (Finset.mem_erase.mpr ⟨hi,Finset.mem_univ _⟩)

end NilBohr
