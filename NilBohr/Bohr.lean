import NilBohr.Definitions

/-! The finite torus partition in Corollary 1.1. -/

open Filter Polynomial

namespace NilBohr

/-- The distinct-degree density bound for unrestricted shifted-prime
configurations, in the form of KMTT [arXiv:2608.19525v1, Theorem 1.2].
Ordering the distinct shifts by degree and adjoining the zero anchor does not
change the configurations. The bound includes its implied constant. -/
def KMTTShiftedPrimeDensityBound : Prop :=
  ∀ {ℓ : ℕ} (P : Fin (ℓ + 1) → Polynomial ℤ), FixedPolynomialFamily P →
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A : Finset ℤ, A ⊆ positiveInterval N →
        ¬ ContainsConfiguration A P (fun _ => True) →
        (A.card : ℝ) ≤ C * ((N : ℝ) * (Real.log (N : ℝ)) ^ (-c))

noncomputable def circleBin (L : ℕ) (hL : 0 < L) (t : ℝ) : Fin L :=
  ⟨⌊(L : ℝ) * Int.fract t⌋₊, (Nat.floor_lt (mul_nonneg (Nat.cast_nonneg L)
    (Int.fract_nonneg t))).2 (by
      have h : (0 : ℝ) < L := by exact_mod_cast hL
      simpa only [mul_one] using mul_lt_mul_of_pos_left (Int.fract_lt_one t) h)⟩

theorem norm_circle_sub_lt_of_circleBin_eq {L : ℕ} (hL : 0 < L)
    {s t : ℝ} (h : circleBin L hL s = circleBin L hL t) :
    ‖((s - t : ℝ) : Circle)‖ < 1 / (L : ℝ) := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hs₀ := Nat.floor_le (mul_nonneg hL'.le (Int.fract_nonneg s))
  have ht₀ := Nat.floor_le (mul_nonneg hL'.le (Int.fract_nonneg t))
  have hs₁ := Nat.lt_floor_add_one ((L : ℝ) * Int.fract s)
  have ht₁ := Nat.lt_floor_add_one ((L : ℝ) * Int.fract t)
  have heq : ⌊(L : ℝ) * Int.fract s⌋₊ = ⌊(L : ℝ) * Int.fract t⌋₊ :=
    congrArg Fin.val h
  rw [heq] at hs₀ hs₁
  have hdiff : |Int.fract s - Int.fract t| < 1 / (L : ℝ) := by
    rw [abs_lt]
    constructor
    · have hb : Int.fract t - Int.fract s < 1 / (L : ℝ) := by
        apply (lt_div_iff₀ hL').2
        nlinarith only [hs₀, ht₁]
      linarith
    · apply (lt_div_iff₀ hL').2
      nlinarith only [ht₀, hs₁]
  calc
    ‖((s - t : ℝ) : Circle)‖ = ‖((Int.fract s - Int.fract t : ℝ) : Circle)‖ := by
      simp only [AddCircle.coe_sub, AddCircle.coe_fract]
    _ ≤ |Int.fract s - Int.fract t| := by
      rw [← Real.norm_eq_abs]
      exact QuotientAddGroup.norm_mk_le_norm
    _ < 1 / (L : ℝ) := hdiff

theorem exists_circle_bin_width {ε : ℝ} (hε : 0 < ε) :
    ∃ L : ℕ, 0 < L ∧ 1 / (L : ℝ) < ε := by
  obtain ⟨L, hLε⟩ := exists_nat_gt (ε⁻¹)
  have hLreal : (0 : ℝ) < L := (inv_pos.mpr hε).trans hLε
  refine ⟨L, by exact_mod_cast hLreal, (div_lt_iff₀ hLreal).2 ?_⟩
  have hp : (1 : ℝ) < (L : ℝ) * ε := by
    apply (div_lt_iff₀ hε).1
    simpa only [one_div] using hLε
  simpa only [mul_comm ε] using hp

private theorem eventually_log_power_exceeds (K : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → K < (Real.log (N : ℝ)) ^ κ := by
  have hlim : Tendsto (fun N : ℕ => (Real.log (N : ℝ)) ^ κ) atTop atTop :=
    (tendsto_rpow_atTop hκ).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (hlim.eventually_ge_atTop (K + 1))
  exact ⟨N₀, fun N hN => (by linarith [hN₀ N hN])⟩

theorem finite_coloring_forces_configuration {ℓ : ℕ}
    (P : Fin (ℓ + 1) → Polynomial ℤ) (selector : ℕ → Prop)
    (hsmall : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A : Finset ℤ, A ⊆ positiveInterval N →
        ¬ ContainsConfiguration A P selector →
        (A.card : ℝ) ≤ C * ((N : ℝ) * (Real.log (N : ℝ)) ^ (-c)))
    {Colors : Type} [Fintype Colors] [DecidableEq Colors] (color : ℤ → Colors) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A : Finset ℤ, A ⊆ positiveInterval N →
        (N : ℝ) * (Real.log (N : ℝ)) ^ (-κ) ≤ (A.card : ℝ) →
        ∃ b : Colors, ContainsConfiguration (A.filter (fun x => color x = b)) P
          selector := by
  obtain ⟨c, C, hc, hC, N₀, hbound⟩ := hsmall
  let κ : ℝ := c / 2
  have hκ : 0 < κ := by dsimp [κ]; positivity
  obtain ⟨N₁, hN₁⟩ := eventually_log_power_exceeds ((Fintype.card Colors : ℝ) * C) hκ
  refine ⟨κ, hκ, max 2 (max N₀ N₁), ?_⟩
  intro N hN A hA hdense
  let B : Colors → Finset ℤ := fun b => A.filter (fun x => color x = b)
  by_contra hnone
  have hN₂ : 2 ≤ N := le_trans (le_max_left _ _) hN
  have hN₀ : N₀ ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hN)
  have hN₁' : N₁ ≤ N := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hN)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hpower_pos : 0 < (Real.log (N : ℝ)) ^ (-c) := Real.rpow_pos_of_pos hlog _
  have hNp : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hcard : (A.card : ℝ) = ∑ b : Colors, ((B b).card : ℝ) := by
    have heq : A.card = ∑ b : Colors, (B b).card :=
      Finset.card_eq_sum_card_fiberwise (t := Finset.univ) (f := color)
        (fun _ _ => Finset.mem_univ _)
    exact_mod_cast heq
  have hupper : (A.card : ℝ) ≤ (Fintype.card Colors : ℝ) * C *
      ((N : ℝ) * (Real.log (N : ℝ)) ^ (-c)) := by
    rw [hcard]
    calc
      ∑ b : Colors, ((B b).card : ℝ) ≤
          ∑ _ : Colors, C * ((N : ℝ) * (Real.log (N : ℝ)) ^ (-c)) := by
        apply Finset.sum_le_sum
        intro b _
        exact hbound N hN₀ (B b) ((Finset.filter_subset _ _).trans hA)
          (fun hb => hnone ⟨b, hb⟩)
      _ = _ := by simp [mul_assoc]
  have hstrict : (Fintype.card Colors : ℝ) * C *
      ((N : ℝ) * (Real.log (N : ℝ)) ^ (-c)) <
        (N : ℝ) * (Real.log (N : ℝ)) ^ (-κ) := by
    calc
      _ < (Real.log (N : ℝ)) ^ κ * ((N : ℝ) * (Real.log (N : ℝ)) ^ (-c)) :=
        mul_lt_mul_of_pos_right (hN₁ N hN₁') (mul_pos hNp hpower_pos)
      _ = (N : ℝ) * ((Real.log (N : ℝ)) ^ κ * (Real.log (N : ℝ)) ^ (-c)) := by ring
      _ = (N : ℝ) * (Real.log (N : ℝ)) ^ (-κ) := by
        have hκc : κ + -c = -κ := by dsimp [κ]; ring
        rw [← Real.rpow_add hlog, hκc]
  exact (not_lt_of_ge hdense) (hupper.trans_lt hstrict)

/-- A recurrence conclusion remains valid inside one monochromatic cell,
at a possibly smaller density exponent. -/
theorem recurrence_in_color_cell {ℓ : ℕ}
    {P : Fin (ℓ + 1) → Polynomial ℤ} {selector : ℕ → Prop}
    (hrec : RecurrenceConclusion P selector)
    {Colors : Type} [Fintype Colors] [DecidableEq Colors] (color : ℤ → Colors) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A : Finset ℤ, A ⊆ positiveInterval N →
        (N : ℝ) * (Real.log (N : ℝ)) ^ (-κ) ≤ (A.card : ℝ) →
        ∃ b : Colors, ContainsConfiguration (A.filter (fun x => color x = b)) P
          selector := by
  apply finite_coloring_forces_configuration P selector _ color
  obtain ⟨c, hc, N₀, hbound⟩ := hrec
  refine ⟨c, 1, hc, zero_lt_one, N₀, ?_⟩
  intro N hN A hA hnone
  rw [one_mul]
  exact le_of_lt (lt_of_not_ge (fun h => hnone (hbound N hN A hA h)))

/-- Corollary 1.1. The first shifted polynomial is `aX`, with signed
nonzero integer `a`. The conclusion includes all the original shifts and
their pairwise distinctness, as well as each strict Bohr condition. -/
theorem bohr_recurrence {ℓ r : ℕ} (P : Fin (ℓ + 1) → Polynomial ℤ)
    (hP : FixedPolynomialFamily P) (hKMTT : KMTTShiftedPrimeDensityBound)
    (a : ℤ) (ha : a ≠ 0) (hlinear : P 1 = C a * X)
    (ω : Fin r → ℝ) {ε : ℝ} (hε : 0 < ε) :
    RecurrenceConclusion P
      (fun p => ∀ i, ‖((ω i * (((p : ℤ) - 1 : ℤ) : ℝ) : ℝ) : Circle)‖ < ε) := by
  classical
  obtain ⟨L, hL, hwidth⟩ := exists_circle_bin_width hε
  let color (x : ℤ) (i : Fin r) : Fin L := circleBin L hL (ω i * (x : ℝ) / (a : ℝ))
  obtain ⟨κ, hκ, N₀, hcolors⟩ := finite_coloring_forces_configuration P (fun _ => True) (hKMTT P hP) color
  refine ⟨κ, hκ, N₀, ?_⟩
  intro N hN A hA hdense
  obtain ⟨b, x, p, hprime, _, hpoints, hdistinct⟩ := hcolors N hN A hA hdense
  refine ⟨x, p, hprime, ?_, (fun i => (Finset.mem_filter.1 (hpoints i)).1), hdistinct⟩
  have hx : color x = b := by
    simpa [hP.2.1] using (Finset.mem_filter.1 (hpoints 0)).2
  have hy : color (x + a * ((p : ℤ) - 1)) = b := by
    simpa [hlinear] using (Finset.mem_filter.1 (hpoints 1)).2
  intro i
  have hsame := congrFun (hy.trans hx.symm) i
  have hscaled : ω i * ((x + a * ((p : ℤ) - 1) : ℤ) : ℝ) / (a : ℝ) -
      ω i * (x : ℝ) / (a : ℝ) = ω i * (((p : ℤ) - 1 : ℤ) : ℝ) := by
    have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
    push_cast
    field_simp
    ring
  have hphase := norm_circle_sub_lt_of_circleBin_eq hL hsame
  change ‖((ω i * ((x + a * ((p : ℤ) - 1) : ℤ) : ℝ) / (a : ℝ) -
      ω i * (x : ℝ) / (a : ℝ) : ℝ) : Circle)‖ < 1 / (L : ℝ) at hphase
  rw [hscaled] at hphase
  exact hphase.trans hwidth

end NilBohr
