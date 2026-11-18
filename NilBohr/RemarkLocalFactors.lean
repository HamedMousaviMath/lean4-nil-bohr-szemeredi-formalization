import NilBohr.Density
import NilBohr.InverseFourier

/-! The fixed-modulus derivative argument in Remark 1.6. -/

open scoped BigOperators

namespace NilBohr

/-- The auxiliary denominator from the unweighted inverse is absorbed in a
single further power of the base modulus when it divides the initial lcm. -/
theorem auxiliary_step_dvd_fixed_power {q r b B w : ℕ}
    (hr : 0 < r) (hrw : r ≤ w) (hw : initialModulus w ∣ q) (hb : b ≤ B) :
    r * q^b ∣ q^(B+1) := by
  have hrq : r ∣ q := (show r ∣ initialModulus w from
    Finset.dvd_lcm (Finset.mem_Icc.mpr ⟨hr, hrw⟩)).trans hw
  refine (mul_dvd_mul_right hrq (q^b)).trans ?_
  rw [← pow_succ']
  exact pow_dvd_pow q (Nat.succ_le_succ hb)

/-- Pull a Lipschitz bound back to a prescribed multiple of its step. -/
theorem modular_lipschitz_of_dvd (φ : ℤ → ℂ) {s L : ℕ}
    (hs : 0 < s) (hsL : s ∣ L) {D : ℝ} (hD : 0 ≤ D)
    (hφ : ∀ x t : ℤ, ‖φ (x + (s : ℤ)*t) - φ x‖ ≤ D*|(t : ℝ)|) :
    ∀ x t : ℤ, ‖φ (x + (L : ℤ)*t) - φ x‖ ≤ (D*(L : ℝ))*|(t : ℝ)| := by
  obtain ⟨u, hu⟩ := hsL
  have huL : u ≤ L := by
    rw [hu]
    exact Nat.le_mul_of_pos_left u hs
  intro x t
  have h := hφ x ((u : ℤ)*t)
  rw [← mul_assoc, ← Nat.cast_mul, ← hu, Int.cast_mul, Int.cast_natCast, abs_mul,
    abs_of_nonneg (Nat.cast_nonneg u), ← mul_assoc] at h
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr huL) hD) (abs_nonneg _))

/-- If the step is already fixed, approximation by the value at the start
of each progression gives a derivative correlation at frequency zero. -/
theorem zero_frequency_correlation_of_fixed_step
    (X : Finset ℤ) (f φ : ℤ → ℂ) (hf : SupportedOn X f)
    (hunit : ∀ x, ‖f x‖ ≤ 1) (hφ : ∀ x, ‖φ x‖ ≤ 1)
    (h : ℤ) {L V : ℕ} (hL : 0 < L) (hV : 0 < V)
    (D R : ℝ) (hD : 0 ≤ D)
    (hLip : ∀ x t : ℤ, ‖φ (x + (L : ℤ)*t) - φ x‖ ≤ D*|(t : ℝ)|)
    (hError : ((occupiedLocalBlocks X L V).card : ℝ) * V * (D*(V : ℝ)) ≤ R/2)
    (hCorr : R ≤ ‖∑ x ∈ X, spatialMultiplicativeDifference f h x * φ x‖) :
    R/2 ≤ ∑ i ∈ occupiedLocalBlocks X L V,
      ‖localDifferenceCorrelation f (positiveInterval V) (localBlockOrigin L V i) (L : ℤ) 0 h‖ := by
  let A := occupiedLocalBlocks X L V
  let a := localBlockOrigin L V
  let g := spatialMultiplicativeDifference f h
  have hGS : SupportedOn X (fun x => g x * φ x) := by
    intro x hx
    simp [g, spatialMultiplicativeDifference, hf _ hx]
  have hg : ∀ x : ℤ, ‖g x‖ ≤ 1 := by
    intro x
    simp only [g, spatialMultiplicativeDifference, norm_mul, Complex.norm_conj]
    exact mul_le_one₀ (hunit _) (norm_nonneg _) (hunit _)
  have hT (i : ℤ × ℤ) (t : ℤ) (ht : t ∈ positiveInterval V) :
      ‖g (a i + (L : ℤ)*t) * φ (a i + (L : ℤ)*t) -
          g (a i + (L : ℤ)*t) * φ (a i)‖ ≤ D*(V : ℝ) := by
    have ht' := Finset.mem_Icc.mp ht
    have ht₀ : (0 : ℝ) ≤ (t : ℝ) := by exact_mod_cast (show 0 ≤ t by omega)
    have htV : (t : ℝ) ≤ V := by exact_mod_cast ht'.2
    rw [← mul_sub, norm_mul]
    refine (mul_le_of_le_one_left (norm_nonneg _) (hg _)).trans ?_
    refine (hLip (a i) t).trans ?_
    rw [abs_of_nonneg ht₀]
    exact mul_le_mul_of_nonneg_left htV hD
  have hAtom (i : ℤ × ℤ) :
      ‖∑ t ∈ positiveInterval V, g (a i + (L : ℤ)*t) * φ (a i + (L : ℤ)*t)‖ ≤
        ‖localDifferenceCorrelation f (positiveInterval V) (a i) (L : ℤ) 0 h‖ +
          (V : ℝ)*(D*(V : ℝ)) := by
    let A₁ := ∑ t ∈ positiveInterval V, g (a i + (L : ℤ)*t) * φ (a i + (L : ℤ)*t)
    let A₀ := ∑ t ∈ positiveInterval V, g (a i + (L : ℤ)*t) * φ (a i)
    have hDiff : ‖A₁-A₀‖ ≤ (V : ℝ)*(D*(V : ℝ)) := by
      dsimp only [A₁,A₀]
      rw [← Finset.sum_sub_distrib]
      refine (norm_sum_le _ _).trans ?_
      simpa only [Finset.sum_const, card_positiveInterval, nsmul_eq_mul] using
        (Finset.sum_le_sum fun t ht => hT i t ht)
    have hMain : ‖A₀‖ ≤ ‖localDifferenceCorrelation f (positiveInterval V) (a i) (L : ℤ) 0 h‖ := by
      dsimp only [A₀, localDifferenceCorrelation]
      rw [← Finset.sum_mul, norm_mul]
      simp only [fourier_eval_zero, mul_one]
      exact mul_le_of_le_one_right (norm_nonneg _) (hφ _)
    change ‖A₁‖ ≤ _
    calc
      ‖A₁‖ = ‖(A₁-A₀)+A₀‖ := by rw [sub_add_cancel]
      _ ≤ ‖A₁-A₀‖ + ‖A₀‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  have hBounds :
      ‖∑ x ∈ X, g x * φ x‖ ≤
        (∑ i ∈ A, ‖localDifferenceCorrelation f (positiveInterval V) (a i) (L : ℤ) 0 h‖) +
          (A.card : ℝ)*V*(D*(V : ℝ)) := by
    rw [sum_occupiedLocalBlocks _ hGS hL hV]
    refine (norm_sum_le _ _).trans ?_
    simpa only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_assoc] using
      (Finset.sum_le_sum (s := A) fun i _ => hAtom i)
  change R/2 ≤ ∑ i ∈ A, _
  linarith only [hCorr, hBounds, hError]

/-- On fixed progressions the differentiated frequency is exactly zero.
The remaining Fourier maximization is separate on each progression. -/
theorem exists_localBlockPhase_of_fixed_step_correlations
    (X G : Finset ℤ) (hG : G.Nonempty) (f : ℤ → ℂ)
    (hf : SupportedOn X f) (hunit : ∀ x, ‖f x‖ ≤ 1)
    {L V : ℕ} (hL : 0 < L) (hV : 0 < V) (D R : ℝ) (hD : 0 ≤ D) (hR : 0 ≤ R)
    (hError : ((occupiedLocalBlocks X L V).card : ℝ) * V * (D * (V : ℝ)) ≤ R / 2)
    (hCorr : ∀ h ∈ G, ∃ φ : ℤ → ℂ, (∀ x, ‖φ x‖ ≤ 1) ∧
      (∀ x t : ℤ, ‖φ (x + (L : ℤ)*t) - φ x‖ ≤ D * |(t : ℝ)|) ∧
      R ≤ ‖∑ x ∈ X, spatialMultiplicativeDifference f h x * φ x‖) :
    ∃ b γ : (ℤ × ℤ) → ℝ,
      (G.card : ℝ) * R ^ 2 ≤ 4 * (X.card : ℝ) *
        ((occupiedLocalBlocks X L V).card : ℝ) * V *
        ‖∑ x ∈ X, f x * localBlockPhase L V b γ x‖ := by
  obtain ⟨b, γ, hBound⟩ := exists_localBlockPhase_of_fixed_frequency X G hG f hf hunit
    hL hV 0 (R/2) (by positivity) (fun h hh => by
      obtain ⟨φ, hφ, hLip, hCorr⟩ := hCorr h hh
      exact zero_frequency_correlation_of_fixed_step X f φ hf hunit hφ h hL hV D R
        hD hLip hError hCorr)
  refine ⟨b, γ, ?_⟩
  calc
    _ = 4 * ((G.card : ℝ) * (R/2)^2) := by ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left hBound (by norm_num : (0:ℝ) ≤ 4)).trans_eq (by ring)

/-- The inverse inputs require an initial lcm at a polynomial cutoff in
the inverse threshold. Positivity is included to give a monotone guard. -/
def LcmCutoff (U E : ℝ) (q : ℕ) (δ : ℝ) : Prop :=
  0 < δ ∧ initialModulus ⌈U*δ^(-E)⌉₊ ∣ q

theorem lcmCutoff_mono {U E : ℝ} (hU : 0 ≤ U) (hE : 0 ≤ E) (q : ℕ) :
    Monotone (LcmCutoff U E q) := by
  intro t s hts ht
  refine ⟨ht.1.trans_le hts, ?_⟩
  apply dvd_trans _ ht.2
  have hCut : ⌈U*s^(-E)⌉₊ ≤ ⌈U*t^(-E)⌉₊ :=
    Nat.ceil_mono (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_nonpos ht.1 hts (neg_nonpos.mpr hE)) hU)
  unfold initialModulus
  exact Finset.lcm_dvd (fun _ hm => Finset.dvd_lcm
    (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hm).1, (Finset.mem_Icc.mp hm).2.trans hCut⟩))

theorem lcmCutoff_at_replacementRate {U E a V δ : ℝ} {q : ℕ}
    (ha : 0 < a) (h : LcmCutoff (U*a^(-E)) (V*E) q δ) :
    LcmCutoff U E q (a*δ^V) := by
  have hδ := h.1
  refine ⟨by positivity, ?_⟩
  rw [Real.mul_rpow ha.le (Real.rpow_nonneg h.1.le _), ← Real.rpow_mul h.1.le,
    mul_neg, ← mul_assoc]
  exact h.2

theorem lcmCutoff_of_le_cutoff {U E δ : ℝ} {q w : ℕ}
    (hδ : 0 < δ) (h : U*δ^(-E) ≤ w) (hDiv : initialModulus w ∣ q) :
    LcmCutoff U E q δ := by
  refine ⟨hδ, dvd_trans ?_ hDiv⟩
  have hCut : ⌈U*δ^(-E)⌉₊ ≤ w := Nat.ceil_le.mpr h
  unfold initialModulus
  exact Finset.lcm_dvd (fun _ hm => Finset.dvd_lcm
    (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hm).1, (Finset.mem_Icc.mp hm).2.trans hCut⟩))

end NilBohr
