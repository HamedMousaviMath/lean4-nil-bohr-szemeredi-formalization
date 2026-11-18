import NilBohr.Ergodic
import Mathlib.Data.Complex.ExponentialBounds

/-! The two prime progression observations in the introduction. -/

namespace NilBohr

open Filter Set
open scoped Topology

/-- A nontrivial increasing arithmetic progression of length `k`. -/
def ContainsPrimeProgression (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ p r : ℕ, 0 < r ∧ ∀ i : Fin k, p + (i : ℕ) * r ∈ A

/-- Prime-relative counting ratio for an arbitrary set. -/
noncomputable def primeSetRatio (A : Set ℕ) (N : ℕ) : ℝ := by
  classical
  exact (((primesThrough N).filter (· ∈ A)).card : ℝ) / (primesThrough N).card

/-- The relative-density Green–Tao theorem, specialized to the positive
lower relative density form used for a fixed window. -/
def GreenTaoRelativeDensity : Prop :=
  ∀ A : Set ℕ, A ⊆ {p | Nat.Prime p} →
    (∃ δ : ℝ, 0 < δ ∧ ∀ᶠ N in (atTop : Filter ℕ), δ ≤ primeSetRatio A N) →
    ∀ k : ℕ, 2 ≤ k → ContainsPrimeProgression A k

/-- A fixed window with a positive prime-relative density contains
arbitrarily long nontrivial progressions. -/
theorem fixedWindow_primeProgression (hGT : GreenTaoRelativeDensity)
    (V : ℤ → ℝ) (J : OpenArc)
    (hD : Tendsto (primeDensityRatio V J) atTop (𝓝 J.length))
    (k : ℕ) (hk : 2 ≤ k) :
    ContainsPrimeProgression {p | Nat.Prime p ∧ J.Contains (V ((p : ℤ) - 1))} k := by
  let A : Set ℕ := {p | Nat.Prime p ∧ J.Contains (V ((p : ℤ) - 1))}
  apply hGT A (fun _ hp => hp.1) _ k hk
  refine ⟨J.length / 2, half_pos J.length_pos, ?_⟩
  have he : primeSetRatio A = primeDensityRatio V J := by
    funext N
    classical
    unfold primeSetRatio primeDensityRatio primesSelectedThrough
    apply congrArg (fun a : ℕ => (a : ℝ) / ((primesThrough N).card : ℝ))
    apply congrArg Finset.card
    ext p
    simp only [Finset.mem_filter, A, Set.mem_setOf_eq]
    exact ⟨fun h => ⟨h.1,h.2.2⟩, fun h => ⟨h.1,(Finset.mem_filter.mp h.1).2,h.2⟩⟩
  rw [he]
  exact hD.eventually (Ici_mem_nhds (half_lt_self J.length_pos))

/-- The separate logarithmic density bounds for progression-free subsets
of primes in Teräväinen–Wang, Theorem 1.1. -/
noncomputable def sparseGreenTaoBound (k N : ℕ) (c : ℝ) : ℝ :=
  if k = 4 then (Real.log (Real.log (N : ℝ))) ^ (-c)
  else Real.exp (- (Real.log (Real.log (Real.log (N : ℝ)))) ^ c)

/-- The constants in Teräväinen–Wang may depend on the progression length,
with an ambient cutoff of 100. -/
def TeravainenWangSparseGreenTao : Prop :=
  ∀ k : ℕ, 4 ≤ k → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ (N : ℕ) (A : Finset ℕ), 100 ≤ N → A ⊆ primesThrough N →
      ¬ ContainsPrimeProgression (A : Set ℕ) k →
      (A.card : ℝ) / (primesThrough N).card ≤ C * sparseGreenTaoBound k N c

private theorem one_le_log_log {N : ℕ} (hN : 100 ≤ N) :
    1 ≤ Real.log (Real.log (N : ℝ)) := by
  have e3 : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
  have h3 : Real.exp 3 < 27 := by
    rw [show (3 : ℝ) = (3 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
    calc
      Real.exp 1 ^ (3 : ℕ) < (3 : ℝ) ^ (3 : ℕ) :=
        pow_lt_pow_left₀ e3 (Real.exp_nonneg _) (by decide)
      _ = _ := by norm_num
  have hN' : (100 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : (3 : ℝ) ≤ Real.log (N : ℝ) :=
    (Real.le_log_iff_exp_le (by positivity)).mpr (by linarith)
  exact (Real.le_log_iff_exp_le (by linarith)).mpr (e3.le.trans hlog)

private theorem sparseGreenTaoBound_four_le {N : ℕ} (hN : 100 ≤ N) {c : ℝ} (hc : 0 < c) :
    sparseGreenTaoBound 4 N c ≤ Real.exp ((4 * c)⁻¹) *
      Real.exp (- (Real.log (Real.log (Real.log (N : ℝ)))) ^ (1 / 2 : ℝ)) := by
  let u := Real.log (Real.log (N : ℝ))
  have hu : 1 ≤ u := one_le_log_log hN
  have hu' : 0 < u := by linarith
  have hlog : 0 ≤ Real.log u := Real.log_nonneg hu
  have hu'power : u ^ (-c) = Real.exp (-c * Real.log u) :=
    by rw [Real.rpow_def_of_pos hu', mul_comm]
  change (if (4 : ℕ) = 4 then u ^ (-c) else _) ≤ _
  rw [if_pos rfl, hu'power, ← Real.sqrt_eq_rpow, ← Real.exp_add, Real.exp_le_exp]
  change -c * Real.log u ≤ (4 * c)⁻¹ - √(Real.log u)
  have hs := Real.sq_sqrt hlog
  rw [show (4 * c)⁻¹ = 1 / (4 * c) by rw [one_div], le_sub_iff_add_le,
    le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (2 * c * √(Real.log u) - 1), congrArg (fun x => 4 * c ^ 2 * x) hs]

/-- The common weaker threshold displayed in the manuscript, with
constants depending only on the length. The conclusion is finite and
holds at the very same ambient scale. -/
theorem shrinkingWindow_primeProgression (hTW : TeravainenWangSparseGreenTao)
    (k : ℕ) (hk : 4 ≤ k) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (V : ℤ → ℝ) (J : ℕ → OpenArc) (N : ℕ),
      100 ≤ N →
      C * Real.exp (- (Real.log (Real.log (Real.log (N : ℝ)))) ^ c) <
        primeDensityRatio V (J N) N →
      ContainsPrimeProgression (primesSelectedThrough V (J N) N : Set ℕ) k := by
  obtain ⟨C,c,hC,hc,hTW⟩ := hTW k hk
  by_cases h4 : k = 4
  · subst k
    refine ⟨C * Real.exp ((4 * c)⁻¹), 1/2, by positivity, by norm_num, ?_⟩
    intro V J N hN hd
    apply Classical.byContradiction
    intro hfree
    have hsub : primesSelectedThrough V (J N) N ⊆ primesThrough N := by
      classical
      exact Finset.filter_subset _ _
    have hD := hTW N _ hN hsub hfree
    have hbound := (hD.trans (mul_le_mul_of_nonneg_left
      (sparseGreenTaoBound_four_le hN hc) hC.le))
    exact hd.not_le (by simpa only [primeDensityRatio, mul_assoc] using hbound)
  · refine ⟨C,c,hC,hc,?_⟩
    intro V J N hN hd
    apply Classical.byContradiction
    intro hfree
    have hsub : primesSelectedThrough V (J N) N ⊆ primesThrough N := by
      classical
      exact Finset.filter_subset _ _
    have hD := hTW N _ hN hsub hfree
    exact hd.not_le (by simpa only [primeDensityRatio, sparseGreenTaoBound, h4, if_false] using hD)

/-- At scales with a positive lower bound on the selected prime density,
the absolute selected average is dominated by the unrestricted positive
average times the reciprocal lower density. -/
theorem norm_selectedPrimeAverage_le_of_density (V : ℤ → ℝ) (J : OpenArc)
    (a : ℕ → ℂ) (N : ℕ) {d : ℝ} (hd : 0 < d) (hD : d ≤ primeDensityRatio V J N) :
    ‖selectedPrimeAverage V J a N‖ ≤
      d⁻¹ * ((∑ p ∈ primesThrough N, ‖a p‖) / ((primesThrough N).card : ℝ)) := by
  have hpos := hd.trans_le hD
  have hsub : primesSelectedThrough V J N ⊆ primesThrough N := by
    classical
    exact Finset.filter_subset _ _
  have hnum : ‖selectedOverPrimes V J a N‖ ≤
      (∑ p ∈ primesThrough N, ‖a p‖) / ((primesThrough N).card : ℝ) := by
    rw [selectedOverPrimes, norm_div, Complex.norm_natCast]
    exact div_le_div_of_nonneg_right ((norm_sum_le _ _).trans
      (Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => norm_nonneg _)) (by positivity)
  rw [selectedPrimeAverage_eq_div_ratio, norm_div, Complex.norm_real, Real.norm_of_nonneg hpos.le]
  calc
    _ ≤ ‖selectedOverPrimes V J a N‖ / d :=
      div_le_div_of_nonneg_left (norm_nonneg _) hd hD
    _ ≤ _ := by rw [mul_comm, ← div_eq_mul_inv]; exact div_le_div_of_nonneg_right hnum hd.le

/-- For a fixed window with positive limiting relative density, the
domination needed for a tail maximal estimate holds simultaneously for
all test sequences and all sufficiently large scales. -/
theorem eventually_norm_selectedPrimeAverage_le (V : ℤ → ℝ) (J : OpenArc)
    (hD : Tendsto (primeDensityRatio V J) atTop (𝓝 J.length)) :
    ∀ᶠ N in (atTop : Filter ℕ), ∀ a : ℕ → ℂ,
      ‖selectedPrimeAverage V J a N‖ ≤ (J.length / 2)⁻¹ *
        ((∑ p ∈ primesThrough N, ‖a p‖) / ((primesThrough N).card : ℝ)) :=
  (hD.eventually (Ici_mem_nhds (half_lt_self J.length_pos))).mono
    (fun N hN a => norm_selectedPrimeAverage_le_of_density V J a N (half_pos J.length_pos) hN)

end NilBohr
