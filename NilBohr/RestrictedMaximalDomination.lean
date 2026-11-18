import NilBohr.BohrPrimeProgressions

/-! The positive-density restriction transfers unrestricted positive
maximal bounds, with all initial scales included. -/

open Filter Topology

namespace NilBohr

/-- Positive limiting relative density gives a uniform pointwise
domination for the restricted averages. The constant is independent
of the summands and of the cutoff, including empty selected sets. -/
theorem selectedPrimeAverage_domination (V : ℤ → ℝ) (J : OpenArc)
    (hDensity : Tendsto (primeDensityRatio V J) atTop (𝓝 J.length)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → ℂ) (N : ℕ),
      ‖selectedPrimeAverage V J a N‖ ≤
        C * ((∑ p ∈ primesThrough N, ‖a p‖) / ((primesThrough N).card : ℝ)) := by
  have hEventually : ∀ᶠ N : ℕ in atTop, J.length/2 < primeDensityRatio V J N :=
    hDensity.eventually (Ioi_mem_nhds (by linarith [J.length_pos]))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hEventually
  let C := max (N₀ + 1 : ℝ) (2 / J.length)
  have hN₀one : (1 : ℝ) ≤ N₀ + 1 := by linarith [(show (0 : ℝ) ≤ (N₀ : ℝ) from Nat.cast_nonneg _)]
  have hC : 0 < C := zero_lt_one.trans_le (hN₀one.trans (le_max_left _ _))
  refine ⟨C, hC, ?_⟩
  intro a N
  have hmean : 0 ≤ ((∑ p ∈ primesThrough N, ‖a p‖) / ((primesThrough N).card : ℝ)) := by
    positivity
  by_cases h : 0 < (primesSelectedThrough V J N).card
  · by_cases hN : N₀ ≤ N
    · have h := norm_selectedPrimeAverage_le_of_density V J a N (half_pos J.length_pos)
        (hN₀ N hN).le
      rw [show (J.length/2)⁻¹ = 2/J.length by rw [inv_div]] at h
      exact h.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hmean)
    · have hP : ((primesThrough N).card : ℝ) ≤ N₀ + 1 := by
        have hcard := Finset.card_filter_le (p := Nat.Prime) (Finset.range (N+1))
        have hN' : N ≤ N₀ := by omega
        exact_mod_cast (show (primesThrough N).card ≤ N₀+1 from
          (by simpa [primesThrough] using hcard : (primesThrough N).card ≤ N+1).trans
            (Nat.add_le_add_right hN' 1))
      have hs : (1 : ℝ) ≤ (primesSelectedThrough V J N).card := by exact_mod_cast h
      have hsub : primesSelectedThrough V J N ⊆ primesThrough N := by
        classical
        exact Finset.filter_subset _ _
      have hp : (0 : ℝ) < (primesThrough N).card := by
        exact_mod_cast h.trans_le (Finset.card_le_card hsub)
      let d : ℝ := (N₀+1)⁻¹
      have hd : 0 < d := by dsimp [d]; positivity
      have hD : d ≤ primeDensityRatio V J N := by
        unfold d primeDensityRatio
        exact (inv_anti₀ hp hP).trans
          (by rw [← one_div]; exact div_le_div_of_nonneg_right hs hp.le)
      have hDom := norm_selectedPrimeAverage_le_of_density V J a N hd hD
      rw [show d⁻¹ = N₀+1 by simp [d]] at hDom
      exact hDom.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hmean)
  · have hz : primesSelectedThrough V J N = ∅ :=
      Finset.card_eq_zero.mp (by omega)
    simpa [selectedPrimeAverage, hz] using mul_nonneg hC.le hmean

end NilBohr
