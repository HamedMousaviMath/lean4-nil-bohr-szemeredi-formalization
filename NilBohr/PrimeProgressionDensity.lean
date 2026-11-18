import NilBohr.BohrPrimeProgressions

/-! Combining the two prime progression inputs in the introduction. -/

namespace NilBohr

open Filter Set
open scoped Topology

private theorem tendsto_sparseGreenTaoBound (k : ℕ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun N : ℕ => sparseGreenTaoBound k N c) atTop (𝓝 0) := by
  have hcast : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog := Real.tendsto_log_atTop.comp hcast
  have hloglog := Real.tendsto_log_atTop.comp hlog
  by_cases hk : k = 4
  · simpa only [sparseGreenTaoBound, hk, if_true, Function.comp_def] using
      (tendsto_rpow_neg_atTop hc).comp hloglog
  · have hlogloglog := Real.tendsto_log_atTop.comp hloglog
    have hpow := (tendsto_rpow_atTop hc).comp hlogloglog
    simpa only [sparseGreenTaoBound, hk, if_false, Function.comp_def] using
      Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hpow)

/-- The qualitative positive-density premise for fixed windows follows
from the quantitative sparse-prime theorem already used for moving
windows. Lengths two and three follow by taking an initial segment of a
four-term progression. -/
theorem greenTaoRelativeDensity_of_sparse (hTW : TeravainenWangSparseGreenTao) :
    GreenTaoRelativeDensity := by
  classical
  intro A _ ⟨δ,hδ,hA⟩ k _
  let m := max 4 k
  obtain ⟨C,c,hC,hc,hTW'⟩ := hTW m (le_max_left _ _)
  have hzero : Tendsto (fun N : ℕ => C * sparseGreenTaoBound m N c) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_sparseGreenTaoBound m hc).const_mul C
  obtain ⟨N,hN,hnδ,hsmall⟩ := ((eventually_ge_atTop (100 : ℕ)).and
    (hA.and (hzero.eventually (Iio_mem_nhds hδ)))).exists
  let B := (primesThrough N).filter (· ∈ A)
  have hB : ContainsPrimeProgression (B : Set ℕ) m := by
    by_contra hfree
    have H := hTW' N B hN (Finset.filter_subset _ _) hfree
    exact (lt_irrefl δ) ((hnδ.trans H).trans_lt hsmall)
  obtain ⟨p,r,hr,hprog⟩ := hB
  refine ⟨p,r,hr,?_⟩
  intro i
  have hi := hprog (Fin.castLE (le_max_right 4 k) i)
  exact (Finset.mem_filter.mp hi).2

/-- The fixed-window deduction using the same external input as the
shrinking-window deduction. -/
theorem fixedWindow_primeProgression_of_sparse (hTW : TeravainenWangSparseGreenTao)
    (V : ℤ → ℝ) (J : OpenArc)
    (hD : Tendsto (primeDensityRatio V J) atTop (𝓝 J.length))
    (k : ℕ) (hk : 2 ≤ k) :
    ContainsPrimeProgression {p | Nat.Prime p ∧ J.Contains (V ((p : ℤ) - 1))} k :=
  fixedWindow_primeProgression (greenTaoRelativeDensity_of_sparse hTW) V J hD k hk

end NilBohr
