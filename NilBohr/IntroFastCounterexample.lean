import NilBohr.IntroFastApproximants
import NilBohr.IntroFastObstruction

/-! The failure of every fixed polylogarithmic density threshold when
irrationality of the Heisenberg parameter is the sole condition. -/

open Filter
open scoped Topology

namespace NilBohr

/-- The introductory obstruction holds on one common sequence of sets for
all fixed positive density exponents. It excludes every positive shift,
so in particular it excludes the selected shifted-prime configurations. -/
theorem intro_fast_approximation_counterexample :
    ∃ (β : ℝ) (a r : ℕ → ℕ), 0 < β ∧ β < 1 ∧ Irrational β ∧ StrictMono r ∧
      (∀ j, (r j).Prime ∧ 0 < a j ∧ a j < r j ∧
        0 < β - (a j : ℝ)/(r j : ℝ) ∧
        β - (a j : ℝ)/(r j : ℝ) < Real.exp (-((r j : ℝ)^j))) ∧
      let N := fun j => fastApproximationScale (r j) j
      Tendsto N atTop atTop ∧ ∀ α : ℝ, ∃ A : ℕ → Finset ℤ,
        (∀ j, A j ⊆ positiveInterval (N j) ∧
          ∀ {x : ℤ} {n : ℕ}, x ∈ A j → x + (n : ℤ) ∈ A j → x + (n : ℤ)^2 ∈ A j →
            ¬ introObstructionArc.Contains (heisenbergPhase α β (n : ℤ))) ∧
        (∀ᶠ j : ℕ in atTop, 1/(578*(r j : ℝ)) ≤ setDensity (A j) (N j)) ∧
        ∀ κ : ℝ, 0 < κ → ∀ᶠ j : ℕ in atTop,
          (Real.log (N j : ℝ))^(-κ) < setDensity (A j) (N j) := by
  obtain ⟨β, a, r, hβ₀, hβ₁, hβirr, hr, _, _, h⟩ := exists_fast_prime_approximants
  have hr₂ (j : ℕ) : 2 ≤ r j := (h j).1.two_le
  let N := fun j => fastApproximationScale (r j) j
  refine ⟨β, a, r, hβ₀, hβ₁, hβirr, hr, h, tendsto_fastApproximationScale r hr₂, ?_⟩
  intro α
  have hset (j : ℕ) :
      ∃ B : Finset ℤ, B ⊆ positiveInterval (N j) ∧
        (r j ≤ N j → 1/(578*(r j : ℝ)) ≤ setDensity B (N j)) ∧
        ∀ {x : ℤ} {n : ℕ}, x ∈ B → x + (n : ℤ) ∈ B → x + (n : ℤ)^2 ∈ B →
          ¬ introObstructionArc.Contains (heisenbergPhase α β (n : ℤ)) := by
    by_cases hN : r j ≤ N j
    · obtain ⟨B, hsub, hd, hAvoid⟩ :=
        exists_fastApproximationScale_obstruction (α := α)
          (h j).1.pos hN (h j).2.2.2.1.le (h j).2.2.2.2
      exact ⟨B, hsub, fun _ => hd, hAvoid⟩
    · exact ⟨∅, Finset.empty_subset _, fun h' => (hN h').elim,
        fun hx => (Finset.not_mem_empty _ hx).elim⟩
  choose A hA using hset
  have hDen : ∀ᶠ j : ℕ in atTop, 1/(578*(r j : ℝ)) ≤ setDensity (A j) (N j) := by
    filter_upwards [eventually_two_mul_le_fastApproximationScale hr] with j hN
    exact (hA j).2.1 (by
      change r j ≤ fastApproximationScale (r j) j
      omega)
  refine ⟨A, fun j => ⟨(hA j).1, (hA j).2.2⟩, hDen, ?_⟩
  intro κ hκ
  filter_upwards [eventually_fastApproximationScale_log_neg_rpow_lt hr hr₂ hκ
    (show (0 : ℝ) < 1/578 by norm_num), hDen] with j hκj hd
  rw [div_div] at hκj
  exact hκj.trans_le hd

end NilBohr
