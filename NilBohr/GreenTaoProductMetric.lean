import NilBohr.GreenTaoModel
import NilBohr.TwistedOrbit

/-! The concrete product chain metric from Green–Tao Definition 2.2.
This file establishes the two projection bounds and the twisted Lipschitz test.
The group and quotient topologies are established in GreenTaoProductMetricTopology. -/

open MeasureTheory

namespace NilBohr

noncomputable section

/-- The symmetric edge cost of the Mal'cev chain in product coordinates. -/
def productMalcevEdge (g h : HeisenbergPoint × ℝ) : ℝ :=
  min
    (max (heisenbergMalcevNorm (heisenbergMul g.1 (heisenbergInv h.1))) |g.2 - h.2|)
    (max (heisenbergMalcevNorm (heisenbergMul h.1 (heisenbergInv g.1))) |h.2 - g.2|)

private def productChainLengths (g h : HeisenbergPoint × ℝ) : Set ℝ :=
  {d | ∃ (n : ℕ) (x : ℕ → HeisenbergPoint × ℝ), x 0 = g ∧ x n = h ∧
    d = ∑ i ∈ Finset.range n, productMalcevEdge (x i) (x (i+1))}

def heisenbergProductGroupDistance (g h : HeisenbergPoint × ℝ) : ℝ :=
  sInf (productChainLengths g h)

private def productRepresentativeDistances (g h : HeisenbergPoint × ℝ) : Set ℝ :=
  {d | ∃ u v w b : ℤ, d = heisenbergProductGroupDistance g
    (heisenbergMul h.1 ((u : ℝ), (v : ℝ), (w : ℝ)), h.2 + b)}

def heisenbergProductQuotientDistance (g h : HeisenbergPoint × ℝ) : ℝ :=
  sInf (productRepresentativeDistances g h)

private theorem productChainLengths_nonempty (g h : HeisenbergPoint × ℝ) :
    (productChainLengths g h).Nonempty := by
  let x : ℕ → HeisenbergPoint × ℝ := fun i => if i = 0 then g else h
  exact ⟨_, 1, x, by simp [x], by simp [x], rfl⟩

private theorem productRepresentativeDistances_nonempty (g h : HeisenbergPoint × ℝ) :
    (productRepresentativeDistances g h).Nonempty :=
  ⟨_, 0, 0, 0, 0, rfl⟩

private theorem malcevCoordinateChain_nonneg (n : ℕ) (x : ℕ → HeisenbergPoint) :
    0 ≤ ∑ i ∈ Finset.range n,
      min (heisenbergMalcevNorm (heisenbergMul (x i) (heisenbergInv (x (i+1)))))
        (heisenbergMalcevNorm (heisenbergMul (x (i+1)) (heisenbergInv (x i)))) :=
  Finset.sum_nonneg (fun _ _ => le_min (by unfold heisenbergMalcevNorm; positivity)
    (by unfold heisenbergMalcevNorm; positivity))

private theorem productGroupDistance_nonneg (g h : HeisenbergPoint × ℝ) :
    0 ≤ heisenbergProductGroupDistance g h := by
  apply le_csInf (productChainLengths_nonempty g h)
  rintro _ ⟨n, x, _, _, rfl⟩
  apply Finset.sum_nonneg
  intro i _
  unfold productMalcevEdge
  exact le_min (le_max_of_le_right (abs_nonneg _)) (le_max_of_le_right (abs_nonneg _))

theorem heisenbergProductQuotientDistance_nonneg (g h : HeisenbergPoint × ℝ) :
    0 ≤ heisenbergProductQuotientDistance g h := by
  apply le_csInf (productRepresentativeDistances_nonempty g h)
  rintro _ ⟨u, v, w, b, rfl⟩
  exact productGroupDistance_nonneg _ _

theorem heisenbergGroupDistance_le_product (g h : HeisenbergPoint × ℝ) :
    heisenbergGroupDistance g.1 h.1 ≤ heisenbergProductGroupDistance g h := by
  apply le_csInf (productChainLengths_nonempty g h)
  rintro _ ⟨n, x, hx, hy, rfl⟩
  unfold heisenbergGroupDistance
  have hbelow : BddBelow {d : ℝ | ∃ (n : ℕ) (x : ℕ → HeisenbergPoint),
      x 0 = g.1 ∧ x n = h.1 ∧ d = ∑ i ∈ Finset.range n,
        min (heisenbergMalcevNorm (heisenbergMul (x i) (heisenbergInv (x (i+1)))))
          (heisenbergMalcevNorm (heisenbergMul (x (i+1)) (heisenbergInv (x i))))} := by
    refine ⟨0, ?_⟩
    rintro _ ⟨m, y, _, _, rfl⟩
    exact malcevCoordinateChain_nonneg m y
  refine (csInf_le hbelow
    ⟨n, fun i => (x i).1, congrArg Prod.fst hx, congrArg Prod.fst hy, rfl⟩).trans ?_
  apply Finset.sum_le_sum
  intro i _
  exact min_le_min (le_max_left _ _) (le_max_left _ _)

theorem abs_sub_le_heisenbergProductGroupDistance (g h : HeisenbergPoint × ℝ) :
    |g.2 - h.2| ≤ heisenbergProductGroupDistance g h := by
  apply le_csInf (productChainLengths_nonempty g h)
  rintro _ ⟨n, x, hx, hy, rfl⟩
  have hsum := dist_le_range_sum_of_dist_le (f := fun i => (x i).2) n
    (d := fun i => productMalcevEdge (x i) (x (i+1))) (fun i => by
      rw [Real.dist_eq]
      unfold productMalcevEdge
      refine le_min (le_max_right _ _) ?_
      rw [abs_sub_comm]
      exact le_max_right _ _)
  simpa only [Real.dist_eq, hx, hy] using hsum

theorem heisenbergQuotientDistance_le_product (g h : HeisenbergPoint × ℝ) :
    heisenbergQuotientDistance g.1 h.1 ≤ heisenbergProductQuotientDistance g h := by
  apply le_csInf (productRepresentativeDistances_nonempty g h)
  rintro _ ⟨u, v, w, b, rfl⟩
  unfold heisenbergQuotientDistance
  let h' := heisenbergMul h.1 ((u : ℝ), (v : ℝ), (w : ℝ))
  calc
    _ ≤ heisenbergGroupDistance g.1 h' := by
      apply csInf_le
      · exact ⟨0, fun z hz => by
          obtain ⟨a, c, d, rfl⟩ := hz
          apply le_csInf
          · let x : ℕ → HeisenbergPoint :=
              fun i => if i = 0 then g.1 else heisenbergMul h.1 ((a : ℝ), (c : ℝ), (d : ℝ))
            exact ⟨_, 1, x, by simp [x], by simp [x], rfl⟩
          · rintro _ ⟨n, x, _, _, rfl⟩
            exact malcevCoordinateChain_nonneg n x⟩
      · exact ⟨u, v, w, rfl⟩
    _ ≤ heisenbergProductGroupDistance g (h', h.2 + b) :=
      heisenbergGroupDistance_le_product g (h', h.2 + b)

theorem circleDist_le_heisenbergProductQuotientDistance (g h : HeisenbergPoint × ℝ) :
    dist (g.2 : Circle) (h.2 : Circle) ≤ heisenbergProductQuotientDistance g h := by
  apply le_csInf (productRepresentativeDistances_nonempty g h)
  rintro _ ⟨u, v, w, b, rfl⟩
  have hcast : ((h.2 + (b : ℝ) : ℝ) : Circle) = (h.2 : Circle) := by
    rw [AddCircle.coe_add]
    simp
  rw [← hcast]
  rw [dist_eq_norm, ← AddCircle.coe_sub]
  exact (torusNorm_le_abs _).trans (abs_sub_le_heisenbergProductGroupDistance g
    (heisenbergMul h.1 ((u : ℝ), (v : ℝ), (w : ℝ)), h.2 + b))

private theorem phase_neg_eq_fourier (u : ℝ) :
    phase (-u) = fourier (T := 1) (-1) (u : Circle) := by
  rw [fourier_coe_apply, phase]
  congr 1
  push_cast
  ring

/-- The twisted test descends along both right lattice actions. -/
theorem heisenbergTwist_productLatticeInvariant (Φ : HeisenbergPoint → ℂ) (U : ℝ)
    (hΦ : HeisenbergLipschitzNormLE Φ U) (g : HeisenbergPoint × ℝ) (u v w b : ℤ) :
    Φ (heisenbergMul g.1 ((u : ℝ), (v : ℝ), (w : ℝ))) * phase (-(g.2 + b)) =
      Φ g.1 * phase (-g.2) := by
  rw [hΦ.1, phase_neg_eq_fourier, phase_neg_eq_fourier, AddCircle.coe_add]
  have hb : ((b : ℝ) : Circle) = 0 := by
    exact (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨b, by simp⟩
  rw [hb, add_zero]

/-- The product twist increases the Lipschitz bound by at most a fixed factor.
Both constants are with respect to the precise Mal'cev chain formula. -/
theorem heisenbergTwist_productLipschitzBound :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ (Φ : HeisenbergPoint → ℂ) (U : ℝ),
      HeisenbergLipschitzNormLE Φ U →
      ∃ S M : ℝ, 0 ≤ S ∧ 0 ≤ M ∧ S + M ≤ L * U ∧
        (∀ g : HeisenbergPoint × ℝ, ‖Φ g.1 * phase (-g.2)‖ ≤ S) ∧
        (∀ g h : HeisenbergPoint × ℝ,
          ‖Φ g.1 * phase (-g.2) - Φ h.1 * phase (-h.2)‖ ≤
            M * heisenbergProductQuotientDistance g h) := by
  obtain ⟨C, hC⟩ := exists_lipschitzWith_fourier (-1)
  have hC₀ : 0 ≤ (C : ℝ) := C.coe_nonneg
  refine ⟨1 + C, by linarith, ?_⟩
  intro Φ U hΦ
  obtain ⟨_, S, M, hS, hM, hSM, hsup, hdist⟩ := hΦ
  refine ⟨S, M + S*C, hS, by positivity, ?_,
    fun g => by simpa [norm_mul, norm_phase] using hsup g.1, ?_⟩
  · have hSU : S ≤ U := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hSU hC₀]
  · intro g h
    let D := heisenbergProductQuotientDistance g h
    have h1 : ‖Φ g.1 - Φ h.1‖ ≤ M * D :=
      (hdist _ _).trans (mul_le_mul_of_nonneg_left
        (heisenbergQuotientDistance_le_product g h) hM)
    have h2 : ‖phase (-g.2) - phase (-h.2)‖ ≤ (C : ℝ) * D := by
      rw [phase_neg_eq_fourier, phase_neg_eq_fourier, ← dist_eq_norm]
      exact (hC.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left
        (circleDist_le_heisenbergProductQuotientDistance g h) hC₀)
    have hdecomp : Φ g.1 * phase (-g.2) - Φ h.1 * phase (-h.2) =
        (Φ g.1 - Φ h.1) * phase (-g.2) + Φ h.1 * (phase (-g.2) - phase (-h.2)) := by
      ring
    rw [hdecomp]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_phase, mul_one]
    calc
      _ ≤ M * D + S * ((C : ℝ) * D) := by
        apply add_le_add h1
        exact mul_le_mul (hsup _) h2 (norm_nonneg _) hS
      _ = (M + S*C) * D := by ring

end
end NilBohr
