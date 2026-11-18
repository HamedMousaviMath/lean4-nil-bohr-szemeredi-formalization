import NilBohr.GreenTaoTopology
import NilBohr.GreenTaoCoordinateIndex
import NilBohr.MalcevChainMetric
import NilBohr.GreenTaoQuotientMetric

/-! The Heisenberg chain metric and its topology on the group and right-coset quotient. -/

namespace NilBohr
noncomputable section

private def scalarMalcevEdge (g h : HeisenbergPoint) : ℝ :=
  min
    (heisenbergMalcevNorm (heisenbergMul g (heisenbergInv h)))
    (heisenbergMalcevNorm (heisenbergMul h (heisenbergInv g)))

private theorem scalarMalcevEdge_y (g h : HeisenbergPoint) :
    |g.2.1 - h.2.1| ≤ scalarMalcevEdge g h := by
  have one (u v : HeisenbergPoint) :
      |u.2.1 - v.2.1| ≤ heisenbergMalcevNorm (heisenbergMul u (heisenbergInv v)) := by
    simp only [heisenbergMalcevNorm, heisenbergMul, heisenbergInv, sub_eq_add_neg]
    exact (le_max_left _ _).trans (le_max_right _ _)
  exact le_min (one g h) ((abs_sub_comm _ _).le.trans (one h g))

private theorem scalarMalcevEdge_nonneg (g h : HeisenbergPoint) : 0 ≤ scalarMalcevEdge g h :=
  (abs_nonneg _).trans (scalarMalcevEdge_y _ _)

private theorem malcev_vertical_eq (x y : HeisenbergPoint) :
    (heisenbergMul x (heisenbergInv y)).2.2 -
      (heisenbergMul x (heisenbergInv y)).1 * (heisenbergMul x (heisenbergInv y)).2.1 =
      (x.2.2 - y.2.2) - (x.1 - y.1) * x.2.1 := by
  simp only [heisenbergMul, heisenbergInv]
  ring

private theorem scalarMalcevEdge_z (g h : HeisenbergPoint) (Y : ℝ)
    (hg : |g.2.1| ≤ Y) (hh : |h.2.1| ≤ Y) :
    |g.2.2 - h.2.2| ≤ scalarMalcevEdge g h * (1 + Y) := by
  have one (u v : HeisenbergPoint) (hu : |u.2.1| ≤ Y) :
      |u.2.2 - v.2.2| ≤ (heisenbergMalcevNorm (heisenbergMul u (heisenbergInv v))) * (1 + Y) := by
    let E := heisenbergMalcevNorm (heisenbergMul u (heisenbergInv v))
    have hₓ : |u.1 - v.1| ≤ E := by
      dsimp [E, heisenbergMalcevNorm, heisenbergMul, heisenbergInv]
      exact le_max_left _ _
    have h𝓏 : |(u.2.2 - v.2.2) - (u.1 - v.1) * u.2.1| ≤ E := by
      rw [← malcev_vertical_eq]
      exact (le_max_right _ _).trans (le_max_right _ _)
    calc
      _ = |((u.2.2 - v.2.2) - (u.1 - v.1) * u.2.1) + (u.1 - v.1) * u.2.1| := by
        rw [sub_add_cancel]
      _ ≤ |(u.2.2 - v.2.2) - (u.1 - v.1) * u.2.1| + |(u.1 - v.1) * u.2.1| := by
        exact abs_add_le _ _
      _ ≤ E + E * Y := by
        rw [abs_mul]
        exact add_le_add h𝓏 (mul_le_mul hₓ hu (abs_nonneg _) ((abs_nonneg _).trans hₓ))
      _ = _ := by ring
  unfold scalarMalcevEdge
  rw [min_mul_of_nonneg _ _ (by linarith [abs_nonneg g.2.1])]
  exact le_min (one g h hg) ((abs_sub_comm _ _).le.trans (one h g hh))

/-- The total Mal'cev chain length controls the vertical coordinate
quadratically along every finite chain. -/
private theorem heisenberg_chain_vertical_le (x : ℕ → HeisenbergPoint) (n : ℕ) :
    let L := ∑ i ∈ Finset.range n, scalarMalcevEdge (x i) (x (i+1))
    |(x 0).2.2 - (x n).2.2| ≤ L * (1 + |(x 0).2.1| + L) := by
  let E (i : ℕ) := scalarMalcevEdge (x i) (x (i+1))
  let L := ∑ i ∈ Finset.range n, E i
  have hY (i : ℕ) (hi : i ≤ n) : |(x i).2.1| ≤ |(x 0).2.1| + L := by
    have h1 := dist_le_range_sum_of_dist_le (f := fun j => (x j).2.1) i
      (d := E) (fun j => by
        rw [Real.dist_eq]
        exact scalarMalcevEdge_y _ _)
    rw [Real.dist_eq, abs_sub_comm] at h1
    have h2 : (∑ j ∈ Finset.range i, E j) ≤ L :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hi)
        (fun j _ _ => scalarMalcevEdge_nonneg _ _)
    calc
      _ = |(x 0).2.1 + ((x i).2.1 - (x 0).2.1)| := by congr 1; ring
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add_left (h1.trans h2) _)
  calc
    |(x 0).2.2 - (x n).2.2| ≤ ∑ i ∈ Finset.range n, dist (x i).2.2 (x (i+1)).2.2 := by
      rw [← Real.dist_eq]
      exact dist_le_range_sum_dist (fun i => (x i).2.2) n
    _ ≤ ∑ i ∈ Finset.range n, E i * (1 + |(x 0).2.1| + L) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [Real.dist_eq, add_assoc]
      have hin := Finset.mem_range.mp hi
      exact scalarMalcevEdge_z _ _ _ (hY i hin.le) (hY (i+1) hin)
    _ = L * (1 + |(x 0).2.1| + L) := by rw [← Finset.sum_mul]

private theorem scalarMalcevEdge_x (g h : HeisenbergPoint) :
    |g.1 - h.1| ≤ scalarMalcevEdge g h := by
  have one (u v : HeisenbergPoint) :
      |u.1 - v.1| ≤ heisenbergMalcevNorm (heisenbergMul u (heisenbergInv v)) := by
    simp only [heisenbergMalcevNorm, heisenbergMul, heisenbergInv, sub_eq_add_neg]
    exact le_max_left _ _
  exact le_min (one g h) ((abs_sub_comm _ _).le.trans (one h g))


private theorem scalarMalcevEdge_coord (g h : HeisenbergGroup) :
    scalarMalcevEdge (HeisenbergGroup.coordinates g) (HeisenbergGroup.coordinates h) =
      malcevEdge heisenbergMalcevFinCoordinates g h := by
  simp [scalarMalcevEdge, malcevEdge, norm_heisenbergMalcevFinCoordinates]

theorem malcevGroupChainDistance_eq_heisenbergGroupDistance (g h : HeisenbergGroup) :
    malcevGroupChainDistance heisenbergMalcevFinCoordinates g h =
      heisenbergGroupDistance (HeisenbergGroup.coordinates g) (HeisenbergGroup.coordinates h) := by
  change chainDistance (malcevEdge heisenbergMalcevFinCoordinates) g h =
    chainDistance scalarMalcevEdge _ _
  apply le_antisymm
  · have H := chainDistance_map_le (edge := scalarMalcevEdge)
      HeisenbergGroup.coordinates.symm (malcevEdge_nonneg heisenbergMalcevFinCoordinates)
      (fun x y => by
        rw [← scalarMalcevEdge_coord]
        simp) (HeisenbergGroup.coordinates g) (HeisenbergGroup.coordinates h)
    simpa using H
  · exact chainDistance_map_le HeisenbergGroup.coordinates scalarMalcevEdge_nonneg
      (fun x y => (scalarMalcevEdge_coord x y).le) g h

theorem heisenbergGroupDistance_le_directed (g h : HeisenbergPoint) :
    heisenbergGroupDistance g h ≤ heisenbergMalcevNorm (heisenbergMul g (heisenbergInv h)) :=
  (chainDistance_le_edge scalarMalcevEdge_nonneg g h).trans (min_le_left _ _)

/-- Small chain distance controls the ordinary coordinate distance locally. -/
theorem heisenbergDist_lt_of_groupDistance_lt {g h : HeisenbergPoint} {ε : ℝ}
    (hc : heisenbergGroupDistance g h < min (min 1 ε) (ε / (2 + |g.2.1|))) :
    dist g h < ε := by
  obtain ⟨_, ⟨n, x, hx, hy, rfl⟩, hL⟩ :=
    chainDistance_exists_length_lt (edge := scalarMalcevEdge) hc
  let L := ∑ i ∈ Finset.range n, scalarMalcevEdge (x i) (x (i+1))
  change L < min (min 1 ε) (ε / (2 + |g.2.1|)) at hL
  have hL0 : 0 ≤ L := Finset.sum_nonneg fun _ _ => scalarMalcevEdge_nonneg _ _
  have hL1 : L < 1 := hL.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hLε : L < ε := hL.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hLz : L * (2 + |g.2.1|) < ε := (lt_div_iff₀ (by positivity)).mp
    (hL.trans_le (min_le_right _ _))
  have horizontal (f : HeisenbergPoint → ℝ)
      (he : ∀ p q, |f p - f q| ≤ scalarMalcevEdge p q) : dist (f g) (f h) < ε := by
    rw [← hx, ← hy]
    refine lt_of_le_of_lt (dist_le_range_sum_of_dist_le (f := fun i => f (x i)) n
      (fun _ => by rw [Real.dist_eq]; exact he _ _)) hLε
  have hZ := heisenberg_chain_vertical_le x n
  change |(x 0).2.2 - (x n).2.2| ≤ L * (1 + |(x 0).2.1| + L) at hZ
  rw [hx, hy] at hZ
  rw [Prod.dist_eq, max_lt_iff, Prod.dist_eq, max_lt_iff]
  refine ⟨horizontal Prod.fst scalarMalcevEdge_x,
    horizontal (fun p => p.2.1) scalarMalcevEdge_y, ?_⟩
  rw [Real.dist_eq]
  exact (hZ.trans (mul_le_mul_of_nonneg_left (by linarith only [hL1]) hL0)).trans_lt hLz

theorem heisenbergGroupDistance_small_radius_pos (g : HeisenbergPoint) {ε : ℝ} (hε : 0 < ε) :
    0 < min (min 1 ε) (ε / (2 + |g.2.1|)) :=
  lt_min (lt_min zero_lt_one hε) (div_pos hε (by positivity))

private theorem continuous_heisenberg_relative_norm (g : HeisenbergPoint) :
    Continuous (fun h => heisenbergMalcevNorm (heisenbergMul g (heisenbergInv h))) := by
  unfold heisenbergMalcevNorm heisenbergMul heisenbergInv
  fun_prop

theorem heisenberg_relative_norm_self (g : HeisenbergPoint) :
    heisenbergMalcevNorm (heisenbergMul g (heisenbergInv g)) = 0 := by
  let G := HeisenbergGroup.coordinates.symm g
  have h : heisenbergMul g (heisenbergInv g) = HeisenbergGroup.coordinates 1 := by
    simpa [G] using (HeisenbergGroup.coordinates_mul G G⁻¹).symm.trans
      (congrArg HeisenbergGroup.coordinates (mul_inv_cancel G))
  rw [h]
  simp [heisenbergMalcevNorm, HeisenbergGroup.coordinates]

/-- An ordinary coordinate neighborhood fits inside every positive-radius chain ball. -/
theorem heisenbergGroupDistance_lt_of_dist_lt (g : HeisenbergPoint) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ h : HeisenbergPoint, dist g h < δ → heisenbergGroupDistance g h < ε := by
  obtain ⟨δ, hδ, hD⟩ := Metric.continuousAt_iff.mp
    (continuous_heisenberg_relative_norm g).continuousAt ε hε
  refine ⟨δ, hδ, fun h hh => (heisenbergGroupDistance_le_directed g h).trans_lt ?_⟩
  have hh' := hD (dist_comm g h ▸ hh)
  rw [heisenberg_relative_norm_self, Real.dist_eq, sub_zero] at hh'
  exact (le_abs_self _).trans_lt hh'

private theorem heisenbergGroupDistance_isOpen (s : Set HeisenbergPoint) :
    IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, ∀ y, heisenbergGroupDistance x y < ε → y ∈ s := by
  rw [Metric.isOpen_iff]
  constructor
  · intro hs g hg
    obtain ⟨ε, hε, hB⟩ := hs g hg
    exact ⟨_, heisenbergGroupDistance_small_radius_pos g hε, fun h hh =>
      hB (by simpa only [Metric.mem_ball, dist_comm] using
        heisenbergDist_lt_of_groupDistance_lt hh)⟩
  · intro hs g hg
    obtain ⟨ε, hε, hB⟩ := hs g hg
    obtain ⟨δ, hδ, hD⟩ := heisenbergGroupDistance_lt_of_dist_lt g hε
    exact ⟨δ, hδ, fun h hh => hB h
      (hD h (by simpa only [Metric.mem_ball, dist_comm] using hh))⟩

theorem heisenbergGroupDistance_eq_zero_iff (g h : HeisenbergPoint) :
    heisenbergGroupDistance g h = 0 ↔ g = h := by
  constructor
  · intro hD
    by_contra hne
    have hp : 0 < dist g h := dist_pos.mpr hne
    exact (lt_irrefl _) (heisenbergDist_lt_of_groupDistance_lt
      (g := g) (h := h) (ε := dist g h)
      (hD ▸ heisenbergGroupDistance_small_radius_pos g hp))
  · rintro rfl
    exact chainDistance_self scalarMalcevEdge_nonneg g

private theorem scalarMalcevEdge_comm (g h : HeisenbergPoint) :
    scalarMalcevEdge g h = scalarMalcevEdge h g :=
  min_comm _ _

/-- The group chain distance is a metric with the ordinary matrix topology. -/
def heisenbergGroupMetric : MetricSpace HeisenbergGroup :=
  MetricSpace.ofDistTopology
    (fun g h => heisenbergGroupDistance (HeisenbergGroup.coordinates g) (HeisenbergGroup.coordinates h))
    (fun g => chainDistance_self scalarMalcevEdge_nonneg (HeisenbergGroup.coordinates g))
    (fun g h => chainDistance_comm scalarMalcevEdge_comm (HeisenbergGroup.coordinates g)
      (HeisenbergGroup.coordinates h))
    (fun g h k => chainDistance_triangle scalarMalcevEdge_nonneg (HeisenbergGroup.coordinates g)
      (HeisenbergGroup.coordinates h) (HeisenbergGroup.coordinates k))
    (fun s => by
      let e := HeisenbergGroup.coordinatesHomeomorph
      rw [← e.symm.isOpen_preimage, heisenbergGroupDistance_isOpen]
      constructor
      · intro hs g hg
        obtain ⟨ε, hε, hB⟩ := hs (e g) (by simpa [e] using hg)
        exact ⟨ε, hε, fun h hh => by simpa [e] using hB (e h) hh⟩
      · intro hs g hg
        obtain ⟨ε, hε, hB⟩ := hs (e.symm g) hg
        exact ⟨ε, hε, fun h hh => hB (e.symm h)
          (by simpa [e] using hh)⟩)
    (fun _ _ h => HeisenbergGroup.coordinates.injective
      ((heisenbergGroupDistance_eq_zero_iff _ _).mp h))

theorem heisenbergGroupMetric_dist_eq_chain (g h : HeisenbergGroup) :
    @dist HeisenbergGroup heisenbergGroupMetric.toDist g h =
      malcevGroupChainDistance heisenbergMalcevFinCoordinates g h :=
  (malcevGroupChainDistance_eq_heisenbergGroupDistance g h).symm

theorem heisenbergGroupMetric_right (g h z : HeisenbergGroup) :
    @dist HeisenbergGroup heisenbergGroupMetric.toDist (g*z) (h*z) =
      @dist HeisenbergGroup heisenbergGroupMetric.toDist g h := by
  simp only [heisenbergGroupMetric_dist_eq_chain, malcevGroupChainDistance_right]

/-- The Green–Tao metric on the real Heisenberg right-coset nilmanifold. -/
def heisenbergNilmanifoldMetric : MetricSpace (HeisenbergGroup ⧸ HeisenbergGroup.lattice) := by
  letI := heisenbergGroupMetric
  exact rightInvariantQuotientMetric HeisenbergGroup.lattice heisenbergGroupMetric_right
    HeisenbergGroup.isClosed_lattice

theorem heisenbergNilmanifoldMetric_topology :
    heisenbergNilmanifoldMetric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace (HeisenbergGroup ⧸ HeisenbergGroup.lattice)) :=
  rfl

theorem heisenbergNilmanifoldMetric_dist_eq_chain (g h : HeisenbergGroup) :
    @dist (HeisenbergGroup ⧸ HeisenbergGroup.lattice) heisenbergNilmanifoldMetric.toDist
      (g : HeisenbergGroup ⧸ HeisenbergGroup.lattice)
      (h : HeisenbergGroup ⧸ HeisenbergGroup.lattice) =
      malcevQuotientChainDistance HeisenbergGroup.lattice heisenbergMalcevFinCoordinates g h := by
  letI := heisenbergGroupMetric
  change (sInf (Set.range fun γ : HeisenbergGroup.lattice => dist g (h * γ))) = _
  simp only [malcevQuotientChainDistance, heisenbergGroupMetric_dist_eq_chain]

theorem malcevQuotientChainDistance_eq_heisenbergQuotientDistance (g h : HeisenbergGroup) :
    malcevQuotientChainDistance HeisenbergGroup.lattice heisenbergMalcevFinCoordinates g h =
      heisenbergQuotientDistance (HeisenbergGroup.coordinates g) (HeisenbergGroup.coordinates h) := by
  unfold malcevQuotientChainDistance heisenbergQuotientDistance
  congr 1
  ext L
  constructor
  · rintro ⟨⟨γ, u, v, w, rfl⟩, rfl⟩
    refine ⟨u, v, w, ?_⟩
    dsimp only
    rw [malcevGroupChainDistance_eq_heisenbergGroupDistance]
    rfl
  · rintro ⟨u, v, w, rfl⟩
    refine ⟨⟨⟨u,v,w⟩, u,v,w,rfl⟩, ?_⟩
    dsimp only
    rw [malcevGroupChainDistance_eq_heisenbergGroupDistance]
    rfl

end
end NilBohr
