import NilBohr.GreenTaoScalarMetric
import NilBohr.GreenTaoProductMetric
import NilBohr.GreenTaoProductTopology

/-! The product chain metric, its ordinary quotient topology, and its
identity with the abstract Green–Tao formula for each permitted basis order. -/

namespace NilBohr

noncomputable section

private theorem productMalcevEdge_nonneg (g h : HeisenbergPoint × ℝ) :
    0 ≤ productMalcevEdge g h := by
  unfold productMalcevEdge
  exact le_min ((abs_nonneg _).trans (le_max_right _ _))
    ((abs_nonneg _).trans (le_max_right _ _))

private theorem productMalcevEdge_coord (d : ℕ) (g h : HeisenbergProductGroup) :
    productMalcevEdge (heisenbergProductCoordinates g) (heisenbergProductCoordinates h) =
      malcevEdge (heisenbergProductMalcevFinCoordinates d) g h := by
  rw [malcevEdge, norm_heisenbergProductMalcevFinCoordinates,
    norm_heisenbergProductMalcevFinCoordinates]
  rfl

theorem malcevGroupChainDistance_eq_heisenbergProductGroupDistance (d : ℕ)
    (g h : HeisenbergProductGroup) :
    malcevGroupChainDistance (heisenbergProductMalcevFinCoordinates d) g h =
      heisenbergProductGroupDistance (heisenbergProductCoordinates g)
        (heisenbergProductCoordinates h) := by
  change chainDistance (malcevEdge (heisenbergProductMalcevFinCoordinates d)) g h =
    chainDistance productMalcevEdge _ _
  apply le_antisymm
  · have H := chainDistance_map_le (edge := productMalcevEdge)
      heisenbergProductCoordinates.symm
      (malcevEdge_nonneg (heisenbergProductMalcevFinCoordinates d))
      (fun x y => by
        rw [← productMalcevEdge_coord]
        simp) (heisenbergProductCoordinates g) (heisenbergProductCoordinates h)
    simpa using H
  · exact chainDistance_map_le heisenbergProductCoordinates productMalcevEdge_nonneg
      (fun x y => (productMalcevEdge_coord d x y).le) g h

theorem heisenbergProductGroupDistance_le_directed (g h : HeisenbergPoint × ℝ) :
    heisenbergProductGroupDistance g h ≤
      max (heisenbergMalcevNorm (heisenbergMul g.1 (heisenbergInv h.1))) |g.2 - h.2| :=
  (chainDistance_le_edge productMalcevEdge_nonneg g h).trans (min_le_left _ _)

private theorem heisenbergProductDist_lt_of_groupDistance_lt {g h : HeisenbergPoint × ℝ}
    {ε : ℝ} (hc : heisenbergProductGroupDistance g h < min (min 1 ε) (ε / (2 + |g.1.2.1|))) :
    dist g h < ε := by
  rw [Prod.dist_eq, max_lt_iff, Real.dist_eq]
  constructor
  · exact heisenbergDist_lt_of_groupDistance_lt ((heisenbergGroupDistance_le_product g h).trans_lt hc)
  · exact (abs_sub_le_heisenbergProductGroupDistance g h).trans_lt
      (hc.trans_le ((min_le_left _ _).trans (min_le_right _ _)))

private theorem continuous_product_relative_norm (g : HeisenbergPoint × ℝ) :
    Continuous (fun h : HeisenbergPoint × ℝ =>
      max (heisenbergMalcevNorm (heisenbergMul g.1 (heisenbergInv h.1))) |g.2 - h.2|) := by
  unfold heisenbergMalcevNorm heisenbergMul heisenbergInv
  fun_prop

private theorem product_relative_norm_self (g : HeisenbergPoint × ℝ) :
    max (heisenbergMalcevNorm (heisenbergMul g.1 (heisenbergInv g.1))) |g.2 - g.2| = 0 := by
  simp [heisenberg_relative_norm_self]

private theorem heisenbergProductGroupDistance_lt_of_dist_lt (g : HeisenbergPoint × ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ h : HeisenbergPoint × ℝ,
      dist g h < δ → heisenbergProductGroupDistance g h < ε := by
  obtain ⟨δ, hδ, hD⟩ := Metric.continuousAt_iff.mp
    (continuous_product_relative_norm g).continuousAt ε hε
  refine ⟨δ, hδ, fun h hh => (heisenbergProductGroupDistance_le_directed g h).trans_lt ?_⟩
  have hh' := hD (dist_comm g h ▸ hh)
  rw [product_relative_norm_self, Real.dist_eq, sub_zero] at hh'
  exact (le_abs_self _).trans_lt hh'

private theorem heisenbergProductGroupDistance_isOpen (s : Set (HeisenbergPoint × ℝ)) :
    IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, ∀ y, heisenbergProductGroupDistance x y < ε → y ∈ s := by
  rw [Metric.isOpen_iff]
  constructor
  · intro hs g hg
    obtain ⟨ε, hε, hB⟩ := hs g hg
    exact ⟨_, heisenbergGroupDistance_small_radius_pos g.1 hε, fun h hh =>
      hB (by simpa only [Metric.mem_ball, dist_comm] using
        heisenbergProductDist_lt_of_groupDistance_lt hh)⟩
  · intro hs g hg
    obtain ⟨ε, hε, hB⟩ := hs g hg
    obtain ⟨δ, hδ, hD⟩ := heisenbergProductGroupDistance_lt_of_dist_lt g hε
    exact ⟨δ, hδ, fun h hh => hB h
      (hD h (by simpa only [Metric.mem_ball, dist_comm] using hh))⟩

theorem heisenbergProductGroupDistance_eq_zero_iff (g h : HeisenbergPoint × ℝ) :
    heisenbergProductGroupDistance g h = 0 ↔ g = h := by
  constructor
  · intro hD
    by_contra hne
    have hp : 0 < dist g h := dist_pos.mpr hne
    exact (lt_irrefl _) (heisenbergProductDist_lt_of_groupDistance_lt
      (g := g) (h := h) (ε := dist g h)
      (hD ▸ heisenbergGroupDistance_small_radius_pos g.1 hp))
  · rintro rfl
    exact chainDistance_self productMalcevEdge_nonneg g

private theorem productMalcevEdge_comm (g h : (HeisenbergPoint × ℝ)) :
    productMalcevEdge g h = productMalcevEdge h g :=
  min_comm _ _

/-- The group chain metric has the usual product topology. -/
def heisenbergProductGroupMetric : MetricSpace HeisenbergProductGroup :=
  MetricSpace.ofDistTopology
    (fun g h => heisenbergProductGroupDistance (heisenbergProductCoordinates g)
      (heisenbergProductCoordinates h))
    (fun g => chainDistance_self productMalcevEdge_nonneg (heisenbergProductCoordinates g))
    (fun g h => chainDistance_comm productMalcevEdge_comm (heisenbergProductCoordinates g)
      (heisenbergProductCoordinates h))
    (fun g h k => chainDistance_triangle productMalcevEdge_nonneg (heisenbergProductCoordinates g)
      (heisenbergProductCoordinates h) (heisenbergProductCoordinates k))
    (fun s => by
      let e := heisenbergProductCoordinatesHomeomorph
      rw [← e.symm.isOpen_preimage, heisenbergProductGroupDistance_isOpen]
      constructor
      · intro hs g hg
        obtain ⟨ε, hε, hB⟩ := hs (e g) (by simpa [e] using hg)
        exact ⟨ε, hε, fun h hh => by simpa [e] using hB (e h) hh⟩
      · intro hs g hg
        obtain ⟨ε, hε, hB⟩ := hs (e.symm g) hg
        exact ⟨ε, hε, fun h hh => hB (e.symm h)
          (by simpa [e] using hh)⟩)
    (fun _ _ h => heisenbergProductCoordinates.injective
      ((heisenbergProductGroupDistance_eq_zero_iff _ _).mp h))

theorem heisenbergProductGroupMetric_dist_eq_chain (d : ℕ) (g h : HeisenbergProductGroup) :
    @dist HeisenbergProductGroup heisenbergProductGroupMetric.toDist g h =
      malcevGroupChainDistance (heisenbergProductMalcevFinCoordinates d) g h :=
  (malcevGroupChainDistance_eq_heisenbergProductGroupDistance d g h).symm

theorem heisenbergProductGroupMetric_right (g h z : HeisenbergProductGroup) :
    @dist HeisenbergProductGroup heisenbergProductGroupMetric.toDist (g*z) (h*z) =
      @dist HeisenbergProductGroup heisenbergProductGroupMetric.toDist g h := by
  simp only [heisenbergProductGroupMetric_dist_eq_chain 1, malcevGroupChainDistance_right]

/-- The Green–Tao metric on the product right-coset nilmanifold. -/
def heisenbergProductNilmanifoldMetric : MetricSpace HeisenbergProductNilmanifold := by
  letI := heisenbergProductGroupMetric
  exact rightInvariantQuotientMetric heisenbergProductLattice heisenbergProductGroupMetric_right
    isClosed_heisenbergProductLattice

theorem heisenbergProductNilmanifoldMetric_topology :
    heisenbergProductNilmanifoldMetric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace HeisenbergProductNilmanifold) :=
  rfl

theorem heisenbergProductNilmanifoldMetric_dist_eq_chain (d : ℕ)
    (g h : HeisenbergProductGroup) :
    @dist HeisenbergProductNilmanifold heisenbergProductNilmanifoldMetric.toDist
      (g : HeisenbergProductNilmanifold) (h : HeisenbergProductNilmanifold) =
      malcevQuotientChainDistance heisenbergProductLattice
        (heisenbergProductMalcevFinCoordinates d) g h := by
  letI := heisenbergProductGroupMetric
  change (sInf (Set.range fun γ : heisenbergProductLattice => dist g (h * γ))) = _
  simp only [malcevQuotientChainDistance, heisenbergProductGroupMetric_dist_eq_chain d]

theorem malcevQuotientChainDistance_eq_heisenbergProductQuotientDistance (d : ℕ)
    (g h : HeisenbergProductGroup) :
    malcevQuotientChainDistance heisenbergProductLattice (heisenbergProductMalcevFinCoordinates d) g h =
      heisenbergProductQuotientDistance (heisenbergProductCoordinates g)
        (heisenbergProductCoordinates h) := by
  unfold malcevQuotientChainDistance heisenbergProductQuotientDistance
  congr 1
  ext L
  constructor
  · rintro ⟨⟨γ, hγ⟩, rfl⟩
    obtain ⟨⟨u, v, w, hg⟩, b, hb⟩ := (heisenbergProductLattice_mem_iff γ).mp hγ
    refine ⟨u, v, w, b, ?_⟩
    dsimp only
    rw [malcevGroupChainDistance_eq_heisenbergProductGroupDistance]
    change heisenbergProductGroupDistance (heisenbergProductCoordinates g)
      (heisenbergMul (HeisenbergGroup.coordinates h.1) (HeisenbergGroup.coordinates γ.1),
        Multiplicative.toAdd h.2 + Multiplicative.toAdd γ.2) = _
    rw [hg, hb]
    rfl
  · rintro ⟨u, v, w, b, rfl⟩
    let γ : HeisenbergProductGroup := (⟨u,v,w⟩, Multiplicative.ofAdd (b : ℝ))
    have hγ : γ ∈ heisenbergProductLattice :=
      (heisenbergProductLattice_mem_iff γ).mpr ⟨⟨u,v,w,rfl⟩, b,rfl⟩
    refine ⟨⟨γ, hγ⟩, ?_⟩
    dsimp only
    rw [malcevGroupChainDistance_eq_heisenbergProductGroupDistance]
    rfl

end
end NilBohr
