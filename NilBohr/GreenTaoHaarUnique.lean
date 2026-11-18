import NilBohr.GreenTaoProductHaarAmbient

/-! Uniqueness of the normalized invariant probability on the Heisenberg quotients. -/

open MeasureTheory Set Function
open scoped ENNReal

namespace NilBohr

/-- A measurable fundamental domain of mass one determines every invariant
quotient probability.
The proof lifts the probability by counting measure on the discrete fibers. -/
private theorem invariantQuotientProbability_eq {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [PolishSpace G]
    [MeasurableSpace G] [BorelSpace G] {Γ : Subgroup G} [Countable Γ]
    [T2Space (G ⧸ Γ)] [SecondCountableTopology (G ⧸ Γ)]
    [MeasurableSpace (G ⧸ Γ)] [BorelSpace (G ⧸ Γ)]
    (ν : Measure G) [SigmaFinite ν] [ν.IsMulLeftInvariant]
    (D : Set G) (hD : MeasurableSet D)
    (hrep : ∀ g : G, ∃! γ : Γ.op, γ • g ∈ D) (hνD : ν D = 1)
    (μ : Measure (G ⧸ Γ)) [IsProbabilityMeasure μ]
    (hμ : ∀ a : G, MeasurePreserving (fun q : G ⧸ Γ => a • q) μ μ) :
    μ = (ν.restrict D).map (QuotientGroup.mk : G → G ⧸ Γ) := by
  classical
  let π : G → G ⧸ Γ := QuotientGroup.mk
  have hπ : Continuous π := QuotientGroup.continuous_mk
  have hinj : InjOn π D := by
    intro x hx y hy hxy
    have hxy' : x⁻¹ * y ∈ Γ := QuotientGroup.eq.mp hxy
    let γ : Γ.op := ⟨MulOpposite.op (x⁻¹ * y), hxy'⟩
    have hγy : γ • x = y := by
      change x * (x⁻¹ * y) = y
      simp
    have hγD : γ • x ∈ D := hγy.symm ▸ hy
    have h1 : (1 : Γ.op) • x ∈ D := by simpa using hx
    have hγ1 := (hrep x).unique hγD h1
    calc
      x = (1 : Γ.op) • x := (one_smul _ _).symm
      _ = γ • x := by rw [hγ1]
      _ = y := hγy
  have hsurj : Surjective (D.restrict π) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective (s := Γ) q
    obtain ⟨γ, hγ, -⟩ := hrep x
    refine ⟨⟨γ • x, hγ⟩, ?_⟩
    exact QuotientGroup.mk_mul_of_mem _ γ.prop
  let e := Equiv.ofBijective (D.restrict π) ⟨injOn_iff_injective.mp hinj, hsurj⟩
  have he : MeasurableEmbedding e := hπ.continuousOn.measurableEmbedding hD hinj
  let s : G ⧸ Γ → G := Subtype.val ∘ e.symm
  have hs : Measurable s := measurable_subtype_coe.comp (fun A hA => by
    rw [← e.image_eq_preimage]
    exact he.measurableSet_image.mpr hA)
  have hsD (q : G ⧸ Γ) : s q ∈ D := (e.symm q).prop
  have hπs (q : G ⧸ Γ) : π (s q) = q := e.apply_symm_apply q
  let shift (γ : Γ) (q : G ⧸ Γ) : G := s q * (γ : G)
  have hm (γ : Γ) : Measurable (shift γ) := hs.mul_const _
  have hπshift (γ : Γ) (q : G ⧸ Γ) : π (shift γ q) = q :=
    (QuotientGroup.mk_mul_of_mem _ γ.prop).trans (hπs q)
  let lift : Measure G := Measure.sum (fun γ : Γ => Measure.map (shift γ) μ)
  have lift_apply (A : Set G) (hA : MeasurableSet A) :
      lift A = ∫⁻ q, ∑' γ : Γ, A.indicator 1 (shift γ q) ∂μ := by
    have hAshift (γ : Γ) : Measurable (fun q => A.indicator (1 : G → ℝ≥0∞) (shift γ q)) :=
      (measurable_one.indicator hA).comp (hm γ)
    rw [Measure.sum_apply _ hA, lintegral_tsum (fun γ => (hAshift γ).aemeasurable)]
    apply tsum_congr
    intro γ
    rw [Measure.map_apply (hm γ) hA, ← lintegral_indicator_one ((hm γ) hA)]
    congr 1
  haveI : lift.IsMulLeftInvariant := by
    constructor
    intro a
    have ha : Measurable (fun x : G => a * x) := measurable_const.mul measurable_id
    ext A hA
    rw [Measure.map_apply ha hA, lift_apply _ (ha hA), lift_apply A hA]
    let F : G ⧸ Γ → ℝ≥0∞ := fun q => ∑' γ : Γ, A.indicator 1 (shift γ q)
    have hF : Measurable F :=
      Measurable.ennreal_tsum fun γ => (measurable_one.indicator hA).comp (hm γ)
    rw [← (hμ a).lintegral_comp hF]
    apply lintegral_congr
    intro q
    have hπa : π (a * s q) = a • q := by
      change a • π (s q) = a • q
      rw [hπs]
    let δ : Γ := ⟨(s (a • q))⁻¹ * (a * s q),
      QuotientGroup.eq.mp ((hπs (a • q)).trans hπa.symm)⟩
    have hδ : s (a • q) * δ.val = a * s q := by simp [δ]
    calc
      _ = ∑' γ : Γ, A.indicator 1 (shift (δ * γ) (a • q)) := by
        apply tsum_congr
        intro γ
        have hprod : shift (δ * γ) (a • q) = a * shift γ q := by
          change s (a • q) * ((δ : G) * (γ : G)) = a * (s q * (γ : G))
          rw [← mul_assoc, hδ, mul_assoc]
        simp [hprod, indicator_apply]
      _ = ∑' γ : Γ, A.indicator 1 (shift γ (a • q)) :=
        (Equiv.mulLeft δ).tsum_eq (fun γ : Γ => A.indicator 1 (shift γ (a • q)))
  let tile (δ : Γ) : Set G := (fun x : G => x * (δ : G)) '' D
  have htile (δ : Γ) : MeasurableSet (tile δ) := by
    have heq : tile δ = (fun x : G => x * (δ : G)⁻¹) ⁻¹' D := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
      · intro hx
        exact ⟨x * (δ : G)⁻¹, hx, by simp [mul_assoc]⟩
    rw [heq]
    exact (measurable_id.mul_const _) hD
  have hshift_tile (γ δ : Γ) (q : G ⧸ Γ) : shift γ q ∈ tile δ ↔ γ = δ := by
    constructor
    · rintro ⟨y, hy, hyγ⟩
      have hπy : π y = q := by
        rw [← hπshift γ q, ← hyγ]
        exact (QuotientGroup.mk_mul_of_mem _ δ.prop).symm
      have hy' : y = s q := hinj hy (hsD q) (hπy.trans (hπs q).symm)
      rw [hy'] at hyγ
      exact Subtype.ext (mul_left_cancel hyγ.symm)
    · rintro rfl
      exact ⟨s q, hsD q, rfl⟩
  have lift_tile (δ : Γ) : lift (tile δ) = 1 := by
    rw [Measure.sum_apply _ (htile δ)]
    calc
      (∑' γ : Γ, (Measure.map (shift γ) μ) (tile δ)) =
          ∑' γ : Γ, if γ = δ then 1 else 0 := by
        apply tsum_congr
        intro γ
        rw [Measure.map_apply (hm γ) (htile δ)]
        by_cases h : γ = δ
        · have hpre : shift γ ⁻¹' tile δ = univ :=
            Set.eq_univ_of_forall fun q => (hshift_tile γ δ q).mpr h
          rw [hpre, if_pos h, measure_univ]
        · have hpre : shift γ ⁻¹' tile δ = ∅ :=
            Set.eq_empty_iff_forall_not_mem.mpr fun q hq => h ((hshift_tile γ δ q).mp hq)
          simp [hpre, h]
      _ = 1 := by simp
  haveI : SigmaFinite lift := by
    apply Measure.sigmaFinite_of_countable (S := range tile) (countable_range tile)
    · rintro A ⟨δ, rfl⟩
      simp [lift_tile]
    · apply eq_univ_of_forall
      intro x
      let δ : Γ := ⟨(s (π x))⁻¹ * x, QuotientGroup.eq.mp (hπs (π x))⟩
      have hx : s (π x) * δ.val = x := by simp [δ]
      exact mem_sUnion.mpr ⟨tile δ, mem_range_self δ, s (π x), hsD (π x), hx⟩
  have htile1 : tile 1 = D := by
    change (fun x : G => x * 1) '' D = D
    simp
  have hliftD : lift D = 1 := by rw [← htile1, lift_tile]
  have hliftν : lift = ν := by
    simpa [hliftD, hνD] using
      (measure_eq_div_smul lift ν (s := D) (by simp [hνD]) (by simp [hνD]))
  ext A hA
  rw [Measure.map_apply hπ.measurable hA, Measure.restrict_apply (hπ.measurable hA), ← hliftν]
  have hmAD := (hπ.measurable hA).inter hD
  rw [lift_apply _ hmAD, ← lintegral_indicator_one hA]
  apply lintegral_congr
  intro q
  have hcollapse : (∑' γ : Γ, (π ⁻¹' A ∩ D).indicator (1 : G → ℝ≥0∞) (shift γ q)) =
      (π ⁻¹' A ∩ D).indicator (1 : G → ℝ≥0∞) (shift 1 q) := by
    apply tsum_eq_single 1
    intro γ hγ
    have hq : shift γ q ∉ D := by
      rw [← htile1]
      exact fun hq => hγ ((hshift_tile γ 1 q).mp hq)
    simp [indicator_apply, hq]
  have hshift1 : shift 1 q = s q := mul_one _
  have hone : (π ⁻¹' A ∩ D).indicator (1 : G → ℝ≥0∞) (shift 1 q) = A.indicator (1 : (G ⧸ Γ) → ℝ≥0∞) q := by
    simp [hshift1, indicator_apply, hπs q, hsD q]
  exact (hcollapse.trans hone).symm

/-- The scalar chart measure is the unique invariant Borel probability. -/
theorem heisenbergNilmanifoldMeasure_unique (μ : Measure HeisenbergNilmanifold)
    [IsProbabilityMeasure μ]
    (hμ : ∀ a : HeisenbergGroup,
      MeasurePreserving (fun q : HeisenbergNilmanifold => a • q) μ μ) :
    μ = heisenbergNilmanifoldMeasure := by
  letI : Countable HeisenbergGroup.lattice := countable_of_Lindelof_of_discrete
  rw [heisenbergNilmanifoldMeasure_eq_fundamentalDomainPushforward]
  exact invariantQuotientProbability_eq heisenbergAmbientMeasure heisenbergFundamentalCube
    heisenbergFundamentalCube_measurable existsUnique_heisenbergFundamentalCube_right
    heisenbergFundamentalCube_mass μ hμ

/-- The product chart measure is the unique invariant Borel probability. -/
theorem heisenbergProductNilmanifoldMeasure_unique (μ : Measure HeisenbergProductNilmanifold)
    [IsProbabilityMeasure μ]
    (hμ : ∀ a : HeisenbergProductGroup,
      MeasurePreserving (fun q : HeisenbergProductNilmanifold => a • q) μ μ) :
    μ = heisenbergProductNilmanifoldMeasure := by
  letI : PolishSpace HeisenbergProductGroup :=
    heisenbergProductCoordinatesHomeomorph.isClosedEmbedding.polishSpace
  letI : SecondCountableTopology HeisenbergProductNilmanifold :=
    heisenbergProductNilmanifoldHomeomorph.secondCountableTopology
  letI : Countable heisenbergProductLattice := countable_of_Lindelof_of_discrete
  letI : SigmaFinite heisenbergProductAmbientMeasure := by
    unfold heisenbergProductAmbientMeasure
    infer_instance
  rw [heisenbergProductNilmanifoldMeasure_eq_fundamentalDomainPushforward]
  exact invariantQuotientProbability_eq heisenbergProductAmbientMeasure heisenbergProductFundamentalCube
    heisenbergProductFundamentalCube_measurable existsUnique_heisenbergProductFundamentalCube_right
    heisenbergProductFundamentalCube_mass μ hμ

end NilBohr
