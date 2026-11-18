import NilBohr.BohrPeriodic

/-! Simultaneous open-arc Bohr restrictions, including rational frequencies
and the selected-prime count normalization. -/

namespace NilBohr

open Filter MeasureTheory Polynomial Set
open scoped BigOperators Topology ENNReal

/-- A proper circle interval with an arbitrary choice at its endpoints.
The open arc fixes its interior, while membership in the closure permits
either endpoint convention. -/
structure CircleBohrInterval where
  arc : OpenArc
  carrier : Set Circle
  interior_subset : arc.carrier ⊆ carrier
  subset_closed : carrier ⊆ closure arc.carrier

/-- The open interval used for the manuscript's standard Bohr cutoffs. -/
def CircleBohrInterval.openArc (J : OpenArc) : CircleBohrInterval :=
  ⟨J, J.carrier, Subset.rfl, subset_closure⟩

noncomputable def CircleBohrInterval.indicator (J : CircleBohrInterval) : Circle → ℝ :=
  J.carrier.indicator 1

private theorem indicator_mem_Icc (J : CircleBohrInterval) (t : Circle) :
    J.indicator t ∈ Icc (0 : ℝ) 1 := by
  classical
  by_cases ht : t ∈ J.carrier <;> simp [CircleBohrInterval.indicator, ht]

private theorem rationalBohrPoint_eq_mod (β : ℚ) (p : ℕ) :
    ((β : ℝ) * ((p : ℝ) - 1) : Circle) =
      ((β : ℝ) * (((p : ZMod β.den).val : ℝ) - 1) : Circle) := by
  let d := p / β.den
  let r := p % β.den
  have hq : (β.den : ℝ) ≠ 0 := by exact_mod_cast β.den_nz
  have hp : (p : ℝ) = (r : ℝ) + (β.den : ℝ) * (d : ℝ) := by
    exact_mod_cast (Nat.mod_add_div p β.den).symm
  rw [ZMod.val_natCast]
  conv_lhs => rw [hp]
  have he : (β : ℝ) * ((r : ℝ) + (β.den : ℝ) * (d : ℝ) - 1) =
      (β : ℝ) * ((r : ℝ) - 1) + ((β.num * (d : ℤ) : ℤ) : ℝ) := by
    rw [Rat.cast_def]
    push_cast
    field_simp
    ring
  have hz : (((β.num * (d : ℤ) : ℤ) : ℝ) : Circle) = 0 :=
    (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨β.num * (d : ℤ), by simp⟩
  rw [he, AddCircle.coe_add, hz, add_zero]

private theorem exists_continuous_approx_arc (hV : VinogradovPrimeEquidistribution)
    (θ : ℝ) (J : CircleBohrInterval) {ε : ℝ} (hε : 0 < ε) :
    ∃ (ω : ℝ) (L : C(Circle, ℝ)), (∀ t, L t ∈ Icc (0 : ℝ) 1) ∧
      ∀ᶠ N in (atTop : Filter ℕ), (∑ p ∈ primesThrough N,
        |J.indicator (θ * ((p : ℝ) - 1) : Circle) -
          L (ω * ((p : ℝ) - 1) : Circle)|) / ((primesThrough N).card : ℝ) ≤ ε := by
  by_cases hθ : Irrational θ
  · obtain ⟨l,u,K,hl,hu,hord,_,hgap⟩ := J.arc.exists_lipschitz_sandwich hε
    have hlower (t : Circle) : l t ≤ J.indicator t := by
      classical
      by_cases ht : t ∈ J.arc.carrier
      · simpa [CircleBohrInterval.indicator, OpenArc.circleIndicator,
          ht, J.interior_subset ht] using (hord t).2.1
      · have hz : l t ≤ 0 := by
          simpa [OpenArc.circleIndicator, ht] using (hord t).2.1
        exact hz.trans (indicator_mem_Icc J t).1
    have hclosed : closure J.arc.carrier ⊆ {t : Circle | (1 : ℝ) ≤ u t} :=
      closure_minimal (fun t ht => by
        simpa [OpenArc.circleIndicator, ht] using (hord t).2.2.1)
        (isClosed_le continuous_const hu.continuous)
    have hupper (t : Circle) : J.indicator t ≤ u t := by
      classical
      by_cases ht : t ∈ J.carrier
      · simpa [CircleBohrInterval.indicator, ht] using hclosed (J.subset_closed ht)
      · have hpos : 0 ≤ u t := (hord t).1.trans ((hord t).2.1.trans (hord t).2.2.1)
        simpa [CircleBohrInterval.indicator, ht] using hpos
    let g := fun t => u t - l t
    let F : C(Circle, ℂ) :=
      ⟨fun t => (g t : ℂ), Complex.continuous_ofReal.comp (hu.continuous.sub hl.continuous)⟩
    have h := (Complex.continuous_re.tendsto _).comp (vinogradov_shifted hV hθ F)
    have hg : Tendsto (fun N => (∑ p ∈ primesThrough N, g (θ * ((p : ℝ) - 1) : Circle)) /
        ((primesThrough N).card : ℝ)) atTop (𝓝 (∫ t, g t ∂AddCircle.haarAddCircle)) := by
      simpa [circleMean, F, primeAverage, ← Complex.ofReal_sum, ← Complex.ofReal_natCast,
        ← Complex.ofReal_div, Function.comp_def, integral_complex_ofReal] using h
    refine ⟨θ,⟨l,hl.continuous⟩,fun t => ⟨(hord t).1,
      ((hord t).2.1.trans (hord t).2.2.1).trans (hord t).2.2.2⟩,?_⟩
    filter_upwards [hg.eventually (Iic_mem_nhds hgap)] with N hN
    apply le_trans _ hN
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply Finset.sum_le_sum
    intro p _
    set t : Circle := (θ * ((p : ℝ) - 1) : Circle)
    change |J.indicator t - l t| ≤ u t - l t
    rw [abs_of_nonneg (sub_nonneg.mpr (hlower t))]
    exact sub_le_sub_right (hupper t) _
  · have hex : θ ∈ range ((↑) : ℚ → ℝ) := not_not.mp hθ
    obtain ⟨β,rfl⟩ := hex
    letI : NeZero β.den := ⟨β.den_nz⟩
    let w (z : ZMod β.den) : ℂ := (J.indicator ((β : ℝ) * ((z.val : ℝ) - 1) : Circle) : ℂ)
    let F := periodicBohrWeight w
    let L : C(Circle, ℝ) := ⟨fun t => max 0 (min 1 (F t).re),
      continuous_const.max (continuous_const.min (Complex.continuous_re.comp F.continuous))⟩
    refine ⟨1 / (β.den : ℝ), L, fun t => ⟨le_max_left _ _,max_le zero_le_one (min_le_left _ _)⟩, ?_⟩
    have hpoint (p : ℕ) : L (((1 / (β.den : ℝ)) * ((p : ℝ) - 1) : ℝ) : Circle) =
        J.indicator ((β : ℝ) * ((p : ℝ) - 1) : Circle) := by
      change max 0 (min 1 (periodicBohrWeight w
        (((1 / (β.den : ℝ)) * ((p : ℝ) - 1) : ℝ) : Circle)).re) = _
      rw [periodicBohrWeight_eq, rationalBohrPoint_eq_mod β p]
      let t : Circle := ((β : ℝ) * ((((p : ZMod β.den).val : ℕ) : ℝ) - 1) : Circle)
      change max 0 (min 1 ((J.indicator t : ℝ) : ℂ).re) = J.indicator t
      rw [Complex.ofReal_re, min_eq_right (indicator_mem_Icc J t).2,
        max_eq_right (indicator_mem_Icc J t).1]
    exact Filter.Eventually.of_forall (fun N => by
      simp_rw [hpoint, sub_self, abs_zero, Finset.sum_const_zero, zero_div]
      exact hε.le)

private theorem abs_prod_sub_prod_le_sum {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i, a i ∈ Icc (0 : ℝ) 1) (hb : ∀ i, b i ∈ Icc (0 : ℝ) 1) :
    |(∏ i ∈ s, a i) - (∏ i ∈ s, b i)| ≤ ∑ i ∈ s, |a i - b i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi]
    let A := ∏ j ∈ s, a j
    let B := ∏ j ∈ s, b j
    change |a i * A - b i * B| ≤ |a i - b i| + ∑ j ∈ s, |a j - b j|
    rw [show a i * A - b i * B = (a i - b i) * A + b i * (A - B) by ring]
    apply (abs_add_le _ _).trans
    have hA : A ∈ Icc (0 : ℝ) 1 := ⟨Finset.prod_nonneg (fun j _ => (ha j).1),
      Finset.prod_le_one (fun j _ => (ha j).1) (fun j _ => (ha j).2)⟩
    rw [abs_mul, abs_mul, abs_of_nonneg hA.1, abs_of_nonneg (hb i).1]
    exact add_le_add (mul_le_of_le_one_right (abs_nonneg _) hA.2)
      ((mul_le_of_le_one_left (abs_nonneg _) (hb i).2).trans ih)

/-- All of a finite collection of linear interval conditions in the
shifted prime parameter. No independence of the frequencies is required. -/
def simultaneousBohrIntervalPredicate {m : ℕ} (θ : Fin m → ℝ) (J : Fin m → CircleBohrInterval)
    (p : ℕ) : Prop :=
  ∀ i, bohrPrimePoint θ p i ∈ (J i).carrier

private theorem primePredicateWeight_bohr_eq_prod {m : ℕ} (θ : Fin m → ℝ)
    (J : Fin m → CircleBohrInterval) (p : ℕ) :
    primePredicateWeight (simultaneousBohrIntervalPredicate θ J) p =
      ((∏ i, (J i).indicator (bohrPrimePoint θ p i) : ℝ) : ℂ) := by
  classical
  by_cases h : simultaneousBohrIntervalPredicate θ J p
  · have he (i : Fin m) : (J i).indicator (bohrPrimePoint θ p i) = 1 :=
      Set.indicator_of_mem (h i) 1
    simp [primePredicateWeight,h,he]
  · have hex : ∃ i, bohrPrimePoint θ p i ∉ (J i).carrier := by
      simpa only [simultaneousBohrIntervalPredicate, not_forall] using h
    obtain ⟨i,hi⟩ := hex
    have he : (J i).indicator (bohrPrimePoint θ p i) = 0 :=
      Set.indicator_of_not_mem hi 1
    have hprod : (∏ j, (J j).indicator (bohrPrimePoint θ p j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) he
    rw [hprod, Complex.ofReal_zero]
    simp [primePredicateWeight,h]

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Simultaneous fixed interval cutoffs have a pointwise limit at the
common prime-count normalization. Irrational coordinates use their
one-dimensional boundary error. Rational cutoff values are matched
exactly by finite Fourier interpolation, including at endpoints. -/
theorem ae_simultaneousBohrIntervalAverage_tendsto [IsProbabilityMeasure μ]
    (hPNT : PrimeNumberTheorem) (hMWW : MirekWanWrightPointwise (X × (Circle × Circle)))
    (hV : VinogradovPrimeEquidistribution) (T : ProbabilitySystem X μ)
    {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ) (hP : ErgodicPolynomialFamily P)
    (f : Fin ℓ → X → ℂ) (hf : ∀ i, MemLp (f i) ∞ μ)
    {m : ℕ} (θ : Fin m → ℝ) (J : Fin m → CircleBohrInterval) :
    ∀ᵐ x ∂μ, ∃ L : ℂ, Tendsto
      (weightedPrimeAverage (primePredicateWeight (simultaneousBohrIntervalPredicate θ J))
        (fun p => ergodicSequence T P f ((p : ℤ) - 1) x)) atTop (𝓝 L) := by
  let ε (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)
  have hε : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hεpos (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
  choose ω L hL hnear using fun j (i : Fin m) =>
    exists_continuous_approx_arc hV (θ i) (J i) (hεpos j)
  let F (j : ℕ) : C(BohrTorus m, ℂ) :=
    ⟨fun t => ((∏ i, L j i (t i) : ℝ) : ℂ), Complex.continuous_ofReal.comp
      (continuous_finset_prod _ fun i _ => (L j i).continuous.comp (continuous_apply i))⟩
  let δ (j : ℕ) : ℝ := (m : ℝ) * ε j
  have hδ : Tendsto δ atTop (𝓝 0) := by
    simpa only [mul_zero] using hε.const_mul (m : ℝ)
  refine ae_weightedPrimeAverage_of_approximation T P f hf
    (fun j p => F j (bohrPrimePoint (ω j) p)) δ hδ (fun j => ?_)
    (fun j => ae_continuousBohrPrimeAverage_tendsto hPNT hMWW T P hP f hf (ω j) (F j))
  have hev : ∀ᶠ N in (atTop : Filter ℕ), ∀ i : Fin m, (∑ p ∈ primesThrough N,
      |(J i).indicator (bohrPrimePoint θ p i) - L j i (bohrPrimePoint (ω j) p i)|) /
        ((primesThrough N).card : ℝ) ≤ ε j := eventually_all.mpr (hnear j)
  filter_upwards [hev] with N hN
  let a (p : ℕ) (i : Fin m) := (J i).indicator (bohrPrimePoint θ p i)
  let b (p : ℕ) (i : Fin m) := L j i (bohrPrimePoint (ω j) p i)
  simp only [primePredicateWeight_bohr_eq_prod, F, ContinuousMap.coe_mk,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ (∑ p ∈ primesThrough N, ∑ i, |a p i - b p i|) /
          ((primesThrough N).card : ℝ) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro p _
      exact abs_prod_sub_prod_le_sum _ (a p) (b p) (fun i => indicator_mem_Icc _ _) (fun i => hL j i _)
    _ = ∑ i, (∑ p ∈ primesThrough N, |a p i - b p i|) /
          ((primesThrough N).card : ℝ) := by
      rw [← Finset.sum_div]
      congr 1
      exact Finset.sum_comm
    _ ≤ δ j := by
      calc
        _ ≤ ∑ _i : Fin m, ε j := Finset.sum_le_sum (fun i _ => hN i)
        _ = δ j := by simp [δ, nsmul_eq_mul]

/-- The relative prime density of any fixed simultaneous Bohr selector
has a limit. To extract it, the same convergence is tested against 1. -/
theorem simultaneousBohrIntervalDensity_tendsto [IsProbabilityMeasure μ]
    (hPNT : PrimeNumberTheorem) (hMWW : MirekWanWrightPointwise (X × (Circle × Circle)))
    (hV : VinogradovPrimeEquidistribution) (T : ProbabilitySystem X μ)
    {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ) (hP : ErgodicPolynomialFamily P)
    {m : ℕ} (θ : Fin m → ℝ) (J : Fin m → CircleBohrInterval) :
    ∃ d : ℝ, Tendsto (predicatePrimeDensity (simultaneousBohrIntervalPredicate θ J)) atTop (𝓝 d) := by
  have h := ae_simultaneousBohrIntervalAverage_tendsto hPNT hMWW hV T P hP
    (fun _ _ => (1 : ℂ)) (fun _ => memLp_const _) θ J
  obtain ⟨x,L,hL⟩ := h.exists
  have h1 (p : ℕ) : ergodicSequence T P (fun _ _ => (1 : ℂ)) ((p : ℤ) - 1) x = 1 := by
    simp [ergodicSequence]
  simp only [h1] at hL
  have hD : Tendsto (fun N => (predicatePrimeDensity (simultaneousBohrIntervalPredicate θ J) N : ℂ))
      atTop (𝓝 L) := hL.congr (fun N => (predicatePrimeDensity_eq_weighted_one _ N).symm)
  exact ⟨L.re, by simpa only [Function.comp_apply, Complex.ofReal_re] using
    (Complex.continuous_re.tendsto L).comp hD⟩

/-- When the simultaneous cutoffs have positive limiting relative density,
the averages normalized by the number of selected primes also converge. -/
theorem ae_selectedSimultaneousBohrIntervalAverage_tendsto [IsProbabilityMeasure μ]
    (hPNT : PrimeNumberTheorem) (hMWW : MirekWanWrightPointwise (X × (Circle × Circle)))
    (hV : VinogradovPrimeEquidistribution) (T : ProbabilitySystem X μ)
    {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ) (hP : ErgodicPolynomialFamily P)
    (f : Fin ℓ → X → ℂ) (hf : ∀ i, MemLp (f i) ∞ μ)
    {m : ℕ} (θ : Fin m → ℝ) (J : Fin m → CircleBohrInterval)
    {d : ℝ} (hd : 0 < d)
    (hD : Tendsto (predicatePrimeDensity (simultaneousBohrIntervalPredicate θ J)) atTop (𝓝 d)) :
    ∀ᵐ x ∂μ, ∃ L : ℂ, Tendsto
      (predicatePrimeAverage (simultaneousBohrIntervalPredicate θ J)
        (fun p => ergodicSequence T P f ((p : ℤ) - 1) x)) atTop (𝓝 L) :=
  ae_predicatePrimeAverage_tendsto hd hD _
    (ae_simultaneousBohrIntervalAverage_tendsto hPNT hMWW hV T P hP f hf θ J)

/-- All of a finite collection of linear open-arc conditions in the
shifted prime parameter. No independence of the frequencies is required. -/
def simultaneousBohrPredicate {m : ℕ} (θ : Fin m → ℝ) (J : Fin m → OpenArc)
    (p : ℕ) : Prop :=
  simultaneousBohrIntervalPredicate θ (fun i => CircleBohrInterval.openArc (J i)) p


/-- Simultaneous fixed interval cutoffs have a pointwise limit at the
common prime-count normalization. Irrational coordinates use their
one-dimensional boundary error. Rational cutoff values are matched
exactly by finite Fourier interpolation, including at endpoints. -/
theorem ae_simultaneousBohrPrimeAverage_tendsto [IsProbabilityMeasure μ]
    (hPNT : PrimeNumberTheorem) (hMWW : MirekWanWrightPointwise (X × (Circle × Circle)))
    (hV : VinogradovPrimeEquidistribution) (T : ProbabilitySystem X μ)
    {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ) (hP : ErgodicPolynomialFamily P)
    (f : Fin ℓ → X → ℂ) (hf : ∀ i, MemLp (f i) ∞ μ)
    {m : ℕ} (θ : Fin m → ℝ) (J : Fin m → OpenArc) :
    ∀ᵐ x ∂μ, ∃ L : ℂ, Tendsto
      (weightedPrimeAverage (primePredicateWeight (simultaneousBohrPredicate θ J))
        (fun p => ergodicSequence T P f ((p : ℤ) - 1) x)) atTop (𝓝 L) :=
  ae_simultaneousBohrIntervalAverage_tendsto hPNT hMWW hV T P hP f hf θ
    (fun i => CircleBohrInterval.openArc (J i))

/-- The relative prime density of any fixed simultaneous Bohr selector
has a limit. To extract it, the same convergence is tested against 1. -/
theorem simultaneousBohrPrimeDensity_tendsto [IsProbabilityMeasure μ]
    (hPNT : PrimeNumberTheorem) (hMWW : MirekWanWrightPointwise (X × (Circle × Circle)))
    (hV : VinogradovPrimeEquidistribution) (T : ProbabilitySystem X μ)
    {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ) (hP : ErgodicPolynomialFamily P)
    {m : ℕ} (θ : Fin m → ℝ) (J : Fin m → OpenArc) :
    ∃ d : ℝ, Tendsto (predicatePrimeDensity (simultaneousBohrPredicate θ J)) atTop (𝓝 d) :=
  simultaneousBohrIntervalDensity_tendsto hPNT hMWW hV T P hP θ
    (fun i => CircleBohrInterval.openArc (J i))

/-- When the simultaneous cutoffs have positive limiting relative density,
the averages normalized by the number of selected primes also converge. -/
theorem ae_selectedSimultaneousBohrPrimeAverage_tendsto [IsProbabilityMeasure μ]
    (hPNT : PrimeNumberTheorem) (hMWW : MirekWanWrightPointwise (X × (Circle × Circle)))
    (hV : VinogradovPrimeEquidistribution) (T : ProbabilitySystem X μ)
    {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ) (hP : ErgodicPolynomialFamily P)
    (f : Fin ℓ → X → ℂ) (hf : ∀ i, MemLp (f i) ∞ μ)
    {m : ℕ} (θ : Fin m → ℝ) (J : Fin m → OpenArc)
    {d : ℝ} (hd : 0 < d)
    (hD : Tendsto (predicatePrimeDensity (simultaneousBohrPredicate θ J)) atTop (𝓝 d)) :
    ∀ᵐ x ∂μ, ∃ L : ℂ, Tendsto
      (predicatePrimeAverage (simultaneousBohrPredicate θ J)
        (fun p => ergodicSequence T P f ((p : ℤ) - 1) x)) atTop (𝓝 L) :=
  ae_selectedSimultaneousBohrIntervalAverage_tendsto hPNT hMWW hV T P hP f hf θ
    (fun i => CircleBohrInterval.openArc (J i)) hd hD

end NilBohr
