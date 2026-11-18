import NilBohr.BohrPointwise
import NilBohr.BracketPointwise

/-! Uniform Fourier approximation on a finite-dimensional torus and prime
averages under finitely many simultaneous Bohr restrictions. -/

namespace NilBohr

open Filter MeasureTheory Polynomial Set
open scoped BigOperators Topology ENNReal ComplexConjugate

abbrev BohrTorus (m : ℕ) := Fin m → Circle

/-- The vector of frequencies evaluated on the shifted prime variable. -/
def bohrPrimePoint {m : ℕ} (θ : Fin m → ℝ) (p : ℕ) : BohrTorus m :=
  fun i => (θ i * ((p : ℝ) - 1) : Circle)

/-- Characters on the finite product of the unit additive circle. -/
noncomputable def bohrFourier {m : ℕ} (k : Fin m → ℤ) : C(BohrTorus m, ℂ) :=
  ⟨fun t => ∏ i, fourier (T := 1) (k i) (t i),
    continuous_finset_prod _ (fun i _ => (fourier (T := 1) (k i)).continuous.comp
      (continuous_apply i))⟩

private theorem bohrFourier_zero {m : ℕ} : bohrFourier (0 : Fin m → ℤ) = 1 := by
  ext t
  simp [bohrFourier, fourier_zero]

private theorem bohrFourier_add {m : ℕ} (k l : Fin m → ℤ) :
    bohrFourier (k + l) = bohrFourier k * bohrFourier l := by
  ext t
  simp [bohrFourier, fourier_add, Finset.prod_mul_distrib]

private theorem bohrFourier_neg {m : ℕ} (k : Fin m → ℤ) :
    bohrFourier (-k) = star (bohrFourier k) := by
  ext t
  simp [bohrFourier, fourier_neg, map_prod]

private noncomputable def bohrFourierSubalgebra (m : ℕ) : StarSubalgebra ℂ C(BohrTorus m, ℂ) where
  toSubalgebra := Algebra.adjoin ℂ (range bohrFourier)
  star_mem' := by
    show Algebra.adjoin ℂ (range (bohrFourier (m := m))) ≤
      star (Algebra.adjoin ℂ (range (bohrFourier (m := m))))
    refine Algebra.adjoin_le ?_
    rintro - ⟨k, rfl⟩
    exact Algebra.subset_adjoin ⟨-k, bohrFourier_neg k⟩

private theorem bohrFourierSubalgebra_toSubmodule (m : ℕ) :
    (bohrFourierSubalgebra m).toSubalgebra.toSubmodule =
      Submodule.span ℂ (range (bohrFourier (m := m))) := by
  apply Algebra.adjoin_eq_span_of_subset
  refine Subset.trans ?_ Submodule.subset_span
  intro x hx
  refine Submonoid.closure_induction (fun _ => id) ⟨0, bohrFourier_zero⟩ ?_ hx
  rintro - - - - ⟨k, rfl⟩ ⟨l, rfl⟩
  exact ⟨k + l, bohrFourier_add k l⟩

/-- Finite sums of Fourier characters are uniformly dense on the torus. -/
theorem bohrFourier_span_closure_eq_top (m : ℕ) :
    (Submodule.span ℂ (range (bohrFourier (m := m)))).topologicalClosure = ⊤ := by
  rw [← bohrFourierSubalgebra_toSubmodule]
  have hsep : (bohrFourierSubalgebra m).SeparatesPoints := by
    intro x y hxy
    have hdiff : ∃ i, x i ≠ y i := by
      by_contra! h
      exact hxy (funext h)
    obtain ⟨i, hi⟩ := hdiff
    let k : Fin m → ℤ := fun j => if j = i then 1 else 0
    have heval (t : BohrTorus m) : bohrFourier k t = fourier (T := 1) 1 (t i) := by
      simp only [bohrFourier, ContinuousMap.coe_mk]
      rw [Finset.prod_eq_single i] <;> simp_all [k, fourier_zero]
    refine ⟨bohrFourier k, ⟨bohrFourier k, Algebra.subset_adjoin ⟨k, rfl⟩, rfl⟩, ?_⟩
    rw [heval, heval, fourier_one, fourier_one]
    intro he
    exact hi (AddCircle.injective_toCircle (by norm_num) (Subtype.coe_injective he))
  exact congrArg (Subalgebra.toSubmodule <| StarSubalgebra.toSubalgebra ·)
    (ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _ hsep)

private theorem bohrFourier_bohrPrimePoint {m : ℕ} (k : Fin m → ℤ) (θ : Fin m → ℝ)
    (p : ℕ) : bohrFourier k (bohrPrimePoint θ p) =
      bohrPrimeMode (∑ i, (k i : ℝ) * θ i) p := by
  have he (i : Fin m) : fourier (T := 1) (k i) (bohrPrimePoint θ p i) =
      phase (((k i : ℝ) * θ i) * ((p : ℝ) - 1)) := by
    simp only [bohrPrimePoint, fourier_coe_apply, Complex.ofReal_one, div_one, phase,
      Complex.ofReal_mul, Complex.ofReal_intCast, mul_assoc]
  change (∏ i, fourier (T := 1) (k i) (bohrPrimePoint θ p i)) = _
  simp_rw [he]
  rw [bohrPrimeMode, Finset.sum_mul]
  induction (Finset.univ : Finset (Fin m)) using Finset.induction_on with
  | empty => simp [phase]
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, phase_add, ih]

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

private theorem bohrFourierSpan_primeAverage [IsProbabilityMeasure μ]
    (hPNT : PrimeNumberTheorem) (hMWW : MirekWanWrightPointwise (X × (Circle × Circle)))
    (T : ProbabilitySystem X μ) {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ)
    (hP : ErgodicPolynomialFamily P) (f : Fin ℓ → X → ℂ)
    (hf : ∀ i, MemLp (f i) ∞ μ) {m : ℕ} (θ : Fin m → ℝ)
    {F : C(BohrTorus m, ℂ)} (hF : F ∈ Submodule.span ℂ (range bohrFourier)) :
    ∀ᵐ x ∂μ, ∃ L : ℂ, Tendsto
      (weightedPrimeAverage (fun p => F (bohrPrimePoint θ p))
        (fun p => ergodicSequence T P f ((p : ℤ) - 1) x)) atTop (𝓝 L) := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hF
  · rintro _ ⟨k,rfl⟩
    simp_rw [bohrFourier_bohrPrimePoint]
    exact ae_bohrPrimeMode_tendsto hPNT hMWW T P hP f hf _
  · exact Filter.Eventually.of_forall (fun x => ⟨0,
      (tendsto_const_nhds (x := (0 : ℂ))).congr (fun N => by
        simp [ContinuousMap.zero_apply, weightedPrimeAverage, primeAverage])⟩)
  · intro F G _ _ hF hG
    filter_upwards [hF,hG] with x hx hy
    obtain ⟨L,hL⟩ := hx
    obtain ⟨M,hM⟩ := hy
    exact ⟨L + M, (hL.add hM).congr (fun N => by
      simp only [weightedPrimeAverage, primeAverage, ContinuousMap.add_apply, add_mul,
        Finset.sum_add_distrib, add_div, Pi.add_apply])⟩
  · intro c F _ hF
    filter_upwards [hF] with x hx
    obtain ⟨L,hL⟩ := hx
    exact ⟨c * L, (hL.const_mul c).congr (fun N => by
      simp only [weightedPrimeAverage, primeAverage, ContinuousMap.smul_apply, smul_eq_mul,
        mul_assoc, ← Finset.mul_sum, mul_div_assoc])⟩

/-- Continuous weights on any finite-dimensional Bohr torus yield
pointwise convergence. Frequencies may be rational, irrational, or
rationally dependent. -/
theorem ae_continuousBohrPrimeAverage_tendsto [IsProbabilityMeasure μ]
    (hPNT : PrimeNumberTheorem) (hMWW : MirekWanWrightPointwise (X × (Circle × Circle)))
    (T : ProbabilitySystem X μ) {ℓ : ℕ} (P : Fin ℓ → Polynomial ℤ)
    (hP : ErgodicPolynomialFamily P) (f : Fin ℓ → X → ℂ)
    (hf : ∀ i, MemLp (f i) ∞ μ) {m : ℕ} (θ : Fin m → ℝ) (F : C(BohrTorus m, ℂ)) :
    ∀ᵐ x ∂μ, ∃ L : ℂ, Tendsto
      (weightedPrimeAverage (fun p => F (bohrPrimePoint θ p))
        (fun p => ergodicSequence T P f ((p : ℤ) - 1) x)) atTop (𝓝 L) := by
  let δ (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)
  have hδpos (j : ℕ) : 0 < δ j := by dsimp [δ]; positivity
  have hδ : Tendsto δ atTop (𝓝 0) := by
    simpa [δ, Nat.cast_add, Nat.cast_one] using (tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0))
  let E := Submodule.span ℂ (range (bohrFourier (m := m)))
  have hcl : F ∈ closure (E : Set C(BohrTorus m, ℂ)) := by
    change F ∈ E.topologicalClosure
    rw [bohrFourier_span_closure_eq_top]
    trivial
  have hex (j : ℕ) : ∃ G ∈ E, ‖F - G‖ < δ j := by
    obtain ⟨G,hG,hFG⟩ := Metric.mem_closure_iff.mp hcl (δ j) (hδpos j)
    exact ⟨G,hG,by simpa [dist_eq_norm, norm_sub_rev] using hFG⟩
  choose G hG hGnear using hex
  refine ae_weightedPrimeAverage_of_approximation T P f hf
    (fun j p => G j (bohrPrimePoint θ p)) δ hδ (fun j => ?_)
    (fun j => bohrFourierSpan_primeAverage hPNT hMWW T P hP f hf θ (hG j))
  apply Filter.Eventually.of_forall
  intro N
  have hterm (p : ℕ) : ‖F (bohrPrimePoint θ p) - G j (bohrPrimePoint θ p)‖ ≤ δ j :=
    ((ContinuousMap.norm_coe_le_norm (F - G j) (bohrPrimePoint θ p))).trans (hGnear j).le
  by_cases hc : (primesThrough N).card = 0
  · simp [hc, (hδpos j).le]
  have hc' : 0 < ((primesThrough N).card : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hc)
  rw [div_le_iff₀ hc', mul_comm (δ j), ← nsmul_eq_mul, ← Finset.sum_const]
  exact Finset.sum_le_sum (fun p _ => hterm p)

end NilBohr
