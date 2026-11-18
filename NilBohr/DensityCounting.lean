import NilBohr.Density
import NilBohr.PrimePowers

open scoped BigOperators

namespace NilBohr

set_option maxHeartbeats 600000 in
/-- A central block of spatial points supplies the manuscript's constant-density
model lower bound on any set of parameters with sufficiently small shifts. -/
theorem density_model_count_lower {k N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (P : Fin k → Polynomial ℤ) (Y : Finset ℤ) (hY : Y ⊆ positiveInterval M)
    (hshift : ∀ y ∈ Y, ∀ i, |(P i).eval y| ≤ ((N / 4 : ℕ) : ℤ))
    {δ : ℝ} (hδ : 0 ≤ δ) :
    (Y.card : ℝ) / (2 * (M : ℝ)) * δ^k ≤
      ‖countingForm N M (positiveInterval N) P (fun _ => 1) (fun _ => densityModel N δ)‖ := by
  classical
  let I := positiveInterval N
  let X := Finset.Icc (((N / 4 : ℕ) : ℤ) + 1) ((N : ℤ) - ((N / 4 : ℕ) : ℤ))
  have hX : X ⊆ I := by
    intro x hx
    have hp := Finset.mem_Icc.mp hx
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hcardX : (N : ℝ) / 2 ≤ (X.card : ℝ) := by
    have heq : X.card = N - 2 * (N / 4) := by
      dsimp only [X]
      rw [Int.card_Icc]
      omega
    rw [heq]
    have h₁ : N ≤ 2 * (N - 2 * (N / 4)) := by omega
    have h₂ : (N : ℝ) ≤ 2 * ((N - 2 * (N / 4) : ℕ) : ℝ) := by exact_mod_cast h₁
    linarith
  let f (z : ℤ) : ℝ := if z ∈ I then δ else 0
  have hf (z : ℤ) : 0 ≤ f z := by dsimp [f]; split_ifs <;> positivity
  let term (x y : ℤ) := ∏ i, f (x + (P i).eval y)
  have ht (x y : ℤ) : 0 ≤ term x y := Finset.prod_nonneg (fun i _ => hf _)
  have hgood (x y : ℤ) (hx : x ∈ X) (hy : y ∈ Y) : term x y = δ^k := by
    have hsites (i : Fin k) : x + (P i).eval y ∈ I := by
      have hxc := Finset.mem_Icc.mp hx
      have hs := abs_le.mp (hshift y hy i)
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    simp [term, f, hsites]
  have hnum : (Y.card : ℝ) * (X.card : ℝ) * δ^k ≤
      ∑ x ∈ I, ∑ y ∈ positiveInterval M, term x y := by
    calc
      _ = ∑ x ∈ X, ∑ y ∈ Y, term x y := by
        have hfib (x : ℤ) (hx : x ∈ X) :
            ∑ y ∈ Y, term x y = (Y.card : ℝ) * δ^k := by
          rw [Finset.sum_congr rfl (fun y hy => hgood x y hx hy)]
          simp [nsmul_eq_mul]
        rw [Finset.sum_congr rfl hfib]
        simp [nsmul_eq_mul]
        ring
      _ ≤ ∑ x ∈ I, ∑ y ∈ Y, term x y :=
        Finset.sum_le_sum_of_subset_of_nonneg hX
          (fun x _ _ => Finset.sum_nonneg (fun y _ => ht x y))
      _ ≤ _ := Finset.sum_le_sum (fun x _ => Finset.sum_le_sum_of_subset_of_nonneg
        hY (fun y _ _ => ht x y))
  let num := ∑ x ∈ I, ∑ y ∈ positiveInterval M, term x y
  have hnum₀ : 0 ≤ num := Finset.sum_nonneg (fun x _ => Finset.sum_nonneg (fun y _ => ht x y))
  have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hM' : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hcount : countingForm N M (positiveInterval N) P (fun _ => 1) (fun _ => densityModel N δ) =
      (((num / ((N : ℝ) * (M : ℝ))) : ℝ) : ℂ) := by
    simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_natCast,
      Complex.ofReal_sum, Complex.ofReal_prod, countingForm, one_mul, num, term]
    congr 1
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    apply Finset.prod_congr rfl
    intro i hi
    by_cases hz : x + (P i).eval y ∈ positiveInterval N
    · simp only [densityModel, f, I, hz, if_true]
    · simp only [densityModel, f, I, hz, if_false, Complex.ofReal_zero]
  rw [hcount, Complex.norm_of_nonneg (div_nonneg hnum₀ (mul_nonneg hN'.le hM'.le))]
  apply (le_div_iff₀ (mul_pos hN' hM')).mpr
  have heq : (Y.card : ℝ) / (2 * (M : ℝ)) * δ^k * ((N : ℝ) * (M : ℝ)) =
      (Y.card : ℝ) * ((N : ℝ) / 2) * δ^k := by
    field_simp [hM'.ne']
    ring
  rw [heq]
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcardX (Nat.cast_nonneg _)) (pow_nonneg hδ _)).trans hnum

/-- The two errors of size (mu c_3delta^k/4) and the regularity error of
size (c_3delta^k/8) leave a discrepancy of at least (3c_3delta^k/8).
This statement is valid for complex counting forms. -/
theorem regularized_count_discrepancy (weighted unweighted regularized model : ℂ)
    {μ v : ℝ} (hμ : 0 < μ)
    (hweighted : ‖weighted‖ ≤ μ * v / 4)
    (hcompare : ‖weighted - (μ : ℂ) * unweighted‖ ≤ μ * v / 4)
    (hreg : ‖regularized - unweighted‖ ≤ v / 8)
    (hmodel : v ≤ ‖model‖) :
    3 * v / 8 ≤ ‖regularized - model‖ := by
  have hsmall : μ * ‖unweighted‖ ≤ μ * (v / 2) := calc
    _ = ‖(μ : ℂ) * unweighted‖ := by rw [norm_mul, Complex.norm_of_nonneg hμ.le]
    _ = ‖weighted - (weighted - (μ : ℂ) * unweighted)‖ := by congr 1; ring
    _ ≤ ‖weighted‖ + ‖weighted - (μ : ℂ) * unweighted‖ := norm_sub_le _ _
    _ ≤ _ := by linarith
  have hunweighted : ‖unweighted‖ ≤ v / 2 := (mul_le_mul_left hμ).mp hsmall
  have hregularized : ‖regularized‖ ≤ 5 * v / 8 := calc
    _ = ‖regularized - unweighted + unweighted‖ := by rw [sub_add_cancel]
    _ ≤ ‖regularized - unweighted‖ + ‖unweighted‖ := norm_add_le _ _
    _ ≤ _ := by linarith
  have hdiff : ‖model‖ ≤ ‖regularized - model‖ + ‖regularized‖ := calc
    _ = ‖model - regularized + regularized‖ := by rw [sub_add_cancel]
    _ ≤ ‖model - regularized‖ + ‖regularized‖ := norm_add_le _ _
    _ = _ := by rw [norm_sub_rev]
  linarith


/-- Finite proof of the density increment from the specific counting
and local-factor inputs used in Proposition 3.1. The estimates and
construction appearing as hypotheses here are separate obligations. -/
theorem density_increment_atom_from_count_inputs {k N M q B : ℕ}
    (hN : 0 < N) (P : Fin k → Polynomial ℤ) (A : Finset ℤ)
    (H : Fin k → ℤ → ℝ) {δ η μ v L : ℝ}
    (hδ : 0 ≤ δ) (hη : 0 ≤ η) (hμ : 0 < μ)
    (hH₀ : ∀ i z, 0 ≤ H i z)
    (hHsupp : ∀ i z, z ∉ positiveInterval N → H i z = 0)
    (hmass : ∀ i, ∑ z ∈ positiveInterval N, H i z = (N : ℝ) * δ)
    (hatom : ∀ i z, z ∈ positiveInterval N →
      ∃ (a : ℤ) (N' : ℕ), 0 < N' ∧ L ≤ (N' : ℝ) ∧
        (positiveInterval N').image (fun x => a + ((q ^ B : ℕ) : ℤ) * x) ⊆
          positiveInterval N ∧
        H i z = setDensity (progressionPullback A a (q ^ B) N') N')
    (weight : ℤ → ℂ)
    (hweighted :
      ‖countingForm N M (positiveInterval N) P weight
        (fun _ z => if z ∈ A then (1 : ℂ) else 0)‖ ≤ μ * v / 4)
    (hcompare :
      ‖countingForm N M (positiveInterval N) P weight
          (fun _ z => if z ∈ A then (1 : ℂ) else 0) -
        (μ : ℂ) * countingForm N M (positiveInterval N) P (fun _ => 1)
          (fun _ z => if z ∈ A then (1 : ℂ) else 0)‖ ≤ μ * v / 4)
    (hreg :
      ‖countingForm N M (positiveInterval N) P (fun _ => 1) (fun i z => (H i z : ℂ)) -
        countingForm N M (positiveInterval N) P (fun _ => 1)
          (fun _ z => if z ∈ A then (1 : ℂ) else 0)‖ ≤ v / 8)
    (hmodel : v ≤ ‖countingForm N M (positiveInterval N) P (fun _ => 1)
      (fun _ => densityModel N δ)‖)
    (hgain : (k : ℝ) * (2 * η * δ) * ((1 + η) * δ) ^ (k - 1) < 3 * v / 8) :
    ∃ (a : ℤ) (N' : ℕ), L ≤ (N' : ℝ) ∧
      (positiveInterval N').image (fun x => a + ((q ^ B : ℕ) : ℤ) * x) ⊆
        positiveInterval N ∧
      (1 + η) * δ * N' ≤ (progressionPullback A a (q ^ B) N').card := by
  classical
  have hdisc := regularized_count_discrepancy _ _ _ _ hμ hweighted hcompare hreg hmodel
  obtain ⟨i, z, hz, hH⟩ := exists_density_increase_of_count_discrepancy hN P H
    hδ hη hH₀ hHsupp hmass (hgain.trans_le hdisc)
  obtain ⟨a, N', hN', hlen, hs, heq⟩ := hatom i z hz
  refine ⟨a, N', hlen, hs, ?_⟩
  rw [heq, setDensity] at hH
  exact ((lt_div_iff₀ (show (0 : ℝ) < N' by exact_mod_cast hN')).mp hH).le


/-- Conditional expectation of the indicator of (A) onto a finite factor,
written as the ratio of the cardinalities of its fibre intersections. -/
noncomputable def localFactorDensity {κ : Type*} [DecidableEq κ]
    (I A : Finset ℤ) (factor : ℤ → κ) (z : ℤ) : ℝ :=
  if z ∈ I then
    ((A.filter (fun x => factor x = factor z)).card : ℝ) /
      ((I.filter (fun x => factor x = factor z)).card : ℝ)
  else 0

theorem localFactorDensity_nonneg {κ : Type*} [DecidableEq κ]
    (I A : Finset ℤ) (factor : ℤ → κ) (z : ℤ) :
    0 ≤ localFactorDensity I A factor z := by
  unfold localFactorDensity
  split_ifs <;> positivity

theorem localFactorDensity_eq_zero_off {κ : Type*} [DecidableEq κ]
    (I A : Finset ℤ) (factor : ℤ → κ) {z : ℤ} (hz : z ∉ I) :
    localFactorDensity I A factor z = 0 := by
  simp [localFactorDensity, hz]

/-- Exact mass preservation for the finite-factor projections in Proposition 3.1. -/
theorem sum_localFactorDensity {κ : Type*} [DecidableEq κ]
    (I A : Finset ℤ) (hA : A ⊆ I) (factor : ℤ → κ) :
    ∑ z ∈ I, localFactorDensity I A factor z = (A.card : ℝ) := by
  classical
  let values := I.image factor
  have hI (z : ℤ) (hz : z ∈ I) : factor z ∈ values :=
    Finset.mem_image_of_mem factor hz
  have hcardA : A.card = ∑ y ∈ values, (A.filter (fun z => factor z = y)).card :=
    Finset.card_eq_sum_card_fiberwise (fun z hz => hI z (hA hz))
  rw [← Finset.sum_fiberwise_of_maps_to hI (localFactorDensity I A factor), hcardA,
    Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro y hy
  let J := I.filter (fun z => factor z = y)
  have hJ : J.Nonempty := by
    obtain ⟨z, hz, heq⟩ := Finset.mem_image.mp hy
    exact ⟨z, Finset.mem_filter.mpr ⟨hz, heq⟩⟩
  let mass := ((A.filter (fun z => factor z = y)).card : ℝ)
  have hconstant (z : ℤ) (hz : z ∈ J) :
      localFactorDensity I A factor z = mass / (J.card : ℝ) := by
    obtain ⟨hzI, hf⟩ := Finset.mem_filter.mp hz
    simp only [localFactorDensity, if_pos hzI, hf, mass, J]
  change ∑ z ∈ J, localFactorDensity I A factor z = mass
  rw [Finset.sum_congr rfl hconstant]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hJ' : (J.card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hJ
  rw [mul_comm, div_mul_cancel₀ _ hJ']

theorem sum_localFactorDensity_on_interval {κ : Type*} [DecidableEq κ]
    {N : ℕ} (hN : 0 < N) (A : Finset ℤ) (hA : A ⊆ positiveInterval N)
    (factor : ℤ → κ) :
    ∑ z ∈ positiveInterval N, localFactorDensity (positiveInterval N) A factor z =
      (N : ℝ) * setDensity A N := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [sum_localFactorDensity _ _ hA, setDensity, mul_comm, div_mul_cancel₀ _ hN']


/-- Parameters where two of the shifts coincide. -/
noncomputable def coincidentShiftParameters {k : ℕ} (P : Fin k → Polynomial ℤ)
    (Y : Finset ℤ) : Finset ℤ := by
  classical
  exact Y.filter (fun y => ∃ i j, i ≠ j ∧ (P i).eval y = (P j).eval y)

/-- A collision arises from a root of one of the pairwise polynomial
differences. Distinct degrees imply the polynomial injectivity hypothesis. -/
theorem card_coincidentShiftParameters_le {k d : ℕ}
    (P : Fin k → Polynomial ℤ) (hP : Function.Injective P)
    (hdeg : ∀ i, (P i).natDegree ≤ d) (Y : Finset ℤ) :
    (coincidentShiftParameters P Y).card ≤ k^2 * d := by
  classical
  let roots : Fin k × Fin k → Finset ℤ := fun p => (P p.1 - P p.2).roots.toFinset
  have hsubset : coincidentShiftParameters P Y ⊆ (Finset.univ : Finset (Fin k × Fin k)).biUnion roots := by
    intro y hy
    obtain ⟨_, i, j, hij, he⟩ := Finset.mem_filter.mp hy
    apply Finset.mem_biUnion.mpr
    refine ⟨(i,j), Finset.mem_univ _, ?_⟩
    change y ∈ (P i - P j).roots.toFinset
    apply Multiset.mem_toFinset.mpr
    apply (Polynomial.mem_roots (sub_ne_zero.mpr (fun h => hij (hP h)))).mpr
    rw [Polynomial.IsRoot.def, Polynomial.eval_sub, sub_eq_zero]
    exact he
  have hcard (p : Fin k × Fin k) : (roots p).card ≤ d := by
    calc
      _ ≤ (P p.1 - P p.2).roots.card := Multiset.toFinset_card_le _
      _ ≤ (P p.1 - P p.2).natDegree := Polynomial.card_roots' _
      _ ≤ max (P p.1).natDegree (P p.2).natDegree := Polynomial.natDegree_sub_le _ _
      _ ≤ d := max_le (hdeg p.1) (hdeg p.2)
  refine (Finset.card_le_card hsubset).trans ?_
  simpa [pow_two] using
    (Finset.card_biUnion_le_card_mul (Finset.univ : Finset (Fin k × Fin k)) roots d (fun p _ => hcard p))


/-- With no selected-prime configuration, a nonzero summand of the weighted
indicator count can occur only at a collision or a higher prime power. -/
theorem selected_count_summand_exception {ℓ q M : ℕ}
    (P : Fin (ℓ + 1) → Polynomial ℤ) (A : Finset ℤ) (selector : ℕ → Prop)
    (hno : ¬ ContainsScaledConfiguration A P selector q)
    (F : ℤ → ℂ)
    (hcut : ∀ y ∈ positiveInterval M, (q * y.toNat + 1).Prime →
      ¬ selector (q * y.toNat + 1) → F y = 0)
    (x y : ℤ) (hy : y ∈ positiveInterval M)
    (hne : (lambdaModulus q y : ℂ) * F y *
      (∏ i, if x + (rescalePolynomial q (P i)).eval y ∈ A then (1 : ℂ) else 0) ≠ 0) :
    y ∈ coincidentShiftParameters (fun i => rescalePolynomial q (P i)) (positiveInterval M) ∨
      (IsPrimePow (q * y.toNat + 1) ∧ ¬ (q * y.toNat + 1).Prime) := by
  classical
  by_cases hc : y ∈ coincidentShiftParameters (fun i => rescalePolynomial q (P i))
      (positiveInterval M)
  · exact Or.inl hc
  right
  let p := q * y.toNat + 1
  have hy₁ := (Finset.mem_Icc.mp hy).1
  have hycast : (y.toNat : ℤ) = y := Int.toNat_of_nonneg (by omega)
  have hyp : 0 < y.toNat := by omega
  have hpnat : ((q : ℤ) * y + 1).toNat = p := by
    have hcast : (p : ℤ) = (q : ℤ) * y + 1 := by simp [p, hycast]
    rw [← hcast]
    simp
  have hLambdaNe : ArithmeticFunction.vonMangoldt p ≠ 0 := by
    intro hz
    apply hne
    simp [lambdaModulus, hpnat, hz]
  refine ⟨ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hLambdaNe, ?_⟩
  intro hprime
  have hchosen : selector p := by
    by_contra h
    exact hne (by rw [hcut y hy hprime h, mul_zero, zero_mul])
  have hA (i : Fin (ℓ + 1)) : x + (rescalePolynomial q (P i)).eval y ∈ A := by
    by_contra h
    apply hne
    have hfactor : (if x + (rescalePolynomial q (P i)).eval y ∈ A then (1 : ℂ) else 0) = 0 :=
      if_neg h
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hfactor, mul_zero]
  have hd : Function.Injective (fun i => x + (rescalePolynomial q (P i)).eval y) := by
    intro i j hij
    by_contra hneq
    apply hc
    exact Finset.mem_filter.mpr ⟨hy, i, j, hneq, add_left_cancel hij⟩
  apply hno
  refine ⟨x, y.toNat, hyp, hprime, hchosen, ?_, ?_⟩
  · simpa only [hycast] using hA
  · simpa only [hycast] using hd

set_option maxHeartbeats 800000 in
/-- Explicit finite exceptional-mass bound for the selected weighted count.
Only collision parameters and higher prime powers can contribute. -/
theorem norm_selected_count_le_exception_mass {ℓ q M N d : ℕ}
    (hq : 0 < q) (hN : 0 < N) (hM : 0 < M) (P : Fin (ℓ + 1) → Polynomial ℤ) (A : Finset ℤ)
    (hPinj : Function.Injective (fun i => (P i).natDegree)) (hdeg : ∀ i, (P i).natDegree ≤ d)
    (selector : ℕ → Prop) (hno : ¬ ContainsScaledConfiguration A P selector q)
    (F : ℤ → ℂ) (hF : ∀ y ∈ positiveInterval M, ‖F y‖ ≤ 1)
    (hcut : ∀ y ∈ positiveInterval M, (q * y.toNat + 1).Prime →
      ¬ selector (q * y.toNat + 1) → F y = 0) :
    ‖countingForm N M (positiveInterval N) (fun i => rescalePolynomial q (P i))
      (fun y => (lambdaModulus q y : ℂ) * F y)
      (fun _ z => if z ∈ A then (1 : ℂ) else 0)‖ ≤
      ((((ℓ + 1 : ℕ) : ℝ)^2 * (d : ℝ)) * Real.log (q * M + 1 : ℕ) +
       (4 / Real.log 2) * Real.sqrt (q * M + 1 : ℕ) * (Real.log (q * M + 1 : ℕ))^2) / (M : ℝ) := by
  classical
  let X := positiveInterval N
  let I := positiveInterval M
  let R := fun i => rescalePolynomial (q : ℤ) (P i)
  let Y := q * M + 1
  let p := fun y : ℤ => q * y.toNat + 1
  let C := coincidentShiftParameters R I
  have hq' : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
  have hRdeg (i : Fin (ℓ + 1)) : (R i).natDegree = (P i).natDegree :=
    natDegree_rescalePolynomial _ _ hq'
  have hRinj : Function.Injective R := by
    intro i j hij
    have hh := congrArg Polynomial.natDegree hij
    rw [hRdeg, hRdeg] at hh
    exact hPinj hh
  have hY : 2 ≤ Y := by have := Nat.mul_pos hq hM; omega
  let BadP := I.filter (fun y => IsPrimePow (p y) ∧ ¬ (p y).Prime)
  let badWeight (y : ℤ) : ℝ :=
    (if y ∈ C then Real.log Y else 0) +
      (if y ∈ BadP then ArithmeticFunction.vonMangoldt (p y) else 0)
  have hnat (y : ℤ) (hy : y ∈ I) : (y.toNat : ℤ) = y :=
    Int.toNat_of_nonneg (by have := (Finset.mem_Icc.mp hy).1; omega)
  have hpbound (y : ℤ) (hy : y ∈ I) : p y ≤ Y := by
    have hym := (Finset.mem_Icc.mp hy).2
    have hyt : y.toNat ≤ M := by have := hnat y hy; omega
    exact Nat.add_le_add_right (Nat.mul_le_mul_left q hyt) 1
  have hYlog : 0 ≤ Real.log Y := Real.log_nonneg (by exact_mod_cast (show 1 ≤ Y by omega))
  have hbad₀ (y : ℤ) : 0 ≤ badWeight y := by
    dsimp only [badWeight]
    apply add_nonneg
    · split_ifs <;> positivity
    · split_ifs
      · exact ArithmeticFunction.vonMangoldt_nonneg
      · exact le_rfl
  have hLambda_le (y : ℤ) (hy : y ∈ I) :
      ‖(lambdaModulus q y : ℂ)‖ ≤ ArithmeticFunction.vonMangoldt (p y) := by
    have hpnat : ((q : ℤ) * y + 1).toNat = p y := by
      have hcast : (p y : ℤ) = (q : ℤ) * y + 1 := by simp [p, hnat y hy]
      rw [← hcast]; simp
    simp only [lambdaModulus, hpnat]
    rw [Complex.norm_of_nonneg (mul_nonneg (by positivity)
      ArithmeticFunction.vonMangoldt_nonneg)]
    apply mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg
    exact (div_le_one (by exact_mod_cast hq)).2 (by exact_mod_cast Nat.totient_le q)
  let term (x y : ℤ) : ℂ := (lambdaModulus q y : ℂ) * F y *
    ∏ i, if x + (R i).eval y ∈ A then (1 : ℂ) else 0
  have hterm (x y : ℤ) (hy : y ∈ I) : ‖term x y‖ ≤ badWeight y := by
    by_cases hzero : term x y = 0
    · rw [hzero, norm_zero]; exact hbad₀ y
    have hprod : ‖∏ i, if x + (R i).eval y ∈ A then (1 : ℂ) else 0‖ ≤ 1 := by
      rw [norm_prod]
      exact Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => by split_ifs <;> simp)
    have hle : ‖term x y‖ ≤ ArithmeticFunction.vonMangoldt (p y) := by
      simp only [term, norm_mul]
      exact ((mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hprod).trans
        (mul_le_of_le_one_right (norm_nonneg _) (hF y hy))).trans (hLambda_le y hy)
    rcases selected_count_summand_exception P A selector hno F hcut x y hy hzero with hC | hP
    · change y ∈ C at hC
      have hp₀ : 0 < p y := by dsimp [p]; omega
      have hlog := Real.log_le_log (show 0 < (p y : ℝ) by exact_mod_cast hp₀)
        (show (p y : ℝ) ≤ (Y : ℝ) by exact_mod_cast hpbound y hy)
      have hΛ := ArithmeticFunction.vonMangoldt_le_log.trans hlog
      apply hle.trans (hΛ.trans _)
      dsimp only [badWeight]
      rw [if_pos hC]
      exact le_add_of_nonneg_right (by split_ifs; exact ArithmeticFunction.vonMangoldt_nonneg; exact le_rfl)
    · have hbad : y ∈ BadP := Finset.mem_filter.mpr ⟨hy, hP⟩
      apply hle.trans
      dsimp only [badWeight]
      rw [if_pos hbad]
      exact le_add_of_nonneg_left (by split_ifs; exact hYlog; exact le_rfl)
  have hmass : ∑ y ∈ I, badWeight y ≤
      ((((ℓ + 1 : ℕ) : ℝ)^2 * (d : ℝ)) * Real.log Y +
       (4 / Real.log 2) * Real.sqrt Y * (Real.log Y)^2) := by
    dsimp only [badWeight]
    rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter]
    have hc : I.filter (fun y => y ∈ C) = C :=
      Finset.filter_mem_eq_inter.trans (Finset.inter_eq_right.mpr (Finset.filter_subset _ _))
    rw [hc]
    simp only [Finset.sum_const, nsmul_eq_mul]
    apply add_le_add
    · apply mul_le_mul_of_nonneg_right _ hYlog
      have hcard := card_coincidentShiftParameters_le R hRinj (fun i => (hRdeg i).trans_le (hdeg i)) I
      exact_mod_cast hcard
    · have heq : I.filter (fun y => y ∈ BadP) = BadP :=
        Finset.filter_mem_eq_inter.trans (Finset.inter_eq_right.mpr (Finset.filter_subset _ _))
      rw [heq]
      have hinj : ∀ x ∈ BadP, ∀ y ∈ BadP, p x = p y → x = y := by
        intro x hx y hy hxy
        have hx' := hnat x (Finset.mem_filter.mp hx).1
        have hy' := hnat y (Finset.mem_filter.mp hy).1
        have he := Nat.eq_of_mul_eq_mul_left hq (Nat.add_right_cancel hxy)
        omega
      rw [← Finset.sum_image hinj]
      apply le_trans _ (higherPrimePowers_mangoldtMass_le hY)
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_
        (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
      intro v hv
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨hyI, hyp⟩ := Finset.mem_filter.mp hy
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (hpbound y hyI)), hyp⟩
  have hnum : ‖∑ x ∈ X, ∑ y ∈ I, term x y‖ ≤ (N : ℝ) * ∑ y ∈ I, badWeight y := calc
    _ ≤ ∑ x ∈ X, ∑ y ∈ I, ‖term x y‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun _ _ => norm_sum_le _ _))
    _ ≤ ∑ _ ∈ X, ∑ y ∈ I, badWeight y :=
      Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (hterm x))
    _ = _ := by simp [X, nsmul_eq_mul]
  simp only [countingForm, norm_div, Complex.norm_mul, Complex.norm_natCast]
  change ‖∑ x ∈ X, ∑ y ∈ I, term x y‖ / ((N : ℝ) * (M : ℝ)) ≤ _
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  refine (div_le_div_of_nonneg_right hnum (by positivity)).trans ?_
  rw [show (N : ℝ) * (∑ y ∈ I, badWeight y) / ((N : ℝ) * (M : ℝ)) =
      (∑ y ∈ I, badWeight y) / (M : ℝ) by field_simp; ring]
  exact div_le_div_of_nonneg_right hmass (by positivity)

end NilBohr
