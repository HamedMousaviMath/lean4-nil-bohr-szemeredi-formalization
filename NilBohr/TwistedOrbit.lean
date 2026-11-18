import NilBohr.OrbitEquidistribution
import NilBohr.LocalPhases
import NilBohr.Rotations

/-! Finite phase decomposition in the twisted Heisenberg argument. -/

open scoped BigOperators Nat
open Filter MeasureTheory Polynomial

namespace NilBohr

private theorem descPochhammer_eval_modEq (i : ℕ) {L t u : ℤ}
    (h : t ≡ u [ZMOD L]) :
    (descPochhammer ℤ i).eval t ≡ (descPochhammer ℤ i).eval u [ZMOD L] := by
  simp only [descPochhammer_eval_eq_prod_range]
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ]
    exact ih.mul (h.sub_right (i : ℤ))

/-- Congruence of parameter indices modulo `s*d!` gives congruence of every
binomial coefficient of order at most `d` modulo `s`. -/
theorem choose_modEq_of_modEq_factorial_mul {s d i t u : ℕ} (hi : i ≤ d)
    (h : t ≡ u [MOD s * d.factorial]) :
    t.choose i ≡ u.choose i [MOD s] := by
  have h' : (t : ℤ) ≡ (u : ℤ) [ZMOD ((s * d.factorial) : ℕ)] := Int.natCast_modEq_iff.mpr h
  have hpoly := (descPochhammer_eval_modEq i h').dvd
  rw [descPochhammer_eval_eq_descFactorial, descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose] at hpoly
  obtain ⟨a, ha⟩ := hpoly
  obtain ⟨b, hb⟩ := Nat.factorial_dvd_factorial hi
  apply Int.natCast_modEq_iff.mp
  apply Int.modEq_iff_dvd.mpr
  refine ⟨(b : ℤ) * a, ?_⟩
  have hfactorial : (i.factorial : ℤ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
  apply mul_left_cancel₀ hfactorial
  push_cast at ha
  rw [hb, Nat.cast_mul] at ha
  linear_combination ha

/-- The integer-valued polynomial obtained by rounding binomial coefficients. -/
def integerBinomialPhase (d : ℕ) (p : ℕ → ℤ) (t : ℕ) : ℤ :=
  ∑ i ∈ Finset.range d, p (i+1) * (t.choose (i+1) : ℤ)

theorem integerBinomialPhase_modEq_of_modEq_factorial_mul
    {s d t u : ℕ} (p : ℕ → ℤ) (h : t ≡ u [MOD s * d.factorial]) :
    integerBinomialPhase d p t ≡ integerBinomialPhase d p u [ZMOD s] := by
  unfold integerBinomialPhase
  apply Int.modEq_iff_dvd.mpr
  rw [← Finset.sum_sub_distrib]
  apply Finset.dvd_sum
  intro i hi
  have h' : (t.choose (i+1) : ℤ) ≡ (u.choose (i+1) : ℤ) [ZMOD s] :=
    Int.natCast_modEq_iff.mpr (choose_modEq_of_modEq_factorial_mul
      (Nat.succ_le_of_lt (Finset.mem_range.mp hi)) h)
  exact (h'.mul_left (p (i+1))).dvd

private theorem phase_int (n : ℤ) : phase (n : ℝ) = 1 := by
  unfold phase
  push_cast
  convert Complex.exp_int_mul_two_pi_mul_I n using 2
  ring

theorem phase_eq_of_sub_int {x y : ℝ} (h : ∃ a : ℤ, x = y + a) :
    phase x = phase y := by
  obtain ⟨a, rfl⟩ := h
  rw [phase_add, phase_int, mul_one]

/-- The rational phase produced by the integral coefficients is constant
on progressions of step `|m|*d!`, with the sign of `m` retained. -/
theorem integerBinomialPhase_exp_eq_of_modEq
    {m : ℤ} (hm : m ≠ 0) {d t u : ℕ} (p : ℕ → ℤ)
    (h : t ≡ u [MOD m.natAbs * d.factorial]) :
    phase (-(integerBinomialPhase d p t : ℝ) / m) =
      phase (-(integerBinomialPhase d p u : ℝ) / m) := by
  have hP := (integerBinomialPhase_modEq_of_modEq_factorial_mul p h).dvd
  have hmabs : m ∣ (m.natAbs : ℤ) := by simpa only [Int.natCast_natAbs] using self_dvd_abs m
  obtain ⟨z, hz⟩ := hmabs.trans hP
  apply phase_eq_of_sub_int
  refine ⟨z, ?_⟩
  have hz' : (integerBinomialPhase d p u : ℝ) - (integerBinomialPhase d p t : ℝ) =
      (m : ℝ) * (z : ℝ) := by exact_mod_cast hz
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  apply (div_eq_iff hm').2
  rw [add_mul, div_mul_cancel₀ _ hm']
  linarith

/-- A binomial polynomial without its constant term, on nonnegative indices. -/
noncomputable def realBinomialPhase (d : ℕ) (b : ℕ → ℝ) (t : ℕ) : ℝ :=
  ∑ i ∈ Finset.range d, b (i+1) * (t.choose (i+1) : ℝ)

theorem realBinomialPhase_round_split (d : ℕ) (b : ℕ → ℝ) (t : ℕ) :
    realBinomialPhase d b t = (integerBinomialPhase d (fun i => round (b i)) t : ℝ) +
      realBinomialPhase d (fun i => b i - (round (b i) : ℝ)) t := by
  rw [realBinomialPhase, integerBinomialPhase, Int.cast_sum, realBinomialPhase,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  push_cast
  ring

/-- Explicit form of the nearest-integer decomposition forced by a small
horizontal obstruction in the binomial basis. -/
theorem polynomialTwist_round_split {d : ℕ} {a v k l m : ℤ}
    (α β : ℝ) (psi : ℕ → ℝ) (b₀ : ℝ) (b : ℕ → ℝ)
    (hpsi : ∀ t : ℕ, (v : ℝ) * (k*α+l*β) * t + (m : ℝ)*psi t =
      b₀ + realBinomialPhase d b t) :
    ∃ (p : ℕ → ℤ) (e : ℕ → ℝ) (c : ℝ),
      (∀ i, |e i| = torusNorm (b i)) ∧
      ∀ t : ℕ, (m : ℝ)*psi t =
        -(k*α+l*β)*((a : ℝ) + v*t) + (integerBinomialPhase d p t : ℝ) +
          realBinomialPhase d e t + c := by
  refine ⟨fun i => round (b i), fun i => b i - (round (b i) : ℝ),
    b₀ + a*(k*α+l*β), fun i => (torusNorm_eq (b i)).symm, ?_⟩
  intro t
  have h := hpsi t
  rw [realBinomialPhase_round_split] at h
  linear_combination h

/-- The total variation of the small real remainder on the whole prefix.
The statement uses all increments starting at zero, so it also bounds the
increments from one to `K-1` used in the manuscript. -/
theorem realBinomialPhase_totalVariation_le
    {d K : ℕ} {B : ℝ} (hK : 0 < K) (e : ℕ → ℝ)
    (he : ∀ i ∈ Finset.range d, |e (i+1)| ≤ B / (K : ℝ)^(i+1)) :
    ∑ t ∈ Finset.range K,
      |realBinomialPhase d e (t+1) - realBinomialPhase d e t| ≤ (d : ℝ)*B := by
  calc
    _ ≤ ∑ t ∈ Finset.range K, ∑ i ∈ Finset.range d,
        |e (i+1)| * ((t+1).choose (i+1) - (t.choose (i+1) : ℝ)) := by
      apply Finset.sum_le_sum
      intro t ht
      unfold realBinomialPhase
      rw [← Finset.sum_sub_distrib]
      simp_rw [← mul_sub]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      apply Finset.sum_le_sum
      intro i hi
      have hmono : (t.choose (i+1) : ℝ) ≤ ((t+1).choose (i+1) : ℝ) := by
        exact_mod_cast Nat.choose_le_succ t (i+1)
      rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr hmono)]
    _ = ∑ i ∈ Finset.range d, |e (i+1)| * (K.choose (i+1) : ℝ) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.mul_sum, Finset.sum_range_sub (fun t : ℕ => (t.choose (i+1) : ℝ))]
      simp
    _ ≤ ∑ _i ∈ Finset.range d, B := by
      apply Finset.sum_le_sum
      intro i hi
      have hKpow : 0 < (K : ℝ) ^ (i+1) := by positivity
      have hBnonneg : 0 ≤ B / (K : ℝ)^(i+1) := (abs_nonneg _).trans (he i hi)
      calc
        _ ≤ (B / (K : ℝ)^(i+1)) * (K.choose (i+1) : ℝ) :=
          mul_le_mul_of_nonneg_right (he i hi) (by positivity)
        _ ≤ (B / (K : ℝ)^(i+1)) * (K : ℝ)^(i+1) :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.choose_le_pow K (i+1)) hBnonneg
        _ = B := div_mul_cancel₀ _ hKpow.ne'
    _ = _ := by simp [nsmul_eq_mul]


/-- The positive integer dilation of the Heisenberg group in coordinates. -/
def expandHeisenberg (s : ℕ) (g : HeisenbergPoint) : HeisenbergPoint :=
  ((s : ℝ)*g.1, (s : ℝ)*g.2.1, (s : ℝ)^2*g.2.2)

theorem expandHeisenberg_mul (s : ℕ) (g h : HeisenbergPoint) :
    expandHeisenberg s (heisenbergMul g h) =
      heisenbergMul (expandHeisenberg s g) (expandHeisenberg s h) := by
  simp only [expandHeisenberg, heisenbergMul, Prod.mk.injEq]
  exact ⟨by ring, by ring, by ring⟩

theorem expandHeisenberg_dilatedOrbit (α β : ℝ) {s : ℕ} (hs : 0 < s) (n : ℤ) :
    expandHeisenberg s (dilatedHeisenbergOrbit α β s n) = heisenbergOrbit α β n := by
  have hs' : (s : ℝ) ≠ 0 := by positivity
  unfold dilatedHeisenbergOrbit
  generalize heisenbergOrbit α β n = g
  obtain ⟨x, y, z⟩ := g
  simp only [expandHeisenberg, dilatedHeisenbergOrbit, Prod.mk.injEq]
  constructor
  · field_simp
  constructor <;> field_simp

/-- The covering test carries the horizontal character after resolving the
nonzero circle component of the obstruction. -/
noncomputable def heisenbergCoverTest (Φ : HeisenbergPoint → ℂ)
    (k l m : ℤ) (g : HeisenbergPoint) : ℂ :=
  Φ (expandHeisenberg m.natAbs g) * phase ((m.sign : ℝ) * (k*g.1 + l*g.2.1))

theorem heisenbergCoverTest_right_lattice
    (Φ : HeisenbergPoint → ℂ)
    (hΦ : ∀ g (u v w : ℤ), Φ (heisenbergMul g ((u : ℝ), (v : ℝ), (w : ℝ))) = Φ g)
    (k l m : ℤ) (g : HeisenbergPoint) (u v w : ℤ) :
    heisenbergCoverTest Φ k l m (heisenbergMul g ((u : ℝ), (v : ℝ), (w : ℝ))) =
      heisenbergCoverTest Φ k l m g := by
  unfold heisenbergCoverTest
  rw [expandHeisenberg_mul]
  have hlattice : expandHeisenberg m.natAbs ((u : ℝ), (v : ℝ), (w : ℝ)) =
      ((((m.natAbs : ℤ)*u : ℤ) : ℝ), (((m.natAbs : ℤ)*v : ℤ) : ℝ),
        ((((m.natAbs : ℤ)^2*w) : ℤ) : ℝ)) := by
    simp only [expandHeisenberg, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
  rw [hlattice, hΦ]
  congr 1
  apply phase_eq_of_sub_int
  refine ⟨m.sign*(k*u+l*v), ?_⟩
  simp only [heisenbergMul, Int.cast_mul, Int.cast_add]
  ring

theorem heisenbergCoverTest_dilatedOrbit (Φ : HeisenbergPoint → ℂ)
    (α β : ℝ) (k l : ℤ) {m : ℤ} (hm : m ≠ 0) (n : ℤ) :
    heisenbergCoverTest Φ k l m (dilatedHeisenbergOrbit α β m.natAbs n) =
      Φ (heisenbergOrbit α β n) * phase (((n : ℝ)*(k*α+l*β)) / m) := by
  have hS : 0 < m.natAbs := Int.natAbs_pos.mpr hm
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hs' : (m.natAbs : ℝ) ≠ 0 := by positivity
  have hsign : (m.sign : ℝ) * m = (m.natAbs : ℝ) := by
    simpa only [Int.cast_mul, Int.cast_natCast] using
      congrArg (fun z : ℤ => (z : ℝ)) (Int.sign_mul_self_eq_natAbs m)
  have hsignDiv : (m.sign : ℝ) / (m.natAbs : ℝ) = 1 / m := by
    apply (div_eq_div_iff hs' hm').mpr
    simpa using hsign
  unfold heisenbergCoverTest
  rw [expandHeisenberg_dilatedOrbit α β hS]
  congr 1
  apply congrArg phase
  simp only [dilatedHeisenbergOrbit, heisenbergOrbit]
  calc
    _ = ((m.sign : ℝ) / (m.natAbs : ℝ)) * ((n : ℝ)*(k*α+l*β)) := by ring
    _ = _ := by rw [hsignDiv]; ring

/-- Exact absorption of the linear part of the twist into the finite cover. -/
theorem twisted_point_eq_cover_of_round_split
    (Φ : HeisenbergPoint → ℂ) (α β : ℝ) (n k l : ℤ) {m : ℤ} (hm : m ≠ 0)
    (p : ℤ) (e c psi : ℝ)
    (hsplit : (m : ℝ)*psi = -(k*α+l*β)*n + p + e + c) :
    Φ (heisenbergOrbit α β n) * phase (-psi) =
      heisenbergCoverTest Φ k l m (dilatedHeisenbergOrbit α β m.natAbs n) *
        (phase (-(p : ℝ)/m) * phase (-e/m) * phase (-c/m)) := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have he : -psi = ((n : ℝ)*(k*α+l*β))/m + (-(p : ℝ)/m + -e/m + -c/m) := by
    rw [show ((n : ℝ)*(k*α+l*β))/m + (-(p : ℝ)/m + -e/m + -c/m) =
      ((n : ℝ)*(k*α+l*β) - p - e - c) / m by ring]
    apply (eq_div_iff hm').mpr
    linear_combination -hsplit
  rw [heisenbergCoverTest_dilatedOrbit Φ α β k l hm n, he]
  simp_rw [phase_add]
  ring

/-- The chart integral of the covering test is zero when every original vertical
fibre has zero integral. Periodicity follows from the central lattice. -/
theorem heisenbergCoverTest_chartMean_eq_zero (Φ : HeisenbergPoint → ℂ) (k l : ℤ)
    {m : ℤ} (hm : m ≠ 0)
    (hperiodic : ∀ x y, Function.Periodic (fun z => Φ (x,y,z)) 1)
    (hint : ∀ (x y a b : ℝ),
      IntervalIntegrable (fun z => Φ (x,y,z)) volume a b)
    (hzero : ∀ x y, (∫ z in (0 : ℝ)..1, Φ (x,y,z)) = 0) :
    heisenbergChartMean (heisenbergCoverTest Φ k l m) = 0 := by
  let s : ℕ := m.natAbs
  have hs : 0 < s := Int.natAbs_pos.mpr hm
  have hs₂ : (s : ℝ)^2 ≠ 0 := by positivity
  have h (x y : ℝ) : (∫ z in (0 : ℝ)..1, heisenbergCoverTest Φ k l m (x,y,z)) = 0 := by
    simp only [heisenbergCoverTest, expandHeisenberg, intervalIntegral.integral_mul_const]
    let f : ℝ → ℂ := fun z => Φ ((s : ℝ)*x, (s : ℝ)*y, z)
    change (∫ z in (0 : ℝ)..1, f ((s : ℝ)^2*z)) * _ = 0
    rw [intervalIntegral.integral_comp_mul_left f hs₂, mul_zero, mul_one]
    have hz := (hperiodic ((s : ℝ)*x) ((s : ℝ)*y)).intervalIntegral_add_zsmul_eq
      ((s : ℤ)^2) 0 (hint ((s : ℝ)*x) ((s : ℝ)*y))
    have h' : (∫ z in (0 : ℝ)..(s : ℝ)^2, f z) = 0 := by
      simpa only [f, zero_add, zsmul_eq_mul, Int.cast_pow, Int.cast_natCast, mul_one,
        hzero, smul_zero] using hz
    rw [h', smul_zero, zero_mul]
  simp [heisenbergChartMean, h]

/-- One-sided Abel summation with a uniform bound on unweighted prefixes. -/
theorem norm_weighted_prefix_le {J : ℕ} {B : ℝ}
    (F w : ℕ → ℂ) (hw : ∀ j, ‖w j‖ ≤ 1)
    (hF : ∀ j ≤ J, ‖∑ i ∈ Finset.range j, F i‖ ≤ B) :
    ‖∑ j ∈ Finset.range J, w j * F j‖ ≤
      (1 + ∑ j ∈ Finset.range (J-1), ‖w (j+1) - w j‖) * B := by
  have hab := Finset.sum_range_by_parts w F J
  simp only [smul_eq_mul] at hab
  rw [hab]
  calc
    _ ≤ ‖w (J-1) * ∑ i ∈ Finset.range J, F i‖ +
          ‖∑ j ∈ Finset.range (J-1), (w (j+1) - w j) * ∑ i ∈ Finset.range (j+1), F i‖ :=
      norm_sub_le _ _
    _ ≤ B + ∑ j ∈ Finset.range (J-1), ‖w (j+1) - w j‖ * B := by
      refine add_le_add ?_ ((norm_sum_le _ _).trans ?_)
      · rw [norm_mul, ← one_mul B]
        exact mul_le_mul (hw _) (hF J le_rfl) (norm_nonneg _) zero_le_one
      · apply Finset.sum_le_sum
        intro j hj
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left
          (hF _ (by have hmem := Finset.mem_range.mp hj; omega)) (norm_nonneg _)
    _ = _ := by rw [add_mul, one_mul, Finset.sum_mul]


/-- The number of indices `r+Lj` in the prefix of length `K`. -/
def residuePrefixLength (K L r : ℕ) : ℕ :=
  if r < K then (K-1-r)/L + 1 else 0

theorem lt_residuePrefixLength_iff {K L r j : ℕ} (hL : 0 < L) :
    j < residuePrefixLength K L r ↔ r+L*j < K := by
  unfold residuePrefixLength
  split_ifs with hr
  · rw [Nat.lt_succ_iff, Nat.le_div_iff_mul_le hL, mul_comm j L]
    omega
  · omega

theorem sum_filter_mod_eq_residuePrefixLength {R : Type*} [AddCommMonoid R]
    (f : ℕ → R) {K L r : ℕ} (hL : 0 < L) (hr : r < L) :
    (∑ t ∈ (Finset.range K).filter (fun t => t % L = r), f t) =
      ∑ j ∈ Finset.range (residuePrefixLength K L r), f (r+L*j) := by
  symm
  apply Finset.sum_bij (fun j _ => r+L*j)
  · intro j hj
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr ((lt_residuePrefixLength_iff hL).mp (Finset.mem_range.mp hj)),
        by simpa only [Nat.add_mul_mod_self_left] using Nat.mod_eq_of_lt hr⟩
  · intro j hj j' hj' h
    exact Nat.eq_of_mul_eq_mul_left hL (Nat.add_left_cancel h)
  · intro t ht
    have h := Finset.mem_filter.mp ht
    have he : r+L*(t/L) = t := by rw [← h.2, Nat.mod_add_div]
    refine ⟨t/L, Finset.mem_range.mpr ((lt_residuePrefixLength_iff hL).mpr ?_), he⟩
    rw [he]
    exact Finset.mem_range.mp h.1
  · intro j hj
    rfl

theorem sum_range_eq_sum_residuePrefix {R : Type*} [AddCommMonoid R]
    (f : ℕ → R) {K L : ℕ} (hL : 0 < L) :
    (∑ t ∈ Finset.range K, f t) =
      ∑ r ∈ Finset.range L, ∑ j ∈ Finset.range (residuePrefixLength K L r), f (r+L*j) := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun t : ℕ => t % L)
    (t := Finset.range L) (fun t _ => Finset.mem_range.mpr (Nat.mod_lt _ hL))]
  refine Finset.sum_congr rfl fun r hr => ?_
  exact sum_filter_mod_eq_residuePrefixLength f hL (Finset.mem_range.mp hr)

theorem sum_residuePrefixLength {K L : ℕ} (hL : 0 < L) :
    ∑ r ∈ Finset.range L, residuePrefixLength K L r = K := by
  simpa using (sum_range_eq_sum_residuePrefix (K := K) (fun _ => 1 : ℕ → ℕ) hL).symm

/-- Restriction to an increasing progression does not increase total
variation. The endpoint hypothesis also allows an empty progression. -/
theorem progression_totalVariation_le {A : Type*} [PseudoMetricSpace A]
    (f : ℕ → A) (a L R K : ℕ) (hend : a+L*(R-1) ≤ K) :
    ∑ j ∈ Finset.range (R-1), dist (f (a+L*(j+1))) (f (a+L*j)) ≤
      ∑ t ∈ Finset.range K, dist (f (t+1)) (f t) := by
  let P (n : ℕ) : ℝ := ∑ t ∈ Finset.range n, dist (f (t+1)) (f t)
  have hmono : Monotone P := fun n m hnm =>
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hnm)
      (fun _ _ _ => dist_nonneg)
  have hdist (x y : ℕ) (hxy : x ≤ y) : dist (f y) (f x) ≤ P y - P x := by
    rw [dist_comm]
    apply (dist_le_Ico_sum_dist f hxy).trans_eq
    rw [← Finset.sum_Ico_eq_sub _ hxy]
    exact Finset.sum_congr rfl (fun _ _ => dist_comm _ _)
  calc
    _ ≤ ∑ j ∈ Finset.range (R-1), (P (a+L*(j+1)) - P (a+L*j)) :=
      Finset.sum_le_sum (fun j _ => hdist _ _ (by rw [Nat.mul_succ]; omega))
    _ = P (a+L*(R-1)) - P a := by
      rw [Finset.sum_range_sub (fun j => P (a+L*j)), mul_zero, add_zero]
    _ ≤ _ := by
      have hPa : 0 ≤ P a := Finset.sum_nonneg (fun _ _ => dist_nonneg)
      exact (sub_le_self _ hPa).trans (hmono hend)

/-- Lipschitz control of the circle exponential on real representatives. -/
theorem phase_lipschitz_exists :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : ℝ, ‖phase x - phase y‖ ≤ C*|x-y| := by
  obtain ⟨C, hC⟩ := exists_lipschitzWith_fourier 1
  refine ⟨(C : ℝ), C.coe_nonneg, ?_⟩
  intro x y
  have heq (z : ℝ) : fourier (T := 1) 1 (z : Circle) = phase z := by
    rw [fourier_coe_apply]
    simp [phase]
  have h := hC.dist_le_mul (x : Circle) (y : Circle)
  rw [heq, heq, dist_eq_norm, dist_eq_norm, ← AddCircle.coe_sub] at h
  exact h.trans (mul_le_mul_of_nonneg_left (torusNorm_le_abs (x-y)) C.coe_nonneg)


theorem realBinomialPhase_exp_totalVariation_le {d K : ℕ} {m : ℤ} (hm : m ≠ 0)
    {B C : ℝ} (hC : 0 ≤ C) (hLip : ∀ x y : ℝ, ‖phase x - phase y‖ ≤ C*|x-y|)
    (hK : 0 < K) (e : ℕ → ℝ)
    (he : ∀ i ∈ Finset.range d, |e (i+1)| ≤ B / (K : ℝ)^(i+1)) :
    ∑ t ∈ Finset.range K,
      dist (phase (-realBinomialPhase d e (t+1)/m)) (phase (-realBinomialPhase d e t/m)) ≤
      C * ((d : ℝ)*B) := by
  have hmabs : (1 : ℝ) ≤ |(m : ℝ)| := by
    have hnat : 1 ≤ m.natAbs := Int.natAbs_pos.mpr hm
    have hreal : (1 : ℝ) ≤ (m.natAbs : ℝ) := by exact_mod_cast hnat
    simpa only [← Int.cast_abs, ← Int.natCast_natAbs] using hreal
  calc
    _ ≤ ∑ t ∈ Finset.range K, C * |realBinomialPhase d e (t+1) - realBinomialPhase d e t| := by
      apply Finset.sum_le_sum
      intro t ht
      rw [dist_eq_norm]
      refine (hLip _ _).trans (mul_le_mul_of_nonneg_left ?_ hC)
      rw [← sub_div, neg_sub_neg, abs_div, abs_sub_comm]
      exact div_le_self (abs_nonneg _) hmabs
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (realBinomialPhase_totalVariation_le hK e he) hC

/-- The original twisted sum, written with a zero-based summation index. -/
noncomputable def heisenbergTwistedSum (Φ : HeisenbergPoint → ℂ) (α β : ℝ)
    (a v : ℤ) (K : ℕ) (psi : ℕ → ℝ) : ℂ :=
  ∑ t ∈ Finset.range K,
    Φ (heisenbergOrbit α β (a+v*((t : ℤ)+1))) * phase (-psi (t+1))

/-- The unweighted sequence on the finite Heisenberg cover. -/
noncomputable def heisenbergCoverSequence (Φ : HeisenbergPoint → ℂ) (α β : ℝ)
    (a v k l m : ℤ) (t : ℕ) : ℂ :=
  heisenbergCoverTest Φ k l m
    (dilatedHeisenbergOrbit α β m.natAbs (a + v*(t+1 : ℕ)))

/-- The finite residue-class and partial-summation reduction. Here `bound r`
bounds each scalar cover prefix in the class `r`. These are the prefix sums
to which the manuscript applies its untwisted equidistribution estimate. -/
theorem norm_heisenbergTwistedSum_le_of_cover_prefixes :
    ∃ C : ℝ, 0 ≤ C ∧
    ∀ {d K : ℕ} {a v k l m : ℤ} (_hm : m ≠ 0) (_hK : 0 < K)
      (Φ : HeisenbergPoint → ℂ) (α β : ℝ) (psi : ℕ → ℝ)
      (b₀ : ℝ) (b : ℕ → ℝ) (B : ℝ) (bound : ℕ → ℝ),
    (∀ t : ℕ, (v : ℝ)*(k*α+l*β)*t + (m : ℝ)*psi t =
      b₀ + realBinomialPhase d b t) →
    (∀ i ∈ Finset.range d, torusNorm (b (i+1)) ≤ B / (K : ℝ)^(i+1)) →
    (∀ r < m.natAbs*d !, ∀ J ≤ residuePrefixLength K (m.natAbs*d !) r,
      ‖∑ j ∈ Finset.range J,
        heisenbergCoverSequence Φ α β a v k l m (r+(m.natAbs*d !)*j)‖ ≤ bound r) →
    ‖heisenbergTwistedSum Φ α β a v K psi‖ ≤
      (1 + C*((d : ℝ)*B)) * ∑ r ∈ Finset.range (m.natAbs*d !), bound r := by
  obtain ⟨C, hC, hLip⟩ := phase_lipschitz_exists
  refine ⟨C, hC, ?_⟩
  intro d K a v k l m hm hK Φ α β psi b₀ b B bound hpoly hB hprefix
  obtain ⟨p, e, c, he, hsplit⟩ := polynomialTwist_round_split (a := a) α β psi b₀ b hpoly
  let L : ℕ := m.natAbs * d.factorial
  have hL : 0 < L := Nat.mul_pos (Int.natAbs_pos.mpr hm) (Nat.factorial_pos _)
  let F : ℕ → ℂ := heisenbergCoverSequence Φ α β a v k l m
  let w : ℕ → ℂ := fun t => phase (-realBinomialPhase d e t/m)
  let G : ℕ → ℂ := fun t =>
    Φ (heisenbergOrbit α β (a+v*((t : ℤ)+1))) * phase (-psi (t+1))
  have hvar : ∑ t ∈ Finset.range K, dist (w (t+1)) (w t) ≤ C*((d : ℝ)*B) :=
    realBinomialPhase_exp_totalVariation_le hm hC hLip hK e (fun i hi => he _ ▸ hB i hi)
  have hfactor : 0 ≤ 1 + C*((d : ℝ)*B) := by
    have hp : 0 ≤ C*((d : ℝ)*B) := (Finset.sum_nonneg (fun _ _ => dist_nonneg)).trans hvar
    linarith
  have hclass (r : ℕ) (hr : r < L) :
      ‖∑ t ∈ Finset.range (residuePrefixLength K L r), G (r+L*t)‖ ≤
        (1 + C*((d : ℝ)*B)) * bound r := by
    let R := residuePrefixLength K L r
    have hb : 0 ≤ bound r := by simpa using hprefix r hr 0 (Nat.zero_le _)
    by_cases hR : R = 0
    · change ‖∑ t ∈ Finset.range R, G (r+L*t)‖ ≤ _
      simp [hR, mul_nonneg hfactor hb]
    let z := phase (-(integerBinomialPhase d p (r+1) : ℝ)/m) * phase (-c/m)
    have hG (j : ℕ) :
        G (r+L*j) = z * (w (r+1+L*j) * F (r+L*j)) := by
      let t := r+L*j
      have hcast : (a : ℝ) + v*(t+1 : ℕ) = ((a+v*(t+1 : ℕ) : ℤ) : ℝ) := by push_cast; ring
      have hts := hsplit (t+1)
      rw [hcast] at hts
      have hG' := twisted_point_eq_cover_of_round_split Φ α β (a+v*(t+1 : ℕ)) k l hm
        (integerBinomialPhase d p (t+1)) (realBinomialPhase d e (t+1)) c (psi (t+1)) hts
      have hmod : t+1 ≡ r+1 [MOD L] := by
        have hmod' : t ≡ r [MOD L] := by
          change (r+L*j)%L = r%L
          rw [Nat.add_mul_mod_self_left]
        exact hmod'.add_right 1
      rw [integerBinomialPhase_exp_eq_of_modEq hm p hmod] at hG'
      change Φ (heisenbergOrbit α β (a+v*((t : ℤ)+1))) * phase (-psi (t+1)) =
        z * (w (r+1+L*j) * F t)
      rw [show (t : ℤ)+1 = (↑(t+1) : ℤ) by push_cast; ring, hG']
      have ht : r+1+L*j = t+1 := by dsimp [t]; omega
      unfold z w F heisenbergCoverSequence
      rw [ht]
      ring
    have hv : ∑ j ∈ Finset.range (R-1), ‖w (r+1+L*(j+1)) - w (r+1+L*j)‖ ≤ C*((d : ℝ)*B) := by
      have hx := (lt_residuePrefixLength_iff hL).mp
        (show R-1 < residuePrefixLength K L r from Nat.sub_lt (Nat.pos_of_ne_zero hR) zero_lt_one)
      have hend : r+1+L*(R-1) ≤ K := by omega
      simpa only [dist_eq_norm] using (progression_totalVariation_le w (r+1) L R K hend).trans hvar
    change ‖∑ t ∈ Finset.range R, G (r+L*t)‖ ≤ _
    simp_rw [hG, ← Finset.mul_sum, norm_mul, z, norm_mul, norm_phase, one_mul]
    refine (norm_weighted_prefix_le (fun j => F (r+L*j)) (fun j => w (r+1+L*j))
      (fun _ => (norm_phase _).le) (hprefix r hr)).trans ?_
    exact mul_le_mul_of_nonneg_right (add_le_add_left hv _) hb
  change ‖∑ t ∈ Finset.range K, G t‖ ≤ _
  rw [sum_range_eq_sum_residuePrefix G hL]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun r hr => hclass r (Finset.mem_range.mp hr))


private theorem exists_descPochhammer_expansion (d : ℕ) (f : Polynomial ℝ)
    (hf : f.natDegree ≤ d) :
    ∃ c : ℕ → ℝ, f = ∑ i ∈ Finset.range (d+1), C (c i) * descPochhammer ℝ i := by
  induction d generalizing f with
  | zero =>
    refine ⟨fun _ => f.coeff 0, ?_⟩
    simpa using eq_C_of_natDegree_le_zero hf
  | succ d ih =>
    let lead := f.coeff (d+1)
    let Q := f-C lead * descPochhammer ℝ (d+1)
    have hQdegree : Q.natDegree ≤ d+1 := by
      simpa only [Q, max_self] using
        natDegree_sub_le_of_le hf ((natDegree_C_mul_le lead (descPochhammer ℝ (d+1))).trans_eq
          (descPochhammer_natDegree ℝ (d+1)))
    have hlead : Q.coeff (d+1) = 0 := by
      have h₁ := (monic_descPochhammer ℝ (d+1)).coeff_natDegree
      rw [descPochhammer_natDegree] at h₁
      simp [Q, lead, h₁]
    have hQ : Q.natDegree ≤ d := by
      by_cases hle : Q.natDegree ≤ d
      · exact hle
      · exfalso
        have heq : Q.natDegree = d+1 := by omega
        have hpos : 0 < Q.natDegree := by omega
        have hn : Q ≠ 0 := ne_zero_of_natDegree_gt hpos
        exact (leadingCoeff_ne_zero.mpr hn) (by rwa [← coeff_natDegree, heq])
    obtain ⟨c, hrep⟩ := ih Q hQ
    refine ⟨fun i => if i = d+1 then lead else c i, ?_⟩
    rw [Finset.sum_range_succ]
    simp only [if_pos rfl]
    have hsum :
        (∑ i ∈ Finset.range (d+1), C (if i=d+1 then lead else c i) * descPochhammer ℝ i) =
         ∑ i ∈ Finset.range (d+1), C (c i) * descPochhammer ℝ i := by
      exact Finset.sum_congr rfl (fun i hi => by rw [if_neg (Finset.mem_range.mp hi).ne])
    rw [hsum, ← hrep]
    unfold Q
    exact (sub_add_cancel _ _).symm

/-- The binomial basis gives the precise coefficient expression occurring
in the horizontal `C∞[K]` seminorm. -/
theorem exists_binomialPhase_expansion (d : ℕ) (f : Polynomial ℝ) (hf : f.natDegree ≤ d) :
    ∃ (b₀ : ℝ) (b : ℕ → ℝ), ∀ t : ℕ, f.eval (t : ℝ) = b₀ + realBinomialPhase d b t := by
  obtain ⟨c, hc⟩ := exists_descPochhammer_expansion d f hf
  refine ⟨c 0, fun i => c i * (i.factorial : ℝ), fun t => ?_⟩
  rw [hc, eval_finset_sum]
  simp only [eval_C_mul, descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, ← mul_assoc]
  rw [Finset.sum_range_succ']
  simp [realBinomialPhase, Nat.choose_zero_right, add_comm]


theorem sum_positiveInterval_eq_zero_prefix {R : Type*} [AddCommMonoid R]
    (f : ℤ → R) (J : ℕ) :
    (∑ t ∈ positiveInterval J, f t) = ∑ j ∈ Finset.range J, f ((j : ℤ)+1) := by
  unfold positiveInterval
  symm
  apply Finset.sum_bij (fun (j : ℕ) _ => (j : ℤ)+1)
  · intro j hj
    have hj' := Finset.mem_range.mp hj
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro j hj j' hj' he
    omega
  · intro t ht
    obtain ⟨ht₁, ht₂⟩ := Finset.mem_Icc.mp ht
    refine ⟨(t-1).toNat, Finset.mem_range.mpr ?_, ?_⟩ <;> omega
  · intro j hj
    rfl

/-- Reindex the original one-based phase average as the finite twisted sum. -/
theorem phaseAverage_eq_heisenbergTwistedSum (Φ : HeisenbergPoint → ℂ) (α β : ℝ)
    (a v : ℤ) (K : ℕ) (p : Polynomial ℝ) :
    phaseAverage (positiveInterval K) (fun t => Φ (heisenbergOrbit α β (a+v*t))) p =
      heisenbergTwistedSum Φ α β a v K (fun t => p.eval (t : ℝ)) / (K : ℂ) := by
  have hcard : (positiveInterval K).card = K := by simp [positiveInterval, Int.card_Icc]
  simp only [phaseAverage, heisenbergTwistedSum, sum_positiveInterval_eq_zero_prefix,
    hcard, Int.cast_add, Int.cast_one, Int.cast_natCast, Nat.cast_add, Nat.cast_one]

/-- A residue prefix on the cover is the scalar average at the shifted
origin and multiplied step. The factor `J` accounts for normalization. -/
theorem heisenbergCoverSequence_prefix_eq_scalarAverage
    (Φ : HeisenbergPoint → ℂ) (α β : ℝ) (a k l m : ℤ) (v L r J : ℕ) :
    (∑ j ∈ Finset.range J, heisenbergCoverSequence Φ α β a (v : ℤ) k l m (r+L*j)) =
      (J : ℂ) * heisenbergOrbitAverage α β (a+(v : ℤ)*((r : ℤ)+1-L)) (v*L) m.natAbs J
        (heisenbergCoverTest Φ k l m) := by
  unfold heisenbergOrbitAverage
  by_cases hJ : J = 0
  · simp [hJ]
  have hk : (J : ℂ) ≠ 0 := by exact_mod_cast hJ
  rw [mul_comm (J : ℂ), div_mul_cancel₀ _ hk, sum_positiveInterval_eq_zero_prefix]
  apply Finset.sum_congr rfl
  intro j hj
  unfold heisenbergCoverSequence
  push_cast
  congr 2
  ring

/-- Uniform bounds for the long scalar prefixes and the uniform bound on the
covering integrand control every prefix. This is the short-prefix split. -/
theorem norm_heisenbergCoverSequence_prefix_le
    (Φ : HeisenbergPoint → ℂ) (α β : ℝ) (a k l m : ℤ) (v L r J : ℕ)
    (τ U ε : ℝ) (hU : 0 ≤ U) (hε : 0 ≤ ε)
    (hbound : ∀ g, ‖Φ g‖ ≤ U)
    (hlong : τ ≤ (J : ℝ) →
      ‖heisenbergOrbitAverage α β (a+(v : ℤ)*((r : ℤ)+1-L)) (v*L) m.natAbs J
          (heisenbergCoverTest Φ k l m)‖ ≤ ε)
    (hτ : 0 ≤ τ) :
    ‖∑ j ∈ Finset.range J, heisenbergCoverSequence Φ α β a (v : ℤ) k l m (r+L*j)‖ ≤
      (J : ℝ)*ε + τ*U := by
  by_cases hJ : τ ≤ (J : ℝ)
  · rw [heisenbergCoverSequence_prefix_eq_scalarAverage]
    rw [norm_mul, Complex.norm_natCast]
    exact ((mul_le_mul_of_nonneg_left (hlong hJ) (by positivity)).trans
      (le_add_of_nonneg_right (mul_nonneg hτ hU)))
  · calc
      _ ≤ ∑ j ∈ Finset.range J, ‖heisenbergCoverSequence Φ α β a (v : ℤ) k l m (r+L*j)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _j ∈ Finset.range J, U := by
        apply Finset.sum_le_sum
        intro j hj
        unfold heisenbergCoverSequence heisenbergCoverTest
        rw [norm_mul, norm_phase, mul_one]
        exact hbound _
      _ = (J : ℝ)*U := by simp [nsmul_eq_mul]
      _ ≤ τ*U := mul_le_mul_of_nonneg_right (le_of_not_ge hJ) hU
      _ ≤ _ := le_add_of_nonneg_left (mul_nonneg (by positivity) hε)

private theorem realBinomialPhase_apply_zero (d : ℕ) (b : ℕ → ℝ) :
    realBinomialPhase d b 0 = 0 := by
  simp [realBinomialPhase]

private theorem realBinomialPhase_apply_one {d : ℕ} (hd : 0 < d) (b : ℕ → ℝ) :
    realBinomialPhase d b 1 = b 1 := by
  unfold realBinomialPhase
  obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
  rw [Finset.sum_range_succ']
  have hzero : (∑ i ∈ Finset.range e, b (i+1+1) * ((1 : ℕ).choose (i+1+1) : ℝ)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hn : 1 < i + 1 + 1 := by omega
    rw [Nat.choose_eq_zero_of_lt hn, Nat.cast_zero, mul_zero]
  rw [hzero]
  simp

/-- If the circle coefficient vanishes, evaluating at zero and one
recovers the pure horizontal coefficient. -/
theorem binomial_obstruction_horizontal_coefficient {d : ℕ} (hd : 0 < d)
    (g b₀ : ℝ) (b : ℕ → ℝ)
    (h : ∀ t : ℕ, g*t = b₀+realBinomialPhase d b t) :
    b 1 = g := by
  have hz := h 0
  simp only [Nat.cast_zero, mul_zero, realBinomialPhase_apply_zero, add_zero] at hz
  have h₁ := h 1
  rw [← hz, realBinomialPhase_apply_one hd, zero_add, Nat.cast_one, mul_one] at h₁
  exact h₁.symm

/-- Explicit product specialization of Green–Tao Theorem 2.9. The
assumption is a horizontal obstruction for a Heisenberg orbit and a
degree-`d` polynomial on the filtered circle. The checked deduction from the
general theorem is `productHeisenbergObstruction_of_greenTao`. -/
def ProductHeisenbergObstruction : Prop :=
  ∀ (d : ℕ), 0 < d → ∃ C D : ℝ, 1 ≤ C ∧ 0 < D ∧
    ∀ (α β : ℝ) (a : ℤ) (v K : ℕ), 0 < v → 1 < K →
    ∀ (Φ : HeisenbergPoint → ℂ) (U δ : ℝ), 0 < δ → δ < 1/2 →
    HeisenbergLipschitzNormLE Φ U → ∀ poly : Polynomial ℝ, poly.natDegree ≤ d →
    δ*U < ‖heisenbergTwistedSum Φ α β a (v : ℤ) K (fun t => poly.eval (t : ℝ)) / (K : ℂ)‖ →
    ∃ (k l m : ℤ) (b₀ : ℝ) (b : ℕ → ℝ),
      (k ≠ 0 ∨ l ≠ 0 ∨ m ≠ 0) ∧
      max |(k : ℝ)| (max |(l : ℝ)| |(m : ℝ)|) ≤ C * δ^(-D) ∧
      (∀ t : ℕ, (v : ℝ)*(k*α+l*β)*t + (m : ℝ)*poly.eval (t : ℝ) =
        b₀ + realBinomialPhase d b t) ∧
      ∀ i ∈ Finset.range d, (K : ℝ)^(i+1) * torusNorm (b (i+1)) ≤ C * δ^(-D)


/-- The finite implication from the product obstruction and the untwisted
long scalar cover estimates to an explicit twisted bound. The two loss terms
are the long-prefix error and the cost of short prefixes, respectively. -/
theorem norm_heisenbergTwistedAverage_le_of_product_obstruction
    (hGT : ProductHeisenbergObstruction) (d : ℕ) (hd : 0 < d) :
    ∃ C D C₁ : ℝ, 1 ≤ C ∧ 0 < D ∧ 0 ≤ C₁ ∧
      ∀ (α β U δ ε τ : ℝ) (a : ℤ) (v K : ℕ) (Φ : HeisenbergPoint → ℂ)
        (poly : Polynomial ℝ),
      0 < v → 1 < K → 0 < δ → δ < 1/2 → 0 ≤ ε → 0 ≤ τ →
      HeisenbergLipschitzNormLE Φ U → poly.natDegree ≤ d →
      let H := C * δ^(-D)
      (∀ k l : ℤ, (k ≠ 0 ∨ l ≠ 0) → max |(k : ℝ)| |(l : ℝ)| ≤ H →
        H < (K : ℝ)*torusNorm ((v : ℝ)*(k*α+l*β))) →
      (∀ k l m : ℤ, m ≠ 0 → max |(k : ℝ)| (max |(l : ℝ)| |(m : ℝ)|) ≤ H →
        ∀ r < m.natAbs * d.factorial, ∀ J : ℕ, τ ≤ (J : ℝ) →
          ‖heisenbergOrbitAverage α β
            (a+(v : ℤ)*((r : ℤ)+1-(m.natAbs*d.factorial : ℕ)))
            (v*(m.natAbs*d.factorial)) m.natAbs J (heisenbergCoverTest Φ k l m)‖ ≤ ε) →
      ‖heisenbergTwistedSum Φ α β a (v : ℤ) K (fun t => poly.eval (t : ℝ)) / (K : ℂ)‖ ≤
        max (δ*U) ((1+C₁*((d : ℝ)*H))*
          (ε+(H*(d.factorial : ℝ))*τ*U / (K : ℝ))) := by
  obtain ⟨C, D, hC, hD, hgt⟩ := hGT d hd
  obtain ⟨C₁, hC₁, hab⟩ := norm_heisenbergTwistedSum_le_of_cover_prefixes
  refine ⟨C, D, C₁, hC, hD, hC₁, ?_⟩
  intro α β U δ ε τ a v K Φ poly hv hK hδ hδ₂ hε hτ hΦ hdeg H hhoriz hlong
  by_cases hsmall : ‖heisenbergTwistedSum Φ α β a (v : ℤ) K
      (fun t => poly.eval (t : ℝ)) / (K : ℂ)‖ ≤ δ*U
  · exact hsmall.trans (le_max_left _ _)
  have hUb : ∀ g, ‖Φ g‖ ≤ U := by
    obtain ⟨_, S, M, _, hM, hSM, hS, _⟩ := hΦ
    intro g
    exact (hS g).trans (by linarith)
  have hU : 0 ≤ U := (norm_nonneg _).trans (hUb (0,0,0))
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hKpos : 0 < K := Nat.zero_lt_one.trans hK
  obtain ⟨k, l, m, b₀, b, hnonzero, hsize, hcoeff, hsmallCoeff⟩ :=
    hgt α β a v K hv hK Φ U δ hδ hδ₂ hΦ poly hdeg (lt_of_not_ge hsmall)
  change max |(k : ℝ)| (max |(l : ℝ)| |(m : ℝ)|) ≤ H at hsize
  have hml : m ≠ 0 := by
    intro hm
    subst m
    have hpair : k ≠ 0 ∨ l ≠ 0 := by simpa using hnonzero
    have hsmall_pair : max |(k : ℝ)| |(l : ℝ)| ≤ H := by
      rw [max_le_iff] at hsize ⊢
      exact ⟨hsize.1, (le_max_left _ _).trans hsize.2⟩
    have hb₁ :=
      binomial_obstruction_horizontal_coefficient hd ((v : ℝ)*(k*α+l*β)) b₀ b
        (fun t => by simpa using hcoeff t)
    have hb₀ := hsmallCoeff 0 (Finset.mem_range.mpr hd)
    simp only [zero_add, pow_one, hb₁] at hb₀
    exact (not_lt_of_ge hb₀) (hhoriz k l hpair hsmall_pair)
  let L := m.natAbs*d.factorial
  have hL : 0 < L := Nat.mul_pos (Int.natAbs_pos.mpr hml) (Nat.factorial_pos _)
  have hLsize : (L : ℝ) ≤ H*(d.factorial : ℝ) := by
    have hs : (m.natAbs : ℝ) ≤ H := by
      have hma := (le_max_right |(l : ℝ)| |(m : ℝ)|).trans ((le_max_right _ _).trans hsize)
      simpa only [← Int.cast_abs, ← Int.natCast_natAbs] using hma
    simpa only [L, Nat.cast_mul] using mul_le_mul_of_nonneg_right hs (by positivity : 0 ≤ (d.factorial : ℝ))
  have hbound (i : ℕ) (hi : i ∈ Finset.range d) :
      torusNorm (b (i+1)) ≤ H / (K : ℝ)^(i+1) := by
    apply (le_div_iff₀ (by positivity)).mpr
    rw [mul_comm]
    exact hsmallCoeff i hi
  let bound (r : ℕ) : ℝ := (residuePrefixLength K L r : ℝ)*ε + τ*U
  have hprefix (r : ℕ) (hr : r < L) (J : ℕ) (hJ : J ≤ residuePrefixLength K L r) :
      ‖∑ j ∈ Finset.range J, heisenbergCoverSequence Φ α β a (v : ℤ) k l m (r+L*j)‖ ≤ bound r := by
    refine (norm_heisenbergCoverSequence_prefix_le Φ α β a k l m v L r J τ U ε hU hε hUb
      (hlong k l m hml hsize r hr J) hτ).trans ?_
    unfold bound
    gcongr
  have hab' := hab hml hKpos Φ α β (fun t => poly.eval (t : ℝ)) b₀ b H bound hcoeff hbound hprefix
  have hsum : ∑ r ∈ Finset.range L, bound r = (K : ℝ)*ε + (L : ℝ)*(τ*U) := by
    unfold bound
    rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    have hsum' : (∑ r ∈ Finset.range L, (residuePrefixLength K L r : ℝ)) = (K : ℝ) := by
      exact_mod_cast sum_residuePrefixLength (K := K) hL
    rw [hsum']
    simp [nsmul_eq_mul]
  change ‖heisenbergTwistedSum Φ α β a (v : ℤ) K (fun t => poly.eval (t : ℝ))‖ ≤
    (1+C₁*((d : ℝ)*H)) * ∑ r ∈ Finset.range L, bound r at hab'
  rw [hsum] at hab'
  apply le_trans _ (le_max_right _ _)
  rw [norm_div, Complex.norm_natCast]
  calc
    _ ≤ ((1+C₁*((d : ℝ)*H)) * ((K : ℝ)*ε + (L : ℝ)*(τ*U))) / (K : ℝ) :=
      div_le_div_of_nonneg_right hab' (by positivity)
    _ = (1+C₁*((d : ℝ)*H)) * (ε + (L : ℝ)*τ*U/(K : ℝ)) := by
      have hK' : (K : ℝ) ≠ 0 := by positivity
      rw [mul_div_assoc, add_div, mul_div_cancel_left₀ ε hK']
      ring
    _ ≤ _ := by gcongr


section CoverMetric

private noncomputable def heisenbergChainLength (x : ℕ → HeisenbergPoint) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range j,
    min (heisenbergMalcevNorm (heisenbergMul (x i) (heisenbergInv (x (i+1)))))
      (heisenbergMalcevNorm (heisenbergMul (x (i+1)) (heisenbergInv (x i))))

private def heisenbergChainLengths (g h : HeisenbergPoint) : Set ℝ :=
  {d | ∃ (n : ℕ) (x : ℕ → HeisenbergPoint), x 0 = g ∧ x n = h ∧ d = heisenbergChainLength x n}

private theorem heisenbergChainLength_nonneg (x : ℕ → HeisenbergPoint) (j : ℕ) :
    0 ≤ heisenbergChainLength x j := by
  apply Finset.sum_nonneg
  intro i hi
  unfold heisenbergMalcevNorm
  positivity

private theorem heisenbergChainLengths_nonempty (g h : HeisenbergPoint) :
    (heisenbergChainLengths g h).Nonempty := by
  let x : ℕ → HeisenbergPoint := fun i => if i=0 then g else h
  exact ⟨_, 1, x, by simp [x], by simp [x], rfl⟩

private theorem heisenbergChainLengths_bddBelow (g h : HeisenbergPoint) :
    BddBelow (heisenbergChainLengths g h) := by
  refine ⟨0, ?_⟩
  rintro v ⟨n, x, _, _, rfl⟩
  exact heisenbergChainLength_nonneg x n

private theorem heisenbergGroupDistance_nonneg (g h : HeisenbergPoint) :
    0 ≤ heisenbergGroupDistance g h := by
  apply Real.sInf_nonneg
  rintro v ⟨n, x, _, _, rfl⟩
  exact heisenbergChainLength_nonneg x n

private theorem heisenbergGroupDistance_le_chain {g h : HeisenbergPoint} (n : ℕ)
    (x : ℕ → HeisenbergPoint) (hx₀ : x 0 = g) (hxn : x n = h) :
    heisenbergGroupDistance g h ≤ heisenbergChainLength x n :=
  csInf_le (heisenbergChainLengths_bddBelow g h) ⟨n, x, hx₀, hxn, rfl⟩

private theorem heisenbergGroupDistance_le_relative (g h : HeisenbergPoint) :
    heisenbergGroupDistance g h ≤ heisenbergMalcevNorm (heisenbergMul g (heisenbergInv h)) := by
  let x : ℕ → HeisenbergPoint := fun i => if i=0 then g else h
  refine (heisenbergGroupDistance_le_chain 1 x (by simp [x]) (by simp [x])).trans ?_
  simp [heisenbergChainLength, x]

private theorem heisenbergGroupDistance_horizontal (g h : HeisenbergPoint) :
    |g.1 - h.1| ≤ heisenbergGroupDistance g h ∧
      |g.2.1 - h.2.1| ≤ heisenbergGroupDistance g h := by
  have h (f : HeisenbergPoint → ℝ)
      (hf : ∀ g' h', |f g' - f h'| ≤ heisenbergMalcevNorm (heisenbergMul g' (heisenbergInv h'))) :
      |f g - f h| ≤ heisenbergGroupDistance g h := by
    apply le_csInf (heisenbergChainLengths_nonempty g h)
    rintro _ ⟨n, x, hx₀, hxn, rfl⟩
    have hb := dist_le_range_sum_of_dist_le (f := fun i => f (x i)) n
      (d := fun i => min (heisenbergMalcevNorm (heisenbergMul (x i) (heisenbergInv (x (i+1)))))
        (heisenbergMalcevNorm (heisenbergMul (x (i+1)) (heisenbergInv (x i)))))
      (fun i => by
        rw [Real.dist_eq]
        exact le_min (hf _ _) ((abs_sub_comm _ _).le.trans (hf _ _)))
    simpa only [Real.dist_eq, hx₀, hxn, heisenbergChainLength] using hb
  constructor
  · apply h Prod.fst
    intro g' h'
    simp only [heisenbergMalcevNorm, heisenbergMul, heisenbergInv, sub_eq_add_neg]
    exact le_max_left _ _
  · apply h (fun g => g.2.1)
    intro g' h'
    simp only [heisenbergMalcevNorm, heisenbergMul, heisenbergInv, sub_eq_add_neg]
    exact (le_max_left _ _).trans (le_max_right _ _)

private theorem expandHeisenberg_inv (s : ℕ) (x : HeisenbergPoint) :
    expandHeisenberg s (heisenbergInv x) = heisenbergInv (expandHeisenberg s x) := by
  simp only [expandHeisenberg, heisenbergInv, Prod.mk.injEq]
  exact ⟨by ring, by ring, by ring⟩

private theorem heisenbergMalcevNorm_expand_le {s : ℕ} (hs : 0 < s) (g : HeisenbergPoint) :
    heisenbergMalcevNorm (expandHeisenberg s g) ≤ (s : ℝ)^2 * heisenbergMalcevNorm g := by
  have hs₁ : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hss : (s : ℝ) ≤ (s : ℝ)^2 := by nlinarith
  unfold heisenbergMalcevNorm expandHeisenberg
  simp only [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ s by positivity)]
  apply max_le
  · exact (mul_le_mul_of_nonneg_right hss (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity))
  · apply max_le
    · exact (mul_le_mul_of_nonneg_right hss (abs_nonneg _)).trans
        (mul_le_mul_of_nonneg_left ((le_max_left _ _).trans (le_max_right _ _)) (by positivity))
    · rw [show (s : ℝ)^2*g.2.2 - ((s : ℝ)*g.1)*((s : ℝ)*g.2.1) =
          (s : ℝ)^2 * (g.2.2 - g.1*g.2.1) by ring, abs_mul, abs_of_nonneg (sq_nonneg _)]
      exact mul_le_mul_of_nonneg_left ((le_max_right _ _).trans (le_max_right _ _)) (by positivity)

theorem heisenbergGroupDistance_expand_le {s : ℕ} (hs : 0 < s) (g h : HeisenbergPoint) :
    heisenbergGroupDistance (expandHeisenberg s g) (expandHeisenberg s h) ≤
      (s : ℝ)^2 * heisenbergGroupDistance g h := by
  have hpos : 0 < (s : ℝ)^2 := by positivity
  rw [mul_comm]
  apply (div_le_iff₀ hpos).mp
  apply le_csInf (heisenbergChainLengths_nonempty g h)
  rintro _ ⟨n, x, hx₀, hxn, rfl⟩
  apply (div_le_iff₀ hpos).mpr
  rw [mul_comm]
  refine (heisenbergGroupDistance_le_chain n (fun i => expandHeisenberg s (x i))
    (by simp only [hx₀]) (by simp only [hxn])).trans ?_
  unfold heisenbergChainLength
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  simp only [← expandHeisenberg_inv, ← expandHeisenberg_mul]
  rw [mul_min_of_nonneg _ _ hpos.le]
  exact min_le_min (heisenbergMalcevNorm_expand_le hs _) (heisenbergMalcevNorm_expand_le hs _)

private def heisenbergRepresentativeDistances (g h : HeisenbergPoint) : Set ℝ :=
  {d | ∃ u v w : ℤ,
    d = heisenbergGroupDistance g (heisenbergMul h ((u : ℝ), (v : ℝ), (w : ℝ)))}

private theorem heisenbergRepresentativeDistances_nonempty (g h : HeisenbergPoint) :
    (heisenbergRepresentativeDistances g h).Nonempty :=
  ⟨_, 0, 0, 0, rfl⟩

private theorem heisenbergRepresentativeDistances_bddBelow (g h : HeisenbergPoint) :
    BddBelow (heisenbergRepresentativeDistances g h) := by
  refine ⟨0, ?_⟩
  rintro v ⟨i, j, k, rfl⟩
  exact heisenbergGroupDistance_nonneg _ _

private theorem heisenbergQuotientDistance_le_representative (g h : HeisenbergPoint) (u v w : ℤ) :
    heisenbergQuotientDistance g h ≤ heisenbergGroupDistance g
      (heisenbergMul h ((u : ℝ), (v : ℝ), (w : ℝ))) :=
  csInf_le (heisenbergRepresentativeDistances_bddBelow g h) ⟨u, v, w, rfl⟩

theorem heisenbergQuotientDistance_expand_le {s : ℕ} (hs : 0 < s) (g h : HeisenbergPoint) :
    heisenbergQuotientDistance (expandHeisenberg s g) (expandHeisenberg s h) ≤
      (s : ℝ)^2 * heisenbergQuotientDistance g h := by
  have hpos : 0 < (s : ℝ)^2 := by positivity
  rw [mul_comm]
  apply (div_le_iff₀ hpos).mp
  apply le_csInf (heisenbergRepresentativeDistances_nonempty g h)
  rintro _ ⟨u, v, w, rfl⟩
  apply (div_le_iff₀ hpos).mpr
  rw [mul_comm]
  refine (?_ : heisenbergQuotientDistance (expandHeisenberg s g) (expandHeisenberg s h) ≤
    heisenbergGroupDistance (expandHeisenberg s g)
      (expandHeisenberg s (heisenbergMul h ((u : ℝ), (v : ℝ), (w : ℝ))))).trans
    (heisenbergGroupDistance_expand_le hs _ _)
  rw [expandHeisenberg_mul]
  have hcoord : expandHeisenberg s ((u : ℝ), (v : ℝ), (w : ℝ)) =
      ((((s : ℤ)*u : ℤ) : ℝ), (((s : ℤ)*v : ℤ) : ℝ), ((((s : ℤ)^2*w) : ℤ) : ℝ)) := by
    simp only [expandHeisenberg, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
  rw [hcoord]
  apply heisenbergQuotientDistance_le_representative

private theorem heisenbergQuotientDistance_vertical_le (x y z z' : ℝ) :
    heisenbergQuotientDistance (x,y,z) (x,y,z') ≤ |z-z'| := by
  have h := heisenbergQuotientDistance_le_representative (x,y,z) (x,y,z') 0 0 0
  have hcoord : heisenbergMul (x,y,z') (0,0,0) = (x,y,z') := by simp [heisenbergMul]
  simp only [Int.cast_zero, hcoord] at h
  refine (h.trans (heisenbergGroupDistance_le_relative _ _)).trans_eq ?_
  simp only [heisenbergMalcevNorm, heisenbergMul, heisenbergInv]
  have hz : z + (-z' + x*y) + x*(-y) = z-z' := by ring
  rw [hz]
  simp [max_eq_right (abs_nonneg (z-z'))]

/-- Lipschitz bounds in the chain quotient model imply integrability on
vertical fibres. -/
theorem heisenbergLipschitz_vertical_intervalIntegrable (Φ : HeisenbergPoint → ℂ) (U : ℝ)
    (hΦ : HeisenbergLipschitzNormLE Φ U) (x y a b : ℝ) :
    IntervalIntegrable (fun z => Φ (x,y,z)) volume a b := by
  obtain ⟨_, S, M, hS, hM, _, _, hdist⟩ := hΦ
  suffices h : LipschitzWith (Real.toNNReal M) (fun z => Φ (x,y,z)) from
    h.continuous.intervalIntegrable a b
  apply LipschitzWith.of_dist_le_mul
  intro z z'
  rw [dist_eq_norm, Real.dist_eq, Real.toNNReal_of_nonneg hM]
  exact (hdist _ _).trans (mul_le_mul_of_nonneg_left (heisenbergQuotientDistance_vertical_le _ _ _ _) hM)

/-- Testing vertical mean zero in the half-open fundamental chart is
equivalent to testing every fibre representative. -/
theorem heisenberg_verticalMean_iff_unitChart (Φ : HeisenbergPoint → ℂ) {U : ℝ}
    (hΦ : HeisenbergLipschitzNormLE Φ U) :
    (∀ x y, (∫ z in (0 : ℝ)..1, Φ (x,y,z)) = 0) ↔
      (∀ x ∈ Set.Ico (0 : ℝ) 1, ∀ y ∈ Set.Ico (0 : ℝ) 1,
        (∫ z in (0 : ℝ)..1, Φ (x,y,z)) = 0) := by
  refine ⟨fun h x _ y _ => h x y, ?_⟩
  intro h x y
  let f : ℝ → ℂ := fun z => Φ (Int.fract x, Int.fract y, z)
  let c := x * (↑(-⌊y⌋) : ℝ)
  have heq (z : ℝ) : Φ (x,y,z) = f (z+c) := by
    have he := hΦ.1 (x,y,z) (-⌊x⌋) (-⌊y⌋) 0
    simpa only [f, c, heisenbergMul, Int.cast_zero, add_zero, Int.cast_neg, Int.fract,
      sub_eq_add_neg] using he.symm
  have hper : Function.Periodic f 1 := by
    intro z
    simpa [f, heisenbergMul] using hΦ.1 (Int.fract x,Int.fract y,z) 0 0 1
  simp_rw [heq]
  rw [intervalIntegral.integral_comp_add_right, zero_add, add_comm 1 c,
    hper.intervalIntegral_add_eq c 0, zero_add]
  exact h _ ⟨Int.fract_nonneg x, Int.fract_lt_one x⟩ _ ⟨Int.fract_nonneg y, Int.fract_lt_one y⟩

theorem heisenbergCoverTest_chartMean_eq_zero_of_lipschitz
    (Φ : HeisenbergPoint → ℂ) (U : ℝ) (hΦ : HeisenbergLipschitzNormLE Φ U)
    (k l : ℤ) {m : ℤ} (hm : m ≠ 0)
    (hzero : ∀ x y, (∫ z in (0 : ℝ)..1, Φ (x,y,z)) = 0) :
    heisenbergChartMean (heisenbergCoverTest Φ k l m) = 0 := by
  apply heisenbergCoverTest_chartMean_eq_zero Φ k l hm _ _ hzero
  · intro x y z
    simpa [heisenbergMul] using hΦ.1 (x,y,z) 0 0 1
  · exact heisenbergLipschitz_vertical_intervalIntegrable Φ U hΦ


private theorem heisenbergQuotientDistance_le_groupDistance (g h : HeisenbergPoint) :
    heisenbergQuotientDistance g h ≤ heisenbergGroupDistance g h := by
  simpa [heisenbergMul] using heisenbergQuotientDistance_le_representative g h 0 0 0

/-- A right-lattice invariant test with a Mal'cev-coordinate increment bound
has the same increment bound for the quotient chain distance. -/
theorem heisenbergLipschitzNormLE_of_relative
    (Φ : HeisenbergPoint → ℂ) {S M : ℝ} (hS : 0 ≤ S) (hM : 0 < M)
    (hmean : ∀ g (u v w : ℤ), Φ (heisenbergMul g ((u : ℝ), (v : ℝ), (w : ℝ))) = Φ g)
    (hsup : ∀ g, ‖Φ g‖ ≤ S)
    (hrel : ∀ g h, ‖Φ g-Φ h‖ ≤ M * heisenbergMalcevNorm (heisenbergMul g (heisenbergInv h))) :
    HeisenbergLipschitzNormLE Φ (S+M) := by
  refine ⟨hmean, S, M, hS, hM.le, le_rfl, hsup, ?_⟩
  have hg (g h : HeisenbergPoint) :
      ‖Φ g-Φ h‖ ≤ M * heisenbergGroupDistance g h := by
    rw [mul_comm]
    apply (div_le_iff₀ hM).mp
    apply le_csInf (heisenbergChainLengths_nonempty g h)
    rintro _ ⟨n, x, hx₀, hxn, rfl⟩
    apply (div_le_iff₀ hM).mpr
    rw [mul_comm, heisenbergChainLength, Finset.mul_sum]
    have hchain := dist_le_range_sum_of_dist_le (f := fun i => Φ (x i)) n
      (d := fun i => M * min
        (heisenbergMalcevNorm (heisenbergMul (x i) (heisenbergInv (x (i+1)))))
        (heisenbergMalcevNorm (heisenbergMul (x (i+1)) (heisenbergInv (x i)))))
      (fun i => by
        dsimp only
        rw [dist_eq_norm, mul_min_of_nonneg _ _ hM.le]
        exact le_min (hrel _ _) ((norm_sub_rev _ _).le.trans (hrel _ _)))
    simpa only [dist_eq_norm, hx₀, hxn] using hchain
  intro g h
  rw [mul_comm]
  apply (div_le_iff₀ hM).mp
  apply le_csInf (heisenbergRepresentativeDistances_nonempty g h)
  rintro _ ⟨u, v, w, rfl⟩
  apply (div_le_iff₀ hM).mpr
  rw [mul_comm, ← hmean h u v w]
  exact hg _ _

/-- The finite-cover modification has a uniform Lipschitz bound in the
chain quotient model. The dilation cost is quadratic in its degree. -/
theorem heisenbergCoverTest_lipschitz :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Φ : HeisenbergPoint → ℂ) (U : ℝ),
      HeisenbergLipschitzNormLE Φ U → ∀ (k l : ℤ) {m : ℤ}, m ≠ 0 →
      HeisenbergLipschitzNormLE (heisenbergCoverTest Φ k l m)
        (U*(1+(m.natAbs : ℝ)^2+C*(|(k : ℝ)|+|(l : ℝ)|)) + 1) := by
  obtain ⟨C, hC, hLip⟩ := phase_lipschitz_exists
  refine ⟨C, hC, ?_⟩
  intro Φ U hΦ k l m hm
  obtain ⟨hlat, S, M, hS, hM, hSM, hsup, hdist⟩ := hΦ
  let s := m.natAbs
  have hs : 0 < s := Int.natAbs_pos.mpr hm
  let W := C*(|(k : ℝ)|+|(l : ℝ)|)
  have hW : 0 ≤ W := by dsimp [W]; positivity
  let M' := M*(s : ℝ)^2+S*W+1
  have hM' : 0 < M' := by dsimp [M']; positivity
  have hU : 0 ≤ U := (add_nonneg hS hM).trans hSM
  refine ⟨heisenbergCoverTest_right_lattice Φ hlat k l m, S, M', hS, hM'.le, ?_, ?_, ?_⟩
  · dsimp [M', W, s]
    have hS' : S ≤ U := by linarith
    have hM' : M ≤ U := by linarith
    have h1 := mul_le_mul_of_nonneg_right hS' hW
    have h2 := mul_le_mul_of_nonneg_right hM' (sq_nonneg (m.natAbs : ℝ))
    dsimp [W] at h1
    nlinarith
  · intro g
    simpa [heisenbergCoverTest, norm_mul] using hsup (expandHeisenberg s g)
  · let χ (g : HeisenbergPoint) : ℂ := phase ((m.sign : ℝ) * (k*g.1+l*g.2.1))
    have hsign : |(m.sign : ℝ)| = 1 := by
      have h : ((m.sign).natAbs : ℝ) = 1 := by rw [Int.natAbs_sign_of_ne_zero hm]; norm_num
      simpa only [← Int.cast_abs, ← Int.natCast_natAbs] using h
    have hχ (g h : HeisenbergPoint) :
        ‖χ g - χ h‖ ≤ W * heisenbergGroupDistance g h := by
      unfold χ
      apply (hLip _ _).trans
      unfold W
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ hC
      rw [← mul_sub, abs_mul, hsign, one_mul]
      have hlin :
          (k : ℝ)*g.1+(l : ℝ)*g.2.1-((k : ℝ)*h.1+(l : ℝ)*h.2.1) =
            (k : ℝ)*(g.1-h.1)+(l : ℝ)*(g.2.1-h.2.1) := by ring
      rw [hlin, add_mul]
      apply (abs_add_le _ _).trans
      simp only [abs_mul]
      obtain ⟨hx, hy⟩ := heisenbergGroupDistance_horizontal g h
      exact add_le_add (mul_le_mul_of_nonneg_left hx (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hy (abs_nonneg _))
    have hΨ (g h : HeisenbergPoint) :
        ‖heisenbergCoverTest Φ k l m g - heisenbergCoverTest Φ k l m h‖ ≤
          M' * heisenbergGroupDistance g h := by
      have hΦ' : ‖Φ (expandHeisenberg s g)-Φ (expandHeisenberg s h)‖ ≤
          M*((s : ℝ)^2 * heisenbergGroupDistance g h) := by
        apply (hdist _ _).trans
        apply mul_le_mul_of_nonneg_left _ hM
        exact (heisenbergQuotientDistance_expand_le hs g h).trans
          (mul_le_mul_of_nonneg_left (heisenbergQuotientDistance_le_groupDistance g h) (sq_nonneg _))
      change ‖Φ (expandHeisenberg s g)*χ g-Φ (expandHeisenberg s h)*χ h‖ ≤ _
      rw [show Φ (expandHeisenberg s g)*χ g-Φ (expandHeisenberg s h)*χ h =
        (Φ (expandHeisenberg s g)-Φ (expandHeisenberg s h))*χ g +
          Φ (expandHeisenberg s h)*(χ g-χ h) by ring]
      apply (norm_add_le _ _).trans
      rw [norm_mul, norm_mul, show ‖χ g‖ = 1 from norm_phase _, mul_one]
      calc
        _ ≤ M*((s : ℝ)^2 * heisenbergGroupDistance g h) +
            S*(W*heisenbergGroupDistance g h) :=
          add_le_add hΦ' (mul_le_mul (hsup _) (hχ _ _) (norm_nonneg _) hS)
        _ ≤ _ := by
          dsimp [M']
          nlinarith [heisenbergGroupDistance_nonneg g h]
    intro g h
    rw [mul_comm M']
    apply (div_le_iff₀ hM').mp
    apply le_csInf (heisenbergRepresentativeDistances_nonempty g h)
    rintro _ ⟨u, v, w, rfl⟩
    apply (div_le_iff₀ hM').mpr
    rw [mul_comm, ← heisenbergCoverTest_right_lattice Φ hlat k l m h u v w]
    exact hΨ g _

end CoverMetric

end NilBohr
