import NilBohr.DensityIncrementParameters
import NilBohr.ErgodicRate
import NilBohr.GowersComparison
import NilBohr.Horizontal
import NilBohr.InverseTestBound

/-! The unweighted selector comparison from ordinary polynomial phases.
The centered progression estimate stated here is an original upstream
obligation of the manuscript. -/

open Filter Polynomial
open scoped BigOperators Topology

namespace NilBohr

/-- The centered conclusion (24) of Proposition 4.3 for a chosen sequence
of approximating prime denominators. The origin and polynomial test are
uniform, including phases of any degree at most d on the one-based interval. -/
def CenteredHeisenbergPhaseEstimate (d : ℕ) (V : ℤ → ℝ) (F : Circle → ℂ)
    (r : ℕ → ℕ) : Prop :=
  ∀ D : ℝ, 0 < D → ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop,
    ∀ j : ℕ, (r j : ℝ) ≤ X^(1/100 : ℝ) → X^(1/100 : ℝ) < (r (j+1) : ℝ) →
    ∀ (a : ℤ) (v K : ℕ), 0 < v → (v : ℝ) ≤ X^(1/10000 : ℝ) → ¬ r j ∣ v →
      X^(1/2 : ℝ) ≤ (K : ℝ) →
      phaseNorm (d+1) (positiveInterval K)
        (fun t => F (V (a + (v : ℤ)*t) : Circle) - circleMean F) ≤
        C * (Real.log X)^(-D)

/-- A nonempty interval/residue class is exactly a one-based integer
progression. The real length loss from the floor is strictly less than one. -/
theorem localProgression_as_affine {l r u : ℤ} {m : ℕ} (hm : 0 < m)
    (hP : (localProgression l r u m).Nonempty) :
    ∃ a : ℤ, (Finset.Icc l r).card / (m : ℝ) - 1 <
        ((localProgression l r u m).card : ℝ) ∧
      localProgression l r u m =
        (positiveInterval (localProgression l r u m).card).image (fun t => a + (m : ℤ)*t) := by
  let N := (Finset.Icc l r).card
  obtain ⟨y, hy⟩ := hP
  obtain ⟨hyI, hyu⟩ := Finset.mem_filter.mp hy
  have hlr : l ≤ r := (Finset.mem_Icc.mp hyI).1.trans (Finset.mem_Icc.mp hyI).2
  have hNz : (N : ℤ) = r-l+1 := by
    dsimp [N]
    rw [Int.card_Icc, Int.toNat_of_nonneg (by omega)]
    omega
  have hshift (z : ℤ) : z ∈ Finset.Icc l r ↔ z-l+1 ∈ positiveInterval N := by
    simp only [positiveInterval, Finset.mem_Icc, hNz]
    omega
  have hres (z : ℤ) : Int.ModEq (m : ℤ) z u ↔ (z-l+1-1)%(m : ℤ) = (u-l)%(m : ℤ) := by
    rw [add_sub_cancel_right]
    constructor
    · intro h
      exact h.sub_right l
    · intro h
      have h' : Int.ModEq (m : ℤ) (z-l) (u-l) := h
      simpa only [sub_add_cancel] using h'.add_right l
  have hr : (u-l)%(m : ℤ) ∈ (positiveInterval N).image (fun z => (z-1)%(m : ℤ)) :=
    Finset.mem_image.mpr ⟨y-l+1, (hshift y).mp hyI, (hres y).mp hyu⟩
  obtain ⟨a, K, _, hKlen, hrep⟩ := residue_slice_as_progression hm _ hr
  let f : ℤ → ℤ := fun t => (a+l-1) + (m : ℤ)*t
  have hP' : localProgression l r u m = (positiveInterval K).image f := by
    ext z
    simp only [localProgression, Finset.mem_filter, Finset.mem_image]
    rw [hshift, hres, hrep]
    exact exists_congr (fun t => and_congr_right fun _ => by dsimp [f]; constructor <;> intro h <;> linarith)
  have hmZ : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  have hf : Function.Injective f := fun t s h => mul_left_cancel₀ hmZ (add_left_cancel h)
  have hcard : (localProgression l r u m).card = K := by
    rw [hP', Finset.card_image_of_injective _ hf, card_positiveInterval]
  refine ⟨a+l-1, ?_, ?_⟩
  · rw [hcard]
    exact hKlen
  · simpa only [hcard] using hP'

/-- The polynomial-phase supremum decreases under affine reindexing to the
one-based interval when the degree bound is fixed. The affine map here is
injective because its step is positive. -/
theorem phaseNorm_le_affine_pullback {s K m : ℕ} (hs : 0 < s) (hm : 0 < m)
    (a : ℤ) (w : ℤ → ℂ) :
    phaseNorm s ((positiveInterval K).image (fun y => a + (m : ℤ)*y)) w ≤
      phaseNorm s (positiveInterval K) (fun y => w (a + (m : ℤ)*y)) := by
  classical
  let f : ℤ → ℤ := fun y => a + (m : ℤ)*y
  have hmZ : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  have hfi : Function.Injective f := fun t u h => mul_left_cancel₀ hmZ (add_left_cancel h)
  let I := (positiveInterval K).image f
  let L : Polynomial ℝ := C (a : ℝ) + C (m : ℝ) * X
  have hdegL : L.natDegree ≤ 1 := by
    refine Polynomial.natDegree_add_le_of_degree_le (by simp) ?_
    simpa using (Polynomial.natDegree_C_mul_le (m : ℝ) (X : Polynomial ℝ)).trans
      (by simp : (X : Polynomial ℝ).natDegree ≤ 1)
  unfold phaseNorm
  refine csSup_le ⟨‖phaseAverage I w 0‖, 0, by simpa using hs, rfl⟩ ?_
  rintro c ⟨φ, hφ, rfl⟩
  have hφL : (φ.comp L).natDegree < s :=
    (Polynomial.natDegree_comp_le.trans (by simpa using Nat.mul_le_mul_left φ.natDegree hdegL)).trans_lt hφ
  have hphase : phaseAverage I w φ =
      phaseAverage (positiveInterval K) (fun y => w (f y)) (φ.comp L) := by
    simp only [I, phaseAverage, Finset.card_image_of_injective _ hfi,
      Finset.sum_image (fun _ _ _ _ h => hfi h)]
    congr 1
    apply Finset.sum_congr rfl
    intro t _
    simp [Polynomial.eval_comp, L, f]
  rw [hphase]
  exact norm_phaseAverage_le_phaseNorm (fun y => w (f y)) (φ.comp L) hφL

private theorem eventually_log_atTop :
    Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

private theorem eventually_scaled_rpow_le {a b C : ℝ} (hab : a < b) :
    ∀ᶠ t : ℝ in atTop, C*t^a ≤ t^b := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (tendsto_rpow_atTop (sub_pos.mpr hab)).eventually_ge_atTop C] with t ht hC
  have ht' : 0 < t := zero_lt_one.trans_le ht
  calc
    _ ≤ t^(b-a)*t^a := mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg ht'.le a)
    _ = t^((b-a)+a) := (Real.rpow_add ht' _ _).symm
    _ = _ := by ring_nf

set_option maxHeartbeats 1400000 in
/-- The tests of Theorem 4.2 satisfy the scale conditions of Proposition
4.3, uniformly on the smooth-modulus window at the manuscript's value of rho. -/
theorem eventually_localSelectorTest_window {c₀ cRel A₁ A₂ A : ℝ}
    (hc₀ : 0 < c₀) (hc₀' : c₀ < 1/11) (hcRel' : cRel ≤ 1/10)
    (hA₁ : 0 < A₁) (hA₂ : 0 < A₂) (hA : 0 < A) {d w₀ : ℕ} (hd : 0 < d)
    (hw₀ : 16 ≤ w₀) (B : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ q w : ℕ, RelativeModulus c₀ cRel w₀ N q w →
      let t := Real.log (N : ℝ)
      let M := parameterLength N q d
      let xScale := ((q*M+1 : ℕ) : ℝ)
      let ρ := (w : ℝ)^(-A-1)
      (q : ℝ) ≤ Real.exp (t^(1/10 : ℝ)) ∧ 0 < M ∧ (w : ℝ) ≤ t ∧
      t/(2*(d : ℝ)) ≤ Real.log xScale ∧
      ∀ l r u : ℤ, ∀ b : ℕ, b ≤ B →
        (M : ℝ)*(q : ℝ)^(-A₁)*ρ^A₂ ≤ ((Finset.Icc l r).card : ℝ) →
        (localProgression l r u (q^b)).Nonempty →
        (((q^(b+1) : ℕ)) : ℝ) ≤ xScale^(1/10000 : ℝ) ∧
          xScale^(1/2 : ℝ) ≤ ((localProgression l r u (q^b)).card : ℝ) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  let U := (A+1)*A₂
  have hU : 0 < U := by dsimp [U]; positivity
  have hscale := eventually_parameterLength_relativeScaleWindow hc₀ hc₀' hcRel' hd w₀
  have hModGrowth := eventually_scaled_rpow_le (a := c₀*(1/5)) (b := 1/10)
    (C := 4) (by linarith)
  have hstep := eventually_linearSqrt_lt (show (0 : ℝ) < (20000*(d:ℝ))⁻¹ by positivity)
    ((B : ℝ)+1) 0
  have hlength := eventually_linearSqrt_lt (show (0 : ℝ) < (4*(d:ℝ))⁻¹ by positivity)
    ((d : ℝ) + A₁ + (B : ℝ) + 2*U) (Real.log 2)
  have hAmbient := eventually_linearSqrt_lt (show (0 : ℝ) < (4*(d:ℝ))⁻¹ by positivity)
    1 (Real.log 2)
  filter_upwards [hscale, eventually_ge_atTop (3:ℕ), eventually_log_atTop.eventually_ge_atTop 1,
    eventually_log_atTop.eventually hModGrowth, eventually_log_atTop.eventually hstep,
    eventually_log_atTop.eventually hlength, eventually_log_atTop.eventually hAmbient]
    with N hscale hN hlog hModGrowth hstep hlength hAmbient
  intro q w hmod
  let t := Real.log (N : ℝ)
  let M := parameterLength N q d
  let xScale := ((q*M+1 : ℕ) : ℝ)
  let ρ := (w : ℝ)^(-A-1)
  have ht₀ : 0 < t := zero_lt_one.trans_le hlog
  have hw' : w₀ ≤ w := hmod.1
  have hw : (1 : ℝ) ≤ w := by exact_mod_cast (show 1 ≤ w by omega)
  have hwR : (0 : ℝ) < w := zero_lt_one.trans_le hw
  have hq := hmod.2.1
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hq₁ : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL := (cramerCutoff_log_bounds hc₀.le hlog).2.2
  let L := Real.log (cramerCutoff c₀ N)
  have hL₁ : 1 ≤ L := (Real.one_le_rpow hlog hc₀.le).trans
    (cramerCutoff_log_bounds hc₀.le hlog).2.1
  have hw2 : (w : ℝ)^2 ≤ t^(1/10 : ℝ) := calc
    _ ≤ (L^cRel)^2 := pow_le_pow_left₀ hwR.le hmod.2.2.1 2
    _ = L^(2*cRel) := by rw [mul_comm, Real.rpow_mul (zero_le_one.trans hL₁), Real.rpow_two]
    _ ≤ L^(1/5 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL₁ (by linarith)
    _ ≤ (2*t^c₀)^(1/5 : ℝ) := Real.rpow_le_rpow (zero_le_one.trans hL₁) hL (by norm_num)
    _ ≤ 4*t^(c₀*(1/5)) := by
      rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg ht₀.le _), ← Real.rpow_mul ht₀.le]
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg ht₀.le _)
      have htwo : (2 : ℝ)^(1/5 : ℝ) ≤ 2 := by
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
            (by norm_num : (1/5 : ℝ) ≤ 1)
      linarith
    _ ≤ _ := hModGrowth
  have hlogq : Real.log q ≤ t^(1/10 : ℝ) := hmod.2.2.2.2.2.trans hw2
  have hw_le : (w : ℝ) ≤ t := by
    apply (sq_le_sq₀ hwR.le ht₀.le).mp (hw2.trans ?_)
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hlog (by norm_num)
  have hlogqSqrt : Real.log q ≤ Real.sqrt t := by
    rw [Real.sqrt_eq_rpow]
    exact hlogq.trans (Real.rpow_le_rpow_of_exponent_le hlog (by norm_num))
  have hlogw : Real.log w ≤ 2*Real.sqrt t :=
    (Real.log_le_log hwR hw_le).trans (log_le_two_sqrt_density ht₀)
  have hqBound : (q : ℝ) ≤ Real.exp (t^(1/10 : ℝ)) := by
    rw [← Real.exp_log hqR]
    exact Real.exp_le_exp.mpr hlogq
  have hMl := (hscale q w hmod).1
  have hMu := (hscale q w hmod).2
  have hMNpos : 0 < (N : ℝ)^(1/(d:ℝ)) := Real.rpow_pos_of_pos hNR _
  have hMR : (0 : ℝ) < M := (mul_pos hMNpos (Real.exp_pos _)).trans_le hMl
  have hM : 0 < M := by exact_mod_cast hMR
  have hM₁ : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have hlogM : t/(d:ℝ) - (d : ℝ)*Real.sqrt t ≤ Real.log M := by
    have h := Real.log_le_log (mul_pos hMNpos (Real.exp_pos _)) hMl
    rw [Real.log_mul hMNpos.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_rpow hNR] at h
    simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm ((d : ℝ)⁻¹), ← sub_eq_add_neg,
      neg_mul, t] using h
  have hMlogUpper : Real.log M ≤ t/(d:ℝ) := by
    have h := Real.log_le_log hMR hMu
    rw [Real.log_rpow hNR] at h
    simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm ((d : ℝ)⁻¹), t] using h
  have hX₁ : (1 : ℝ) ≤ xScale := by dsimp [xScale]; exact_mod_cast (Nat.succ_le_succ (Nat.zero_le _))
  have hX : 0 < xScale := zero_lt_one.trans_le hX₁
  have hMX : (M : ℝ) ≤ xScale := by
    dsimp [xScale]
    have h : 1 * M ≤ q * M := Nat.mul_le_mul_right M (show 1 ≤ q from hq)
    rw [Nat.one_mul] at h
    exact_mod_cast h.trans (Nat.le_succ (q*M))
  have hXlog : t/(2*(d:ℝ)) ≤ Real.log xScale := by
    have hXlogM := Real.log_le_log hMR hMX
    have hD : (d : ℝ)*Real.sqrt t ≤ t/(4*(d:ℝ)) := by
      have hrest : 0 ≤ (A₁ + (B : ℝ) + 2*U) * Real.sqrt t + Real.log 2 :=
        add_nonneg (mul_nonneg (by positivity) (Real.sqrt_nonneg _)) (Real.log_nonneg (by norm_num))
      change ((d : ℝ) + A₁ + (B : ℝ) + 2*U)*Real.sqrt t + Real.log 2 < (4*(d:ℝ))⁻¹*t at hlength
      have heq : (4*(d:ℝ))⁻¹*t = t/(4*(d:ℝ)) := by ring
      rw [heq] at hlength
      linarith
    have heq : t/(2*(d:ℝ)) = 2 * (t/(4*(d:ℝ))) := by ring
    have heq' : t/(d:ℝ) = 4 * (t/(4*(d:ℝ))) := by ring
    have hT : 0 ≤ t/(4*(d:ℝ)) := by positivity
    rw [heq'] at hlogM
    rw [heq]
    linarith
  have hXUpper : Real.log xScale ≤ 5*(t/(4*(d:ℝ))) := by
    have hY : xScale ≤ 2*(q:ℝ)*(M:ℝ) := by
      dsimp [xScale]
      push_cast
      nlinarith [mul_le_mul hq₁ hM₁ (by norm_num : (0:ℝ) ≤ 1) hqR.le]
    have h := Real.log_le_log hX hY
    rw [Real.log_mul (mul_pos (by norm_num) hqR).ne' hMR.ne',
      Real.log_mul (by norm_num) hqR.ne'] at h
    change 1 * Real.sqrt t + Real.log 2 < (4*(d:ℝ))⁻¹*t at hAmbient
    have heq : (4*(d:ℝ))⁻¹*t = t/(4*(d:ℝ)) := by ring
    rw [heq] at hAmbient
    have heq' : t/(d:ℝ) = 4 * (t/(4*(d:ℝ))) := by ring
    rw [heq'] at hMlogUpper
    linarith
  refine ⟨hqBound, hM, hw_le, hXlog, ?_⟩
  intro l r u b hb hI hP
  have hbR : (b : ℝ) ≤ B := by exact_mod_cast hb
  have hqb : 0 < q^b := pow_pos hq _
  have hqbR : (0 : ℝ) < (q : ℝ)^b := pow_pos hqR _
  constructor
  · change (((q^(b+1) : ℕ)) : ℝ) ≤ xScale^(1/10000 : ℝ)
    push_cast
    apply (Real.log_le_log_iff (pow_pos hqR _) (Real.rpow_pos_of_pos hX _)).mp
    rw [Real.log_pow, Real.log_rpow hX]
    change ((B:ℝ)+1)*Real.sqrt t + 0 < (20000*(d:ℝ))⁻¹ * t at hstep
    have heq : (20000*(d:ℝ))⁻¹ * t = (1/10000:ℝ) * (t/(2*(d:ℝ))) := by ring
    rw [heq] at hstep
    have hqNonneg : 0 ≤ Real.log q := Real.log_nonneg hq₁
    have hstep' := mul_le_mul (show ((b+1 : ℕ) : ℝ) ≤ ((B+1 : ℕ) : ℝ) by exact_mod_cast (Nat.succ_le_succ hb))
      hlogqSqrt hqNonneg (by positivity : 0 ≤ ((B+1 : ℕ) : ℝ))
    push_cast at hstep' ⊢
    linarith
  · obtain ⟨_, hcard, _⟩ := localProgression_as_affine hqb hP
    have hD : 2 * xScale^(1/2 : ℝ) ≤ (M : ℝ)*(q : ℝ)^(-A₁)*ρ^A₂ / (q : ℝ)^b := by
      apply (Real.log_le_log_iff (mul_pos (by norm_num) (Real.rpow_pos_of_pos hX _))
        (by dsimp [ρ]; positivity)).mp
      rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hX _).ne', Real.log_rpow hX,
        Real.log_div (by dsimp [ρ]; positivity) hqbR.ne',
        Real.log_mul (by positivity) (Real.rpow_pos_of_pos (by dsimp [ρ]; positivity) _).ne',
        Real.log_mul hMR.ne' (Real.rpow_pos_of_pos hqR _).ne',
        Real.log_rpow hqR, Real.log_rpow (show 0 < ρ by dsimp [ρ]; positivity),
        show Real.log ρ = (-A-1)*Real.log w by dsimp [ρ]; rw [Real.log_rpow hwR],
        Real.log_pow]
      have hqNonneg : 0 ≤ Real.log q := Real.log_nonneg hq₁
      have hwNonneg : 0 ≤ Real.log w := Real.log_nonneg hw
      have hb₀ : 0 ≤ (b : ℝ) := Nat.cast_nonneg _
      have h1 := mul_le_mul_of_nonneg_left hlogqSqrt hA₁.le
      have h2 := mul_le_mul hbR hlogqSqrt hqNonneg (Nat.cast_nonneg B)
      have h3 := mul_le_mul_of_nonneg_left hlogw hU.le
      have heq : (4*(d:ℝ))⁻¹*t = t/(4*(d:ℝ)) := by ring
      change ((d : ℝ)+A₁+(B : ℝ)+2*U)*Real.sqrt t + Real.log 2 < (4*(d:ℝ))⁻¹*t at hlength
      rw [heq] at hlength
      have hM' : 4*(t/(4*(d:ℝ))) - (d : ℝ)*Real.sqrt t ≤ Real.log M := by
        convert hlogM using 1
        ring
      have heqU : A₂*((-A-1)*Real.log w) = -U*Real.log w := by dsimp [U]; ring
      rw [heqU]
      have hT : 0 ≤ t/(4*(d:ℝ)) := by positivity
      linarith only [h1, h2, h3, hlength, hM', hXUpper, hT]
    have hcard' := (div_le_div_of_nonneg_right hI hqbR.le)
    rw [Nat.cast_pow] at hcard
    have hone : 1 ≤ xScale^(1/2 : ℝ) := Real.one_le_rpow hX₁ (by norm_num)
    linarith

/-- The statement of Lemma 4.4 on the smooth relative window. -/
def UnweightedSelectorComparison (c₀ cRel C : ℝ) (w₀ d ℓ : ℕ)
    (V : ℤ → ℝ) (F : Circle → ℂ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ,
    ∀ N q w : ℕ, N₀ ≤ N → RelativeModulus c₀ cRel w₀ N q w →
      let M := parameterLength N q d
      ∀ P : Fin (ℓ + 1) → Polynomial ℤ, FixedPolynomialFamily P →
      (P (Fin.last ℓ)).natDegree = d → (∀ i, i ≠ 0 → HasCoefficients C q (P i)) →
      ∀ f : Fin (ℓ + 1) → ℤ → ℂ,
        (∀ i, OneBoundedOn (positiveInterval N) (f i)) →
        (∀ i, SupportedOn (positiveInterval N) (f i)) →
        ‖countingForm N M (positiveInterval N) P
          (fun y => selectorWeight V F q y - circleMean F) f‖ ≤ K*(w : ℝ)^(-A)

def CenteredSelectorComparisonAt (Extra : ℕ → ℕ → Prop) (c₀ cRel C : ℝ) (w₀ d ℓ : ℕ)
    (V : ℤ → ℝ) (F : Circle → ℂ) (A : ℝ) : Prop := ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ,
    ∀ N q w : ℕ, N₀ ≤ N → RelativeModulus c₀ cRel w₀ N q w → Extra q w →
      let M := parameterLength N q d
      ∀ P : Fin (ℓ + 1) → Polynomial ℤ, FixedPolynomialFamily P →
      (P (Fin.last ℓ)).natDegree = d → (∀ i, i ≠ 0 → HasCoefficients C q (P i)) →
      ∀ f : Fin (ℓ + 1) → ℤ → ℂ,
        (∀ i, OneBoundedOn (positiveInterval N) (f i)) →
        (∀ i, SupportedOn (positiveInterval N) (f i)) →
        ‖countingForm N M (positiveInterval N) P
          (fun y => selectorWeight V F q y - circleMean F) f‖ ≤ K*(w : ℝ)^(-A)

private theorem positiveInterval_subset_spatialInterval {C : ℝ} (hC : 1 ≤ C) (N : ℕ) :
    positiveInterval N ⊆ spatialInterval C N := by
  intro x hx
  obtain ⟨hx₁, hx₂⟩ := Finset.mem_Icc.mp hx
  have hx₁' : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx₁
  have hx₂' : (x : ℝ) ≤ N := by exact_mod_cast hx₂
  have hN₀ : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hC₀ : 0 ≤ C := zero_le_one.trans hC
  have hlo : -(C*(N : ℝ)) ≤ 0 := neg_nonpos.mpr (mul_nonneg hC₀ hN₀)
  have hhi : (N : ℝ) ≤ C*(N : ℝ) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hC hN₀
  exact Finset.mem_Icc.mpr ⟨Int.ceil_le.mpr (by linarith), Int.le_floor.mpr (hx₂'.trans hhi)⟩

set_option maxHeartbeats 1800000 in
/-- Convert local polynomial phase cancellation to a centered count.
The test threshold may be raised above the one used in the scale estimates. -/
theorem centeredSelectorComparison_using_local_phase
    (Hguard : ℕ → ℝ → Prop) (Extra : ℕ → ℕ → Prop)
    {c₀ cRel C : ℝ}
    (hc₀ : 0 < c₀) (hc₀' : c₀ < 1/11) (_hcRel : 0 < cRel) (hcRel' : cRel ≤ 1/10)
    (hC : 1 ≤ C) {w₀ d ℓ : ℕ} (hw₀ : 16 ≤ w₀) (hd : 0 < d) (_hℓ : 0 < ℓ)
    {η A₁ A₂ K : ℝ} {B : ℕ} (hη : 0 < η) (hA₁ : 0 < A₁)
    (hA₂ : 0 < A₂) (hK : 0 < K)
    (hVN : LocalGeneralizedVonNeumannOn Hguard C d ℓ η A₁ A₂ K B)
    (A : ℝ) (hA : 0 < A) (test : ℕ → ℝ)
    (hTest : ∀ w : ℕ, w₀ ≤ w → 0 < test w ∧ test w ≤ 1/2 ∧
      (w : ℝ)^(-A-1) ≤ test w ∧ test w ≤ (w : ℝ)^(-A))
    (hGuard : ∀ q w : ℕ, w₀ ≤ w → Extra q w → Hguard q (test w))
    {α β : ℝ} (F : Circle → ℂ) (hF : Continuous F)
    (hphase : ∃ r : ℕ → ℕ, AdmissibleBetaDenominators β r ∧
      CenteredHeisenbergPhaseEstimate d (heisenbergPhase α β) F r) :
    CenteredSelectorComparisonAt Extra c₀ cRel C w₀ d ℓ (heisenbergPhase α β) F A := by
  classical
  let V := heisenbergPhase α β
  obtain ⟨r, ⟨hr, a, _, hprimes, c, C', D', hc, hC', _, happ⟩, hphase⟩ := hphase
  let D := A / η + 1
  have hD : 0 < D := by dsimp [D]; positivity
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hDη : A ≤ D * η := by
    dsimp [D]
    rw [add_mul, div_mul_cancel₀ _ hη.ne', one_mul]
    linarith
  obtain ⟨L, hL, hphase⟩ := hphase D hD
  have hdenom := horizontal_scale_bounds c C' 1 (2*(d:ℝ)) hc hC' one_pos (by positivity)
  have hstart := (tendsto_rpow_atTop (show (0:ℝ) < 1/100 by norm_num)).eventually_ge_atTop (r 0 : ℝ)
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp (hphase.and (hdenom.and hstart))
  obtain ⟨W₀, hW₀⟩ := (isCompact_univ (X := Circle)).exists_bound_of_continuousOn
    ((hF.sub continuous_const : Continuous (fun x => F x - circleMean F)).continuousOn)
  let W := max 1 W₀
  have hW₁ : 1 ≤ W := le_max_left _ _
  have hW : 0 < W := zero_lt_one.trans_le hW₁
  let T := L * (2*(d:ℝ))^D
  have hT : 0 < T := by dsimp [T]; positivity
  let K' := W * K * (2 + T^η)
  have hK' : 0 < K' := by dsimp [K']; positivity
  have hwindow := eventually_localSelectorTest_window hc₀ hc₀' hcRel' hA₁ hA₂ hA hd hw₀ B
  have hNη := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero A η hη).eventually (gt_mem_nhds one_pos)
  let Xmin := max 1 X₀
  have hXmin : 0 < Xmin := zero_lt_one.trans_le (le_max_left _ _)
  have hXgrow := eventually_log_atTop.eventually_ge_atTop (2*(d:ℝ)*Real.log Xmin)
  have hE : ∀ᶠ N : ℕ in atTop,
        ∀ q w : ℕ, RelativeModulus c₀ cRel w₀ N q w → Extra q w →
          let M := parameterLength N q d
          ∀ P : Fin (ℓ + 1) → Polynomial ℤ, FixedPolynomialFamily P →
          (P (Fin.last ℓ)).natDegree = d → (∀ i, i ≠ 0 → HasCoefficients C q (P i)) →
          ∀ f : Fin (ℓ + 1) → ℤ → ℂ,
          (∀ i, OneBoundedOn (positiveInterval N) (f i)) →
          (∀ i, SupportedOn (positiveInterval N) (f i)) →
          ‖countingForm N M (positiveInterval N) P
            (fun y => selectorWeight V F q y - circleMean F) f‖ ≤ K'*(w : ℝ)^(-A) := by
    filter_upwards [hwindow, eventually_ge_atTop (3 : ℕ), eventually_log_atTop.eventually_ge_atTop 1,
      eventually_log_atTop.eventually hNη, hXgrow] with N hwindow hN hlog hNη hXgrow
    intro q w hMod hExtra M P hP hPtop hcoeff f hfb hfs
    let t := Real.log (N : ℝ)
    let xScale := ((q*M+1 : ℕ) : ℝ)
    let ρ := test w
    let weight := fun y => selectorWeight V F q y - circleMean F
    let v := fun y => ((W : ℂ)⁻¹) * weight y
    obtain ⟨hqScale, hM, hw_t, hlogX, htests⟩ := hwindow q w hMod
    have hq := hMod.2.1
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have hq₁ : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hwbig : (16 : ℝ) ≤ w := by exact_mod_cast hw₀.trans hMod.1
    have hw₁ : (1 : ℝ) ≤ w := by linarith
    have hw : (0 : ℝ) < w := by linarith
    have hX : 0 < xScale := by dsimp [xScale]; positivity
    have hX' : X₀ ≤ xScale := by
      have hmin : Xmin ≤ xScale := by
        apply (Real.log_le_log_iff hXmin hX).mp
        exact ((le_div_iff₀ (by positivity : 0 < 2*(d:ℝ))).mpr (by
          simpa only [mul_comm (Real.log Xmin)] using hXgrow)).trans hlogX
      exact (le_max_right _ _).trans hmin
    obtain ⟨hphaseX, hdenomX, hstartX⟩ := hX₀ xScale hX'
    obtain ⟨j, hjlo, hjhi⟩ := exists_bracketing_denominators r hr _ hstartX
    obtain ⟨hlo, hhi, _, _⟩ := happ j
    have hpr := (hprimes j).1
    have hlogX' : (w : ℝ) / (2*(d:ℝ)) ≤ Real.log xScale :=
      (div_le_div_of_nonneg_right hw_t (by positivity)).trans hlogX
    have hlogXpos : 0 < Real.log xScale := (div_pos hw (by positivity)).trans_le hlogX'
    have hrw : w < r j := by
      have hg := (hdenomX (r j) (r (j+1)) hpr.pos hlo hhi hjhi).1
      rw [Real.rpow_one] at hg
      have hh := (div_le_iff₀ (by positivity : 0 < 2*(d:ℝ))).mp hlogX'
      have hg' : Real.log xScale * (2*(d:ℝ)) < (r j : ℝ) := by
        simpa only [mul_comm (Real.log xScale)] using hg
      have hcast : (w : ℝ) < (r j : ℝ) := hh.trans_lt hg'
      exact_mod_cast hcast
    obtain ⟨hρ, hρ₂, hρLow, hρ_A⟩ := hTest w hMod.1
    have hXpower : L * (Real.log xScale)^(-D) ≤ T * (w : ℝ)^(-D) := by
      calc
        _ ≤ L * ((w : ℝ)/(2*(d:ℝ)))^(-D) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_nonpos (div_pos hw (by positivity)) hlogX' (by linarith)) hL.le
        _ = _ := by
          dsimp [T]
          rw [Real.div_rpow hw.le (by positivity), Real.rpow_neg (by positivity : 0 ≤ 2*(d:ℝ)),
            div_inv_eq_mul]
          ring
    have hphase_test (l r' u : ℤ) (b : ℕ) (hb : b ≤ B)
        (hsize : (M : ℝ)*(q : ℝ)^(-A₁)*ρ^A₂ ≤ ((Finset.Icc l r').card : ℝ))
        (hnonempty : (localProgression l r' u (q^b)).Nonempty) :
        phaseNorm (d+1) (localProgression l r' u (q^b)) v ≤ T * (w : ℝ)^(-D) := by
      let P₀ := localProgression l r' u (q^b)
      let m := q^b
      let k := P₀.card
      have hm : 0 < m := pow_pos hq _
      obtain ⟨A₀, _, hrep⟩ := localProgression_as_affine hm hnonempty
      have hsizeLow : (M : ℝ)*(q : ℝ)^(-A₁)*((w : ℝ)^(-A-1))^A₂ ≤
          ((Finset.Icc l r').card : ℝ) := by
        refine le_trans ?_ hsize
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (by positivity) hρLow hA₂.le) (by positivity)
      obtain ⟨hstep, hlen⟩ := htests l r' u b hb hsizeLow hnonempty
      have hstep_pos : 0 < q^(b+1) := pow_pos hq _
      have hnot : ¬ r j ∣ q^(b+1) := fun h =>
        (not_le_of_gt hrw) (hMod.2.2.2.2.1 _ hpr (hpr.dvd_of_dvd_pow h))
      have hAvg := hphaseX j hjlo hjhi ((q : ℤ)*A₀) (q^(b+1)) k hstep_pos hstep hnot hlen
      have hlift : phaseNorm (d+1) P₀ weight ≤ L * (Real.log xScale)^(-D) := by
        refine le_trans ?_ hAvg
        have hpull := phaseNorm_le_affine_pullback (s := d+1) (K := k) (by omega) hm A₀ weight
        rw [← hrep] at hpull
        have hea (x : ℤ) : weight (A₀ + (m : ℤ)*x) =
            F (V ((q : ℤ)*A₀ + ((q^(b+1) : ℕ) : ℤ)*x) : Circle) - circleMean F := by
          have he : (q : ℤ)*(A₀ + (m : ℤ)*x) =
              (q : ℤ)*A₀ + ((q^(b+1) : ℕ) : ℤ)*x := by dsimp [m]; push_cast; rw [pow_succ']; ring
          simp only [weight, selectorWeight, he]
        simpa only [hea] using hpull
      have hv' := phaseNorm_const_mul_le (s := d+1) (by omega) P₀ weight ((W:ℂ)⁻¹)
      have hWcomplex : ‖((W : ℂ)⁻¹)‖ ≤ 1 := by
        rw [norm_inv, Complex.norm_of_nonneg hW.le]
        exact inv_le_one_of_one_le₀ hW₁
      have hp := mul_le_of_le_one_left (phaseNorm_nonneg_of_pos (s := d+1) (by omega) P₀ weight)
        hWcomplex
      exact hv'.trans (hp.trans (hlift.trans hXpower))
    have hglobal : phaseNorm (d+1) (positiveInterval M) v ≤ T * (w : ℝ)^(-D) := by
      have hI : Finset.Icc 1 (M : ℤ) = positiveInterval M := rfl
      have hP₀ : localProgression 1 (M : ℤ) 0 (q^(0 : ℕ)) = positiveInterval M := by
        simp [localProgression, positiveInterval, Int.modEq_one]
      have hsize : (M : ℝ)*(q : ℝ)^(-A₁)*ρ^A₂ ≤ ((Finset.Icc 1 (M:ℤ)).card : ℝ) := by
        simp only [hI, card_positiveInterval]
        have hQle : (q : ℝ)^(-A₁) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hq₁ (by linarith)
        have hρle : ρ^A₂ ≤ 1 := Real.rpow_le_one hρ.le (by linarith) hA₂.le
        exact (mul_le_of_le_one_right (by positivity) hρle).trans
          (mul_le_of_le_one_right (by positivity) hQle)
      have hnonempty : (localProgression 1 (M:ℤ) 0 (q^0)).Nonempty := by
        rw [hP₀]
        exact Finset.card_pos.mp (by simpa)
      simpa only [hP₀] using hphase_test 1 (M:ℤ) 0 0 (Nat.zero_le _) hsize hnonempty
    have hlocal : localPhaseNorm d M q B A₁ A₂ ρ v ≤ T * (w : ℝ)^(-D) := by
      unfold localPhaseNorm
      apply Real.sSup_le _ (by positivity)
      rintro x ⟨l, r', u, b, hb, _, hsize, hn, rfl⟩
      exact hphase_test l r' u b hb hsize hn
    have hSUP : (if ℓ=1 then phaseNorm (d+1) (positiveInterval M) v
                  else localPhaseNorm d M q B A₁ A₂ ρ v) ≤ T * (w : ℝ)^(-D) := by
      split_ifs
      · exact hglobal
      · exact hlocal
    have hSUP₀ : 0 ≤ (if ℓ=1 then phaseNorm (d+1) (positiveInterval M) v
                  else localPhaseNorm d M q B A₁ A₂ ρ v) := by
      split_ifs
      · exact phaseNorm_nonneg_of_pos (s := d+1) (by omega) _ _
      · unfold localPhaseNorm
        rename_i h
        let S : Set ℝ := {z | ∃ (l r' u : ℤ) (b : ℕ), b ≤ B ∧
          Finset.Icc l r' ⊆ positiveInterval M ∧
          (M : ℝ)*(q : ℝ)^(-A₁)*ρ^A₂ ≤ ((Finset.Icc l r').card : ℝ) ∧
          (localProgression l r' u (q^b)).Nonempty ∧
          z = phaseNorm (d+1) (localProgression l r' u (q^b)) v}
        change 0 ≤ sSup S
        by_cases hnonempty : S.Nonempty
        · obtain ⟨x, hx⟩ := hnonempty
          have hx₀ : 0 ≤ x := by
            obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := hx
            exact phaseNorm_nonneg_of_pos (s := d+1) (by omega) _ _
          exact hx₀.trans (le_csSup ⟨_, fun x hx => by
            obtain ⟨l, r', u, b, hb, _, hsize, hp, rfl⟩ := hx
            exact hphase_test l r' u b hb hsize hp⟩ hx)
        · rw [Set.not_nonempty_iff_eq_empty.mp hnonempty, Real.sSup_empty]
    have hSUPpower : (if ℓ=1 then phaseNorm (d+1) (positiveInterval M) v
                      else localPhaseNorm d M q B A₁ A₂ ρ v)^η ≤ T^η * (w : ℝ)^(-A) := by
      apply (Real.rpow_le_rpow hSUP₀ hSUP hη.le).trans
      rw [Real.mul_rpow hT.le (by positivity), ← Real.rpow_mul hw.le]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hw₁ (by nlinarith only [hDη])) (by positivity)
    have hN_A : (N : ℝ)^(-η) ≤ (w : ℝ)^(-A) := by
      have hNR : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
      have ht : 0 < t := zero_lt_one.trans_le hlog
      have hN' : (N : ℝ)^(-η) ≤ t^(-A) := by
        rw [Real.rpow_neg ht.le, ← one_div]
        apply (le_div_iff₀ (Real.rpow_pos_of_pos ht A)).mpr
        rw [Real.rpow_def_of_pos hNR, mul_comm (Real.log (N : ℝ)), mul_comm]
        exact hNη.le
      exact hN'.trans (Real.rpow_le_rpow_of_nonpos hw hw_t (by linarith))
    have hv : OneBoundedOn (positiveInterval M) v := by
      intro y _
      change ‖((W : ℂ)⁻¹) * (F (V ((q : ℤ)*y) : Circle) - circleMean F)‖ ≤ 1
      rw [norm_mul, norm_inv, Complex.norm_of_nonneg hW.le, ← div_eq_inv_mul]
      exact (div_le_one hW).mpr
        ((hW₀ _ (Set.mem_univ _)).trans (le_max_right _ _))
    have hsp := positiveInterval_subset_spatialInterval hC N
    have hfbounded : ∀ i, OneBoundedOn (spatialInterval C N) (f i) :=
      fun i x _ => oneBounded_of_supported (hfb i) (hfs i) x
    have hfsupp : ∀ i, SupportedOn (spatialInterval C N) (f i) :=
      fun i x hn => hfs i x (fun h => hn (hsp h))
    have hcount := hVN N q hN hq hqScale hM P hP hPtop hcoeff v f hv hfbounded hfsupp ρ hρ hρ₂
      (hGuard q w hMod.1 hExtra)
    have hcount' := hcount.trans (mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add hN_A hρ_A) hSUPpower) hK.le)
    rw [← countingForm_mono_window N M hsp P hP.2.1 v f (hfs 0)] at hcount'
    have hweight : weight = (fun x => (W : ℂ) * v x) := by
      funext x
      have hWne : (W : ℂ) ≠ 0 := by exact_mod_cast hW.ne'
      simp only [v, ← mul_assoc, mul_inv_cancel₀ hWne, one_mul]
    rw [show (fun y => selectorWeight V F q y - circleMean F) = weight by rfl,
      hweight, countingForm_mul_weight, norm_mul, Complex.norm_of_nonneg hW.le]
    apply (mul_le_mul_of_nonneg_left hcount' hW.le).trans
    dsimp [K']
    ring_nf
    rfl
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hE
  exact ⟨K', hK', N₀, fun N q w hN => hN₀ N hN q w⟩

set_option maxHeartbeats 1800000 in
/-- The centered selector comparison follows from the local generalized
von Neumann estimate and ordinary phase cancellation on the bracketing
denominator's coprime progressions. Both inputs are original manuscript
obligations. The proof includes all uniform scale and normalization steps. -/
theorem unweightedSelectorComparison_of_local_phase
    (hVN : LocalGeneralizedVonNeumann) {c₀ cRel C : ℝ}
    (hc₀ : 0 < c₀) (hc₀' : c₀ < 1/11) (_hcRel : 0 < cRel) (hcRel' : cRel ≤ 1/10)
    (hC : 1 ≤ C) {w₀ d ℓ : ℕ} (hw₀ : 16 ≤ w₀) (hd : 0 < d) (hℓ : 0 < ℓ)
    {α β : ℝ} (F : Circle → ℂ) (hF : Continuous F)
    (hphase : ∃ r : ℕ → ℕ, AdmissibleBetaDenominators β r ∧
      CenteredHeisenbergPhaseEstimate d (heisenbergPhase α β) F r) :
    UnweightedSelectorComparison c₀ cRel C w₀ d ℓ (heisenbergPhase α β) F := by
  classical
  obtain ⟨η,A₁,A₂,K,B,hη,hA₁,hA₂,hK,hLocal⟩ := hVN C d ℓ hC hℓ
  intro A hA
  obtain ⟨K',hK',N₀,hCount⟩ := centeredSelectorComparison_using_local_phase
    (fun _ _ => True) (fun _ _ => True) hc₀ hc₀' _hcRel hcRel' hC hw₀ hd hℓ
    hη hA₁ hA₂ hK (B := B) (by
      intro N q hN hq hBound M hM P hP htop hCoeff v f hv hf hfs ρ hρ hρ' _
      exact hLocal N q hN hq hBound hM P hP htop hCoeff v f hv hf hfs ρ hρ hρ')
    A hA (fun w => (w : ℝ)^(-A-1)) (by
      intro w hw
      have hw' : (16 : ℝ) ≤ w := by exact_mod_cast hw₀.trans hw
      have hw₁ : (1 : ℝ) ≤ w := by linarith
      have hwPos : (0 : ℝ) < w := by linarith
      refine ⟨by positivity, ?_, le_rfl, Real.rpow_le_rpow_of_exponent_le hw₁ (by linarith)⟩
      calc
        _ ≤ (w : ℝ)^(-(1 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hw₁ (by linarith)
        _ ≤ _ := by
          rw [Real.rpow_neg_one, one_div]
          exact (inv_le_inv₀ hwPos (by norm_num : 0 < (2 : ℝ))).mpr (by linarith))
    (fun _ _ _ _ => trivial) F hF hphase
  exact ⟨K',hK',N₀,fun N q w hN hMod => hCount N q w hN hMod trivial⟩

end NilBohr
