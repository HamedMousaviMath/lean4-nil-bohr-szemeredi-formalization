import NilBohr.PrimeLocalProof
import NilBohr.SeparatingComparison
import NilBohr.ArcApproximation

/-! The ambient, sharp-arc comparison in the introduction.
Its square-root parameter scale is independent of smooth moduli. -/

open Filter MeasureTheory Polynomial
open scoped Topology NNReal

namespace NilBohr
noncomputable section

private def ambientInputs (A : Finset ℤ) : Fin 3 → ℤ → ℂ :=
  fun _ x => if x ∈ A then 1 else 0

/-- The weighted three-term count in the proof overview. For the
indicator input the full sum over integers reduces to the finite base
window, since the shift of the base coordinate is zero. -/
def ambientSelectorCount (N : ℕ) (A : Finset ℤ) (V : ℤ → ℝ) (F : Circle → ℂ) : ℂ :=
  countingForm N N.sqrt (positiveInterval N) (separatingFamily 1)
    (fun n => (ArithmeticFunction.vonMangoldt (n+1).toNat : ℂ) * F (V n : Circle))
    (ambientInputs A)

private theorem tendsto_nat_sqrt : Tendsto Nat.sqrt atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (b*b)] with n hn
  exact (Nat.le_sqrt).2 hn

private theorem ambientWindow_subset {N : ℕ} (hM : 0 < N.sqrt) :
    positiveInterval N ⊆ spatialInterval 4 (N.sqrt^2) := by
  intro x hx
  obtain ⟨hl,hu⟩ := Finset.mem_Icc.mp hx
  simp only [spatialInterval, Finset.mem_Icc, Int.ceil_le, Int.le_floor]
  have hM' : (1 : ℝ) ≤ N.sqrt := by exact_mod_cast hM
  have hN' : (N : ℝ) < ((N.sqrt : ℝ)+1)^2 := by exact_mod_cast Nat.lt_succ_sqrt' N
  have hN'' : (N : ℝ) ≤ 4*((N.sqrt^2 : ℕ) : ℝ) := by
    push_cast
    exact hN'.le.trans (by nlinarith [mul_nonneg (sub_nonneg.mpr hM') (by positivity :
      0 ≤ 3*(N.sqrt:ℝ)+1)])
  constructor
  · have hx' : (1 : ℝ) ≤ x := by exact_mod_cast hl
    linarith [show (0 : ℝ) ≤ ((N.sqrt^2:ℕ):ℝ) by positivity]
  · exact (by exact_mod_cast hu : (x : ℝ) ≤ N).trans hN''

private theorem ambient_count_from_square {N : ℕ} (hM : 0 < N.sqrt)
    (A : Finset ℤ) (hA : A ⊆ positiveInterval N) (θ : ℤ → ℂ) :
    countingForm N N.sqrt (positiveInterval N) (separatingFamily 1) θ (ambientInputs A) =
      (((N.sqrt^2 : ℕ) : ℂ) / (N : ℂ)) *
        countingForm (N.sqrt^2) N.sqrt (spatialInterval 4 (N.sqrt^2))
          (separatingFamily 1) θ (ambientInputs A) := by
  have hN : 0 < N := hM.trans_le (Nat.sqrt_le_self _)
  have hbase : SupportedOn (positiveInterval N) (ambientInputs A 0) := by
    intro x hx
    exact if_neg (fun hx' => hx (hA hx'))
  have hz : separatingFamily 1 0 = 0 := by simp [separatingFamily]
  rw [countingForm_mono_window N N.sqrt (ambientWindow_subset hM) _ hz θ _ hbase]
  have hn : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hm : ((N.sqrt : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  simp only [countingForm, Nat.cast_pow]
  field_simp
  ring

private theorem ambientInput_le (A : Finset ℤ) (i : Fin 3) (x : ℤ) :
    ‖ambientInputs A i x‖ ≤ 1 := by
  by_cases hx : x ∈ A <;> simp [ambientInputs, hx]

private theorem ambientInput_supported (A : Finset ℤ) {N : ℕ}
    (hA : A ⊆ positiveInterval N) (hM : 0 < N.sqrt) (i : Fin 3) :
    SupportedOn (spatialInterval 4 (N.sqrt^2)) (ambientInputs A i) := by
  intro x hx
  exact if_neg (fun hxA => hx (ambientWindow_subset hM (hA hxA)))

/-- Smooth comparison in the original counting normalization, uniformly
in all spatial sets at a given cutoff. -/
theorem ambientSelectorCount_centered {V : ℤ → ℝ} {F : Circle → ℂ}
    (hTer : TeravainenFixedFamily) (hp : PrimeLocalPhase 2 V F) {W : ℝ} (hW : 0 ≤ W)
    (hF : ∀ n : ℤ, ‖F (V n : Circle) - circleMean F‖ ≤ W) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℤ, A ⊆ positiveInterval N →
      ‖ambientSelectorCount N A V F -
          circleMean F * ambientSelectorCount N A V (fun _ => 1)‖ < ε := by
  let w (n : ℤ) := F (V n : Circle) - circleMean F
  let θ (n : ℤ) := (ArithmeticFunction.vonMangoldt (n+1).toNat : ℂ) * w n
  let L (M : ℕ) : ℝ := (W+1)*(2*Real.log M+1)
  let u (M : ℕ) (n : ℤ) : ℂ := ((L M)⁻¹ : ℝ) * θ n
  obtain ⟨K,hK,hTer⟩ := hTer 2 (by decide)
  obtain ⟨C,hC,hTer⟩ := hTer fixedDilationFamily fixedDilationFamily_ergodic
    (fun i => by rw [degree_fixedDilationFamily]; omega)
    ⟨1, by rw [degree_fixedDilationFamily]; decide⟩ 4 (by norm_num)
  have hK₀ : 0 < K := zero_lt_one.trans_le hK
  obtain ⟨E,hE,hPhase⟩ := phaseNorm_mangoldt_eventually_log_decay (by decide : 0 < (2:ℕ))
    V F hp (show 0 < K*2 from by positivity)
  let D := 3*(W+1)*C*(1+E)^(1/K)
  have hzero : Tendsto (fun M : ℕ => D*(Real.log (M:ℝ))^(-(1:ℝ))) atTop (𝓝 0) := by
    rw [show (0:ℝ) = D*0 by simp]
    exact ((tendsto_rpow_neg_atTop (show (0:ℝ)<1 by norm_num)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).const_mul D
  have hlog : Tendsto (fun M : ℕ => Real.log (M:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlarge := (eventually_ge_atTop (2 : ℕ)).and
    ((hlog.eventually_ge_atTop 1).and (hPhase.and
      ((eventually_inv_le_log_rpow_neg (K*2)).and (hzero.eventually (Iio_mem_nhds hε)))))
  filter_upwards [tendsto_nat_sqrt.eventually hlarge] with N hN A hA
  let M := N.sqrt
  obtain ⟨hM₂,hlogM,hPhase,hInv,hεM⟩ := hN
  have hM : 0 < M := by omega
  have hL : 1 ≤ L M := by
    dsimp [L]
    nlinarith [mul_nonneg hW (show 0 ≤ Real.log (M:ℝ) by linarith)]
  have hLp : 0 < L M := zero_lt_one.trans_le hL
  have hu : OneBoundedOn (positiveInterval M) (u M) := by
    intro n hn
    have h := norm_mangoldt_weight_le hW w hF hM₂ hn
    change ‖(((L M)⁻¹ : ℝ) : ℂ) * θ n‖ ≤ 1
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hLp.le)]
    exact (inv_mul_le_one₀ hLp).mpr h
  have hQ : phaseNorm 3 (positiveInterval M) (u M) ≤ E * (Real.log M)^(-(K*2)) := by
    refine (phaseNorm_const_mul_le (by decide) _ θ (((L M)⁻¹ : ℝ) : ℂ)).trans ?_
    rw [Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hLp.le)]
    exact (mul_le_of_le_one_left (phaseNorm_nonneg_of_pos (by decide : 0 < (3:ℕ)) _ _)
      (inv_le_one_of_one_le₀ hL)).trans hPhase
  have hBound := hTer M hM (u M) (ambientInputs A) hu (fun i x _ => ambientInput_le A i x)
    (fun i => ambientInput_supported A hA hM i)
  rw [← separatingFamily_one_eq] at hBound
  have hWeight : θ = fun n => (L M : ℂ)*u M n := by
    funext n
    simp only [u, Complex.ofReal_inv, ← mul_assoc, mul_inv_cancel₀
      (show (L M : ℂ) ≠ 0 by exact_mod_cast hLp.ne'), one_mul]
  have hRatio : ‖(((M^2 : ℕ) : ℂ)/(N:ℂ))‖ ≤ 1 := by
    have hNp : 0 < N := hM.trans_le (Nat.sqrt_le_self _)
    rw [norm_div, Complex.norm_natCast, Complex.norm_natCast, div_le_one (by exact_mod_cast hNp)]
    exact_mod_cast Nat.sqrt_le' N
  have hExp : ((1+E) * (Real.log M)^(-(K*2)))^(1/K) =
      (1+E)^(1/K) * (Real.log M)^(-2:ℝ) := by
    rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg (by linarith) _),
      ← Real.rpow_mul (by linarith)]
    congr 2
    field_simp [hK₀.ne']
    ring
  have hTotal : L M * (C * ((M:ℝ)⁻¹ + phaseNorm 3 (positiveInterval M) (u M))^(1/K))
      ≤ D * (Real.log M)^(-(1:ℝ)) := by
    have hInside : (M:ℝ)⁻¹ + phaseNorm 3 (positiveInterval M) (u M) ≤
        (1+E)*(Real.log M)^(-(K*2)) := by rw [add_mul, one_mul]; exact add_le_add hInv hQ
    have hL' : L M ≤ 3*(W+1)*Real.log M := by
      dsimp [L]
      nlinarith [mul_nonneg (show 0 ≤ W+1 by positivity)
        (show 0 ≤ Real.log (M:ℝ)-1 by linarith)]
    calc
      _ ≤ 3*(W+1)*Real.log M * (C * (((1+E)*(Real.log M)^(-(K*2)))^(1/K))) := by
        have hsrc : 0 ≤ (M:ℝ)⁻¹ + phaseNorm 3 (positiveInterval M) (u M) :=
          add_nonneg (by positivity) (phaseNorm_nonneg_of_pos (by decide : 0 < (3:ℕ)) _ _)
        have hpow := Real.rpow_le_rpow hsrc hInside (show 0 ≤ 1/K by positivity)
        exact mul_le_mul hL' (mul_le_mul_of_nonneg_left hpow hC.le)
          (mul_nonneg hC.le (Real.rpow_nonneg hsrc _)) (by positivity)
      _ = _ := by
        rw [hExp]
        have hProd : Real.log M * (Real.log M)^(-2:ℝ) = (Real.log M)^(-(1:ℝ)) := by
          nth_rw 1 [← Real.rpow_one (Real.log (M:ℝ))]
          rw [← Real.rpow_add (by linarith)]
          norm_num
        dsimp [D]
        rw [← hProd]
        ring
  have hCenter : ambientSelectorCount N A V F - circleMean F * ambientSelectorCount N A V (fun _ => 1) =
      countingForm N M (positiveInterval N) (separatingFamily 1) θ (ambientInputs A) := by
    unfold ambientSelectorCount
    apply sub_eq_of_eq_add
    rw [← countingForm_mul_weight, ← countingForm_add_weight]
    congr 1
    funext n
    simp [θ, w]
    ring
  rw [hCenter, ambient_count_from_square hM A hA θ,
    hWeight, countingForm_mul_weight, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg hLp.le]
  exact ((mul_le_of_le_one_left (mul_nonneg hLp.le (norm_nonneg _)) hRatio).trans
    ((mul_le_mul_of_nonneg_left hBound hLp.le).trans hTotal)).trans_lt hεM

end
end NilBohr
