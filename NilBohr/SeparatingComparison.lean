import NilBohr.SeparatingScales
import NilBohr.ErgodicRate

/-! The two fixed-family dilation bounds in Appendix A and their exact
dependence on the global phase norm. -/

open Filter Polynomial
open scoped Topology

namespace NilBohr

private theorem mem_spatialInterval_real {C : ℝ} {N : ℕ} {x : ℤ} :
    x ∈ spatialInterval C N ↔ -C*(N : ℝ) ≤ (x : ℝ) ∧ (x : ℝ) ≤ C*(N : ℝ) := by
  simp only [spatialInterval, Finset.mem_Icc, Int.ceil_le, Int.le_floor]

noncomputable def fixedDilationFamily : Fin 2 → Polynomial ℤ :=
  ![X, X^2]

theorem degree_fixedDilationFamily (i : Fin 2) :
    (fixedDilationFamily i).natDegree = i.val+1 := by
  fin_cases i <;> simp [fixedDilationFamily]

theorem fixedDilationFamily_ergodic : ErgodicPolynomialFamily fixedDilationFamily := by
  refine ⟨by decide, fun i => ⟨?_,?_⟩,?_⟩
  · rw [degree_fixedDilationFamily]
    omega
  · fin_cases i <;> simp [fixedDilationFamily, coeff_X_pow]
  · intro i j hij
    change (fixedDilationFamily i).natDegree < (fixedDilationFamily j).natDegree
    rw [degree_fixedDilationFamily, degree_fixedDilationFamily]
    exact Nat.add_lt_add_right hij 1

theorem separatingFamily_one_eq : separatingFamily 1 = Fin.cases 0 fixedDilationFamily := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [separatingFamily]
  · rw [Fin.cases_succ]
    fin_cases j <;> simp [separatingFamily, fixedDilationFamily]

private theorem dilatedWeight_oneBounded {q M : ℕ} (hq : 0 < q)
    {v : ℤ → ℂ} (hv : OneBoundedOn (positiveInterval M) v) :
    OneBoundedOn (positiveInterval (q*M)) (dilatedWeight q v) := by
  intro n hn
  by_cases hd : (q : ℤ) ∣ n
  · obtain ⟨y, rfl⟩ := hd
    rw [dilatedWeight_at_multiple hq]
    have hqZ : (0 : ℤ) < q := by exact_mod_cast hq
    obtain ⟨h₁, h₂⟩ := Finset.mem_Icc.mp hn
    apply hv y
    refine Finset.mem_Icc.mpr ⟨?_,?_⟩
    · exact Int.add_one_le_iff.mpr ((mul_pos_iff_of_pos_left hqZ).mp
        (lt_of_lt_of_le (by norm_num) h₁))
    · push_cast at h₂
      exact (mul_le_mul_left hqZ).mp h₂
  · simp [dilatedWeight,hd]

private theorem dilated_spatialImage_subset {q N : ℕ} :
    (spatialInterval 1 N).image (fun x : ℤ => (q : ℤ)*x) ⊆ spatialInterval 2 (q*N) := by
  intro x hx
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
  rw [mem_spatialInterval_real] at hy ⊢
  push_cast
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left hy.1 hq,
    mul_le_mul_of_nonneg_left hy.2 hq, mul_nonneg hq hN]

private theorem repeat_position_mem_spatial {q N : ℕ} (hN : 0 < N)
    {y : ℤ} (hy : y ∈ spatialInterval 1 N) {a : ℤ} (ha : 0 ≤ a)
    (haq : a < (q : ℤ)) :
    (q : ℤ)*y+a ∈ spatialInterval 2 (q*N) := by
  rw [mem_spatialInterval_real] at hy ⊢
  push_cast
  have hq' : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have ha' : (0 : ℝ) ≤ a := by exact_mod_cast ha
  have haq' : (a : ℝ) ≤ q := by exact_mod_cast haq.le
  have ht : 0 ≤ (q : ℝ)*((N : ℝ)-1) := mul_nonneg hq' (sub_nonneg.mpr hN')
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left hy.1 hq',
    mul_le_mul_of_nonneg_left hy.2 hq']

private theorem repeated_spatialImage_subset {q N : ℕ} (hN : 0 < N) :
    repeatedSpatialWindow q (spatialInterval 1 N) ⊆ spatialInterval 2 (q*N) := by
  intro x hx
  obtain ⟨⟨y,a⟩,hya,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨hy,ha⟩ := Finset.mem_product.mp hya
  apply repeat_position_mem_spatial hN hy (by positivity)
  exact_mod_cast Finset.mem_range.mp ha

/-- The quantity inside the parentheses in the two fixed-family estimates
in Appendix A, with the exact (q^{-1}) normalization of the global norm. -/
noncomputable def fixedDilationPhaseBound (q M : ℕ) (v : ℤ → ℂ) : ℝ :=
  ((q*M : ℕ) : ℝ)⁻¹ + (q : ℝ)⁻¹ * phaseNorm 3 (positiveInterval M) v

set_option maxHeartbeats 600000 in
/-- The finite fixed-family comparison with both dilation losses, uniform
over the spatial inputs. Each use of the source fits the same spatial
window of size (2(qM)^2). -/
theorem separatingFixedFamily_bounds_of_teravainen (hTer : TeravainenFixedFamily) :
    ∃ K C : ℝ, 1 ≤ K ∧ 0 < C ∧ ∀ q M : ℕ, 0 < q → 0 < M →
      ∀ v : ℤ → ℂ, OneBoundedOn (positiveInterval M) v →
      let N := q*M^2
      ∀ f : Fin 3 → ℤ → ℂ,
        (∀ i, OneBoundedOn (spatialInterval 1 N) (f i)) →
        (∀ i, SupportedOn (spatialInterval 1 N) (f i)) →
        let T := countingForm N M (spatialInterval 1 N) (separatingFamily q) v f
        (‖T‖ ≤ C*(q : ℝ)^2*(fixedDilationPhaseBound q M v)^(1/K)) ∧
        (‖T‖ ≤ C*(q : ℝ)*(fixedDilationPhaseBound q M v)^(1/K)) := by
  obtain ⟨K, hK, hTer⟩ := hTer 2 (by decide)
  obtain ⟨C, hC, hTer⟩ := hTer fixedDilationFamily fixedDilationFamily_ergodic
    (fun i => by rw [degree_fixedDilationFamily]; omega) (by
      refine ⟨1,?_⟩
      rw [degree_fixedDilationFamily]
      decide) 2 (by norm_num)
  refine ⟨K,C,hK,hC,?_⟩
  intro q M hq hM v hv N f hf hfs
  let I := spatialInterval 1 N
  let J := spatialInterval 2 (q*N)
  let H := q*M
  have hH : 0 < H := Nat.mul_pos hq hM
  have hN : 0 < N := Nat.mul_pos hq (pow_pos hM _)
  have hSpace : H^2 = q*N := by dsimp [H,N]; ring
  have hqZ : (0 : ℤ) < q := by exact_mod_cast hq
  have hIn : (I.image (fun x : ℤ => (q : ℤ)*x)) ⊆ J := dilated_spatialImage_subset
  have hRep : repeatedSpatialWindow q I ⊆ J := repeated_spatialImage_subset hN
  have hv' : OneBoundedOn (positiveInterval H) (dilatedWeight q v) := dilatedWeight_oneBounded hq hv
  let f₀ (i : Fin 3) := dilatedWeight q (f i)
  let f₁ (i : Fin 3) (x : ℤ) := f i (x/(q:ℤ))
  have h₀ (i : Fin 3) (x : ℤ) : ‖f₀ i x‖ ≤ 1 := by
    by_cases hx : (q : ℤ) ∣ x
    · obtain ⟨y,rfl⟩ := hx
      change ‖dilatedWeight q (f i) ((q : ℤ)*y)‖ ≤ 1
      rw [dilatedWeight_at_multiple hq]
      exact oneBounded_of_supported (hf i) (hfs i) y
    · dsimp [f₀]
      simp [dilatedWeight,hx]
  have h₁ (i : Fin 3) (x : ℤ) : ‖f₁ i x‖ ≤ 1 :=
    oneBounded_of_supported (hf i) (hfs i) _
  have h₀s (i : Fin 3) :
      SupportedOn (I.image (fun x : ℤ => (q : ℤ)*x)) (f₀ i) := by
    intro x hx
    by_cases hd : (q : ℤ) ∣ x
    · obtain ⟨y,rfl⟩ := hd
      change dilatedWeight q (f i) ((q : ℤ)*y) = 0
      rw [dilatedWeight_at_multiple hq]
      exact hfs i y (fun hy => hx (Finset.mem_image_of_mem _ hy))
    · simp [f₀,dilatedWeight,hd]
  have h₁s (i : Fin 3) : SupportedOn (repeatedSpatialWindow q I) (f₁ i) := by
    intro x hx
    have hrem : 0 ≤ x % (q : ℤ) := Int.emod_nonneg _ hqZ.ne'
    have hrem' : x % (q : ℤ) < (q : ℤ) := Int.emod_lt_of_pos _ hqZ
    apply hfs i
    intro hy
    let a := (x % (q : ℤ)).toNat
    have ha : (a : ℤ) = x % (q : ℤ) := Int.toNat_of_nonneg hrem
    have haq : a < q := by omega
    apply hx
    refine Finset.mem_image.mpr ⟨(x/(q : ℤ),a), Finset.mem_product.mpr
      ⟨hy,Finset.mem_range.mpr haq⟩,?_⟩
    change (q : ℤ)*(x/(q : ℤ))+(a : ℤ) = x
    rw [ha, add_comm]
    exact Int.emod_add_ediv _ _
  have hTer' (g : Fin 3 → ℤ → ℂ) (hg : ∀ i x, ‖g i x‖ ≤ 1) (U : Finset ℤ)
      (hU : U ⊆ J) (hgs : ∀ i, SupportedOn U (g i)) :
      ‖countingForm (q*N) H U (separatingFamily 1) (dilatedWeight q v) g‖ ≤
        C * (fixedDilationPhaseBound q M v)^(1/K) := by
    rw [countingForm_mono_window (q*N) H hU _ (by simp [separatingFamily]) _ _ (hgs 0),
      separatingFamily_one_eq]
    have hSupport (i : Fin 3) : SupportedOn (spatialInterval 2 (H^2)) (g i) := by
      intro x hx
      exact hgs i x (fun hu => hx (hSpace ▸ hU hu))
    have h := hTer H hH (dilatedWeight q v) g hv' (fun i x _ => hg i x) hSupport
    have hphase := phaseNorm_dilatedWeight (M := M) (show 0 < 3 by decide) hq v
    change phaseNorm 3 (positiveInterval H) (dilatedWeight q v) = _ at hphase
    rw [hSpace, hphase] at h
    simpa only [H, fixedDilationPhaseBound,
      div_eq_inv_mul (phaseNorm 3 (positiveInterval M) v) (q : ℝ)] using h
  constructor
  · rw [countingForm_separatingFamily_dilate hN hM hq I v f, norm_mul, norm_pow,
      Complex.norm_natCast]
    exact (mul_le_mul_of_nonneg_left (hTer' f₀ h₀ _ hIn h₀s)
      (by positivity : 0 ≤ (q : ℝ)^2)).trans_eq (by ring)
  · rw [countingForm_separatingFamily_repeat hN hM hq I v f, norm_mul,
      Complex.norm_natCast]
    exact (mul_le_mul_of_nonneg_left (hTer' f₁ h₁ _ hRep h₁s)
      (by positivity : 0 ≤ (q : ℝ))).trans_eq (by ring)

/-- A uniform weight bound costs one constant in the two fixed-family
estimates, while leaving their global phase expressions unchanged. -/
theorem separatingFixedFamily_bounds_of_bounded (hTer : TeravainenFixedFamily) :
    ∃ K C : ℝ, 1 ≤ K ∧ 0 < C ∧ ∀ q M : ℕ, 0 < q → 0 < M →
      ∀ (D : ℝ) (v : ℤ → ℂ), 1 ≤ D → (∀ y ∈ positiveInterval M, ‖v y‖ ≤ D) →
      let N := q*M^2
      ∀ f : Fin 3 → ℤ → ℂ,
        (∀ i, OneBoundedOn (spatialInterval 1 N) (f i)) →
        (∀ i, SupportedOn (spatialInterval 1 N) (f i)) →
        let T := countingForm N M (spatialInterval 1 N) (separatingFamily q) v f
        (‖T‖ ≤ C*D*(q : ℝ)^2*(fixedDilationPhaseBound q M v)^(1/K)) ∧
        (‖T‖ ≤ C*D*(q : ℝ)*(fixedDilationPhaseBound q M v)^(1/K)) := by
  obtain ⟨K,C,hK,hC,hTer⟩ := separatingFixedFamily_bounds_of_teravainen hTer
  refine ⟨K,C,hK,hC,?_⟩
  intro q M hq hM D v hD hv N f hf hfs
  let w : ℤ → ℂ := fun y => (D⁻¹ : ℝ)*v y
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  have hscal : ‖((D⁻¹ : ℝ) : ℂ)‖ = D⁻¹ := by
    rw [Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hDpos.le)]
  have hnorm : OneBoundedOn (positiveInterval M) w := by
    intro y hy
    change ‖((D⁻¹ : ℝ) : ℂ)*v y‖ ≤ 1
    rw [norm_mul, hscal, inv_mul_eq_div]
    exact (div_le_one hDpos).mpr (hv y hy)
  have hvw : v = fun y => (D : ℂ)*w y := by
    funext y
    change _ = (D : ℂ)*(((D⁻¹ : ℝ) : ℂ)*v y)
    rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hDpos.ne', Complex.ofReal_one, one_mul]
  have hphase : phaseNorm 3 (positiveInterval M) w ≤ phaseNorm 3 (positiveInterval M) v := by
    refine (phaseNorm_const_mul_le (by decide) (positiveInterval M) v _).trans ?_
    rw [hscal]
    exact mul_le_of_le_one_left (phaseNorm_nonneg_of_pos (by decide) _ _) ((inv_le_one₀ hDpos).mpr hD)
  have hle : fixedDilationPhaseBound q M w ≤ fixedDilationPhaseBound q M v :=
    add_le_add_left (mul_le_mul_of_nonneg_left hphase (by positivity)) _
  have hnonneg : 0 ≤ fixedDilationPhaseBound q M w :=
    add_nonneg (by positivity) (mul_nonneg (by positivity) (phaseNorm_nonneg_of_pos (by decide) _ _))
  have hPow := Real.rpow_le_rpow hnonneg hle (by positivity : 0 ≤ 1/K)
  have hT : ‖countingForm N M (spatialInterval 1 N) (separatingFamily q) v f‖ =
      D*‖countingForm N M (spatialInterval 1 N) (separatingFamily q) w f‖ := by
    rw [hvw, countingForm_mul_weight, norm_mul, Complex.norm_real, Real.norm_of_nonneg hDpos.le]
  obtain ⟨h₀,h₁⟩ := hTer q M hq hM w hnorm f hf hfs
  change ‖countingForm N M (spatialInterval 1 N) (separatingFamily q) v f‖ ≤ _ ∧ _
  rw [hT]
  refine ⟨?_,?_⟩
  · have h := mul_le_mul_of_nonneg_left (h₀.trans (mul_le_mul_of_nonneg_left hPow
        (by positivity : 0 ≤ C*(q : ℝ)^2))) hDpos.le
    exact h.trans_eq (by ring)
  · have h := mul_le_mul_of_nonneg_left (h₁.trans (mul_le_mul_of_nonneg_left hPow
        (by positivity : 0 ≤ C*(q : ℝ)))) hDpos.le
    exact h.trans_eq (by ring)

/-- The exact repeated-input endpoint (K=1). -/
theorem repeatedDilationPhaseBound_one {q M : ℕ} (hq : 0 < q)
    (v : ℤ → ℂ) :
    (q : ℝ) * (fixedDilationPhaseBound q M v)^(1/(1 : ℝ)) =
      (M : ℝ)⁻¹+phaseNorm 3 (positiveInterval M) v := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [div_self (by norm_num : (1:ℝ) ≠ 0), Real.rpow_one]
  simp only [fixedDilationPhaseBound, Nat.cast_mul, mul_add, mul_inv_rev, ← mul_assoc,
    mul_inv_cancel₀ hq', one_mul]
  rw [show (q : ℝ)*(M : ℝ)⁻¹*(q : ℝ)⁻¹ = (M : ℝ)⁻¹*((q : ℝ)*(q : ℝ)⁻¹) by ring,
    mul_inv_cancel₀ hq', mul_one]

/-- The growth mechanism in the two vacuous upper bounds. Any positive
power of the smooth modulus dominates every fixed power of the denominator. -/
theorem separating_modulus_power_tendsto (q r : ℕ → ℕ)
    (hr : Tendsto r atTop atTop)
    (hscale : ∀ᶠ j in atTop, 0 < q j ∧
      (Real.log (r j : ℝ))^2/8 ≤ Real.log (q j : ℝ))
    {c σ : ℝ} (hc : 0 < c) :
    Tendsto (fun j => (q j : ℝ)^c*(r j : ℝ)^(-σ)) atTop atTop := by
  have hr' : Tendsto (fun j => (r j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hr
  have hlog := Real.tendsto_log_atTop.comp hr'
  apply tendsto_atTop_mono' atTop ?_ hr'
  filter_upwards [hscale,hlog.eventually_ge_atTop (8*(σ+1)/c),
    hr'.eventually_ge_atTop 1] with j hj hlarge hr₁
  obtain ⟨hq,hqlog⟩ := hj
  have hqp : (0 : ℝ) < q j := by exact_mod_cast hq
  have hrp : (0 : ℝ) < r j := zero_lt_one.trans_le hr₁
  have ht : 0 ≤ Real.log (r j : ℝ) := Real.log_nonneg hr₁
  change 8*(σ+1)/c ≤ Real.log (r j : ℝ) at hlarge
  have h₁ := mul_le_mul_of_nonneg_left hqlog hc.le
  have h₂ := mul_le_mul_of_nonneg_right ((div_le_iff₀ hc).mp hlarge) ht
  calc
    (r j : ℝ) = Real.exp (Real.log (r j : ℝ)) := (Real.exp_log hrp).symm
    _ ≤ (q j : ℝ)^c*(r j : ℝ)^(-σ) := by
      rw [Real.rpow_def_of_pos hqp, Real.rpow_def_of_pos hrp, ← Real.exp_add, Real.exp_le_exp]
      nlinarith only [h₁,h₂]

/-- Every fixed positive modulus power overwhelms any fixed positive
power of the small global ordinary-phase norm. -/
theorem separating_phaseNorm_loss_tendsto (q M r : ℕ → ℕ) (v : ℕ → ℤ → ℂ)
    (hr : Tendsto r atTop atTop)
    (hscale : ∀ᶠ j in atTop, 0 < q j ∧
      (Real.log (r j : ℝ))^2/8 ≤ Real.log (q j : ℝ))
    {L c σ : ℝ} (hL : 0 < L) (hc : 0 < c) (hσ : 0 < σ)
    (hlower : ∀ᶠ j in atTop, L/(r j : ℝ) ≤ phaseNorm 3 (positiveInterval (M j)) (v j)) :
    Tendsto (fun j => (q j : ℝ)^c*(phaseNorm 3 (positiveInterval (M j)) (v j))^σ)
      atTop atTop := by
  have h := separating_modulus_power_tendsto q r hr hscale (σ := σ) hc
  apply tendsto_atTop_mono' atTop ?_ (h.const_mul_atTop (Real.rpow_pos_of_pos hL σ))
  filter_upwards [hlower,hr.eventually_ge_atTop 1] with j hlow hrj
  have hrp : (0 : ℝ) < r j := by exact_mod_cast (show 0 < r j by omega)
  have hl := Real.rpow_le_rpow (div_nonneg hL.le hrp.le) hlow hσ.le
  calc
    _ = (q j : ℝ)^c*(L/(r j : ℝ))^σ := by
      rw [Real.rpow_neg hrp.le, Real.div_rpow hL.le hrp.le]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hl (by positivity)

/-- For the global (u^3) lower bound of order (1/r), the right-hand
side of the fixed-family estimate diverges whenever its dilation power
is larger than (1/K). -/
theorem separating_fixedDilationBound_tendsto (q M r : ℕ → ℕ) (v : ℕ → ℤ → ℂ)
    (hr : Tendsto r atTop atTop)
    (hscale : ∀ᶠ j in atTop, 0 < q j ∧
      (Real.log (r j : ℝ))^2/8 ≤ Real.log (q j : ℝ))
    {L K b : ℝ} (hL : 0 < L) (hK : 1 ≤ K) (hb : 1/K < b)
    (hlower : ∀ᶠ j in atTop, L/(r j : ℝ) ≤ phaseNorm 3 (positiveInterval (M j)) (v j)) :
    Tendsto (fun j => (q j : ℝ)^b *
      (fixedDilationPhaseBound (q j) (M j) (v j))^(1/K)) atTop atTop := by
  have hK' : 0 < K := zero_lt_one.trans_le hK
  have hσ : 0 < 1/K := by positivity
  have hbase := separating_modulus_power_tendsto q r hr hscale
    (σ := 1/K) (sub_pos.mpr hb)
  have hbase' := hbase.const_mul_atTop (Real.rpow_pos_of_pos hL (1/K))
  apply tendsto_atTop_mono' atTop ?_ hbase'
  filter_upwards [hscale,hlower,hr.eventually_ge_atTop 1] with j hq hlow hrj
  have hqp : (0 : ℝ) < q j := by exact_mod_cast hq.1
  have hrp : (0 : ℝ) < r j := by exact_mod_cast (show 0 < r j by omega)
  have hlow' : (q j : ℝ)⁻¹ * (L/(r j : ℝ)) ≤ fixedDilationPhaseBound (q j) (M j) (v j) :=
    (mul_le_mul_of_nonneg_left hlow (inv_nonneg.mpr hqp.le)).trans
      (le_add_of_nonneg_left (inv_nonneg.mpr (Nat.cast_nonneg _)))
  have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ (q j : ℝ)⁻¹*(L/(r j : ℝ))) hlow' hσ.le
  calc
    _ = (q j : ℝ)^b * ((q j : ℝ)⁻¹*(L/(r j : ℝ)))^(1/K) := by
      rw [Real.mul_rpow (inv_nonneg.mpr hqp.le) (by positivity),
        Real.div_rpow hL.le hrp.le, Real.inv_rpow hqp.le,
        Real.rpow_neg hrp.le, Real.rpow_sub hqp]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)

end NilBohr
