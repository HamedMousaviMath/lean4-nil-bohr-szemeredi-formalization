import NilBohr.Definitions

/-! Choosing the short parameter intervals in the proof of Theorem 4.2. -/

open scoped BigOperators

namespace NilBohr

private theorem parameter_deletion_budget {ι : Type*} {d k q M L H : ℕ}
    (hq : 0 < q) (hM : 0 < M) (hL : 0 < L)
    {K c₁ D₁ σ r : ℝ} (hK : 0 ≤ K) (hc₁ : 0 < c₁) (hD₁ : 0 ≤ D₁)
    (hσ : 0 < σ) (hσ₁ : σ ≤ 1) (hr : 0 ≤ r)
    (S : Finset ι) (hS : S.card ≤ k) (e V : ι → ℕ)
    (he : ∀ i ∈ S, 0 < e i ∧ e i ≤ d)
    (hV : ∀ i ∈ S, c₁ * (M : ℝ)^(e i) * ((q : ℝ)/σ)^(-D₁) ≤ (V i : ℝ))
    (hH : (H : ℝ) ≤
      (2 * (K+1) * (1 + (k : ℝ)/c₁))⁻¹ * (M : ℝ) * r /
        ((q : ℝ)^(d-1) * ((q : ℝ)/σ)^D₁)) :
    K * ((H : ℝ)/(M : ℝ)) +
      K * (∑ i ∈ S, (q : ℝ)^(e i-1) * (M : ℝ)^(e i-1) * (H : ℝ) /
        ((L : ℝ) * (V i : ℝ))) ≤ r/2 := by
  let a := (2 * (K+1) * (1 + (k : ℝ)/c₁))⁻¹
  let Z := (q : ℝ)^(d-1) * ((q : ℝ)/σ)^D₁
  have ha : 0 < a := by unfold a; positivity
  have hq₁ : 1 ≤ (q : ℝ) := by exact_mod_cast hq
  have hq₀ : 0 < (q : ℝ) := by positivity
  have hM₀ : 0 < (M : ℝ) := by positivity
  have hL₁ : 1 ≤ (L : ℝ) := by exact_mod_cast hL
  have hquot : 1 ≤ (q : ℝ)/σ := by rw [le_div_iff₀ hσ, one_mul]; exact hσ₁.trans hq₁
  have hZ₁ : 1 ≤ Z := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hq₁)
    (Real.one_le_rpow hquot hD₁)
  have hZ : 0 < Z := one_pos.trans_le hZ₁
  change (H : ℝ) ≤ a * (M : ℝ) * r / Z at hH
  have hTail : (H : ℝ)/(M : ℝ) ≤ a*r := by
    apply (div_le_iff₀ hM₀).2
    exact hH.trans ((div_le_self (by positivity) hZ₁).trans_eq (by ring))
  have hTerm (i : ι) (hi : i ∈ S) :
      (q : ℝ)^(e i-1) * (M : ℝ)^(e i-1) * (H : ℝ) /
        ((L : ℝ) * (V i : ℝ)) ≤ (a*r)/c₁ := by
    obtain ⟨hei, hed⟩ := he i hi
    let W := ((q : ℝ)/σ)^D₁
    have hW : 0 < W := Real.rpow_pos_of_pos (div_pos hq₀ hσ) _
    have hVi := hV i hi
    rw [Real.rpow_neg (by positivity : 0 ≤ (q : ℝ)/σ)] at hVi
    change c₁ * (M : ℝ)^(e i) * W⁻¹ ≤ (V i : ℝ) at hVi
    have hVp : 0 < (V i : ℝ) :=
      (show 0 < c₁ * (M : ℝ)^(e i) * W⁻¹ by positivity).trans_le hVi
    have hden : c₁ * (M : ℝ)^(e i) / W ≤ (L : ℝ) * (V i : ℝ) := by
      rw [div_eq_mul_inv]
      exact hVi.trans (le_mul_of_one_le_left hVp.le hL₁)
    have hnum : (q : ℝ)^(e i-1) * (M : ℝ)^(e i-1) * (H : ℝ) ≤
        (q : ℝ)^(d-1) * (M : ℝ)^(e i-1) * (a * (M : ℝ) * r / Z) := by
      have hqpow : (q : ℝ)^(e i-1) ≤ (q : ℝ)^(d-1) :=
        pow_le_pow_right₀ hq₁ (Nat.sub_le_sub_right hed 1)
      exact mul_le_mul (mul_le_mul_of_nonneg_right hqpow (by positivity))
        hH (by positivity) (by positivity)
    calc
      _ ≤ ((q : ℝ)^(d-1) * (M : ℝ)^(e i-1) * (a * (M : ℝ) * r / Z)) /
          ((L : ℝ) * (V i : ℝ)) :=
        div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ ((q : ℝ)^(d-1) * (M : ℝ)^(e i-1) * (a * (M : ℝ) * r / Z)) /
          (c₁ * (M : ℝ)^(e i) / W) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ = (a*r)/c₁ := by
        rw [show e i = e i - 1 + 1 by omega, pow_succ (M : ℝ)]
        have hZe : Z = (q : ℝ)^(d-1) * W := rfl
        rw [hZe]
        field_simp
        ring
  have hsum : (∑ i ∈ S, (q : ℝ)^(e i-1) * (M : ℝ)^(e i-1) * (H : ℝ) /
          ((L : ℝ) * (V i : ℝ))) ≤ (k : ℝ) * ((a*r)/c₁) := by
    calc
      _ ≤ ∑ _ ∈ S, (a*r)/c₁ := Finset.sum_le_sum hTerm
      _ = (S.card : ℝ) * ((a*r)/c₁) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hS) (by positivity)
  calc
    _ ≤ K*(a*r) + K*((k : ℝ)*((a*r)/c₁)) :=
      add_le_add (mul_le_mul_of_nonneg_left hTail hK) (mul_le_mul_of_nonneg_left hsum hK)
    _ = K*a*(1+(k : ℝ)/c₁)*r := by ring
    _ ≤ (K+1)*a*(1+(k : ℝ)/c₁)*r := by gcongr; linarith
    _ = r/2 := by
      unfold a
      field_simp
      ring

/-- Choose an exact floor length with controlled tail and boundary deletion.
The constants depend on the deletion prefactor and the fixed power-law
thresholds for the count and the inverse theorem. -/
theorem choose_short_parameter_interval {ι : Type*} (d k : ℕ)
    (K c₁ D₁ s u t v : ℝ) (hK : 0 ≤ K) (hc₁ : 0 < c₁) (hD₁ : 0 ≤ D₁)
    (hs : 0 < s) (hu : 0 ≤ u) (ht : 0 < t) (hv : 0 ≤ v) :
    ∃ (a c : ℝ) (D : ℕ), 0 < a ∧ 0 < c ∧ 0 < D ∧
      ∀ (q M L : ℕ), 0 < q → 0 < M → 0 < L →
      ∀ (δ : ℝ), 0 < δ → δ ≤ 1 →
      let σ := s * δ^u
      let r := t * δ^v
      σ ≤ 1 → r ≤ 1 →
      ∀ (S : Finset ι), S.card ≤ k → ∀ (e V : ι → ℕ),
      (∀ i ∈ S, 0 < e i ∧ e i ≤ d) →
      (∀ i ∈ S, c₁ * (M : ℝ)^(e i) * ((q : ℝ)/σ)^(-D₁) ≤ (V i : ℝ)) →
      (M : ℝ) ≤ c⁻¹ * ((q : ℝ)/δ)^D ∨
        ∃ H : ℕ, H = ⌊a * (M : ℝ) * r /
            ((q : ℝ)^(d-1) * ((q : ℝ)/σ)^D₁)⌋₊ ∧
          0 < H ∧ H ≤ M ∧ c * (M : ℝ) * (q : ℝ)^(-(D : ℝ)) * δ^(D : ℝ) ≤ (H : ℝ) ∧
          K * ((H : ℝ)/(M : ℝ)) +
            K * (∑ i ∈ S, (q : ℝ)^(e i-1) * (M : ℝ)^(e i-1) * (H : ℝ) /
              ((L : ℝ) * (V i : ℝ))) ≤ r/2 := by
  let a := (2 * (K+1) * (1 + (k : ℝ)/c₁))⁻¹
  let c := (a * t * s^D₁)/2
  let A := ((d-1 : ℕ) : ℝ) + D₁
  let B := v + u*D₁
  let D := ⌈A+B⌉₊+1
  have ha : 0 < a := by unfold a; positivity
  have ha₁ : a ≤ 1 := by
    unfold a
    apply inv_le_one_of_one_le₀
    calc
      1 ≤ (2 : ℝ) := by norm_num
      _ ≤ 2 * (K+1) * (1 + (k : ℝ)/c₁) := by
        have hk : 0 ≤ (k : ℝ)/c₁ := by positivity
        nlinarith [mul_nonneg hK hk]
  have hc : 0 < c := by unfold c; positivity
  have hA : 0 ≤ A := by unfold A; positivity
  have hB : 0 ≤ B := by unfold B; positivity
  have hD : 0 < D := by unfold D; omega
  have hAD : A ≤ (D : ℝ) := by
    have hceil := Nat.le_ceil (A+B)
    simp only [D, Nat.cast_add, Nat.cast_one]
    linarith
  have hBD : B ≤ (D : ℝ) := by
    have hceil := Nat.le_ceil (A+B)
    simp only [D, Nat.cast_add, Nat.cast_one]
    linarith
  refine ⟨a,c,D,ha,hc,hD,?_⟩
  intro q M L hq hM hL δ hδ hδ₁ σ r hσ₁ hr₁ S hS e V he hV
  have hσ : 0 < σ := by dsimp [σ]; positivity
  have hr : 0 < r := by dsimp [r]; positivity
  have hq₁ : 1 ≤ (q : ℝ) := by exact_mod_cast hq
  have hq₀ : 0 < (q : ℝ) := by positivity
  have hM₀ : 0 < (M : ℝ) := by positivity
  let Z := (q : ℝ)^(d-1) * ((q : ℝ)/σ)^D₁
  let T := a * (M : ℝ) * r / Z
  have hquot : 1 ≤ (q : ℝ)/σ := by
    rw [le_div_iff₀ hσ, one_mul]; exact hσ₁.trans hq₁
  have hZ₁ : 1 ≤ Z := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hq₁)
    (Real.one_le_rpow hquot hD₁)
  have hZ : 0 < Z := one_pos.trans_le hZ₁
  have hT : 0 < T := by unfold T; positivity
  have hTM : T ≤ (M : ℝ) := by
    unfold T
    apply (div_le_self (by positivity) hZ₁).trans
    calc
      _ ≤ 1 * (M : ℝ) * 1 := by gcongr
      _ = _ := by ring
  have hZeq : Z = (q : ℝ)^A / (s^D₁ * δ^(u*D₁)) := by
    unfold Z A
    dsimp only [σ]
    rw [Real.div_rpow hq₀.le (by positivity), Real.mul_rpow hs.le (by positivity),
      ← Real.rpow_mul hδ.le,
      ← Real.rpow_natCast (x := (q : ℝ)), ← mul_div_assoc, ← Real.rpow_add hq₀]
  have hTeq : T = 2*c*(M : ℝ)*(q : ℝ)^(-A)*δ^B := by
    unfold T c B
    dsimp only [r]
    rw [hZeq, div_div_eq_mul_div, Real.rpow_neg hq₀.le, Real.rpow_add hδ]
    ring
  have hTlower : 2*c*(M : ℝ)*(q : ℝ)^(-(D : ℝ))*δ^(D : ℝ) ≤ T := by
    rw [hTeq]
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hq₁
        (neg_le_neg hAD)) (by positivity)
    · exact Real.rpow_le_rpow_of_exponent_ge hδ hδ₁ hBD
    · positivity
    · positivity
  by_cases hSmall : T < 2
  · left
    let U := ((q : ℝ)/δ)^D
    have hU : 0 < U := by unfold U; positivity
    have hInv : U⁻¹ = (q : ℝ)^(-(D : ℝ))*δ^(D : ℝ) := by
      unfold U
      rw [div_pow, inv_div, Real.rpow_neg hq₀.le, Real.rpow_natCast, Real.rpow_natCast,
        div_eq_mul_inv, mul_comm]
    have hCut : (2*c*(M : ℝ))/U < 2 := by
      rw [div_eq_mul_inv, hInv, ← mul_assoc]
      exact hTlower.trans_lt hSmall
    have hb := (div_lt_iff₀ hU).mp hCut
    have hM' : (M : ℝ) < c⁻¹ * U := by
      apply (lt_inv_mul_iff₀ hc).2
      linarith only [hb]
    exact hM'.le
  · right
    let H := ⌊T⌋₊
    have hH : (H : ℝ) ≤ T := Nat.floor_le hT.le
    have hHl : T/2 ≤ (H : ℝ) := by
      have hfloor := Nat.lt_floor_add_one T
      change T < (H : ℝ)+1 at hfloor
      linarith [le_of_not_gt hSmall]
    have hp : 0 < H := by
      have : (0 : ℝ) < H := (by positivity : 0 < T/2).trans_le hHl
      exact_mod_cast this
    refine ⟨H,rfl,hp,by exact_mod_cast hH.trans hTM,?_,?_⟩
    · linarith only [hHl, hTlower]
    · exact parameter_deletion_budget hq hM hL hK hc₁ hD₁ hσ hσ₁ hr.le
        S hS e V he hV hH

end NilBohr
