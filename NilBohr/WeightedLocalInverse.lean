import NilBohr.RemarkLocalFactors
import NilBohr.DifferenceWitnesses
import NilBohr.External

/-! Conditional assembly of the weighted local inverse theorem, Lemma 5.1. -/

open Polynomial
open scoped BigOperators

namespace NilBohr

private theorem parameterLength_bounds {N q d : ℕ} (hN : 0 < N) (hq : 0 < q) (hd : 0 < d)
    (hM : 0 < parameterLength N q d) :
    let M := parameterLength N q d
    (M : ℝ)^d ≤ N ∧ (N : ℝ) ≤ (q : ℝ)^(d - 1) * (2 * (M : ℝ))^d := by
  let M := parameterLength N q d
  change (M : ℝ)^d ≤ N ∧ _
  let Q := (q : ℝ)^(d - 1)
  let x := ((N : ℝ) / Q)^((d : ℝ)⁻¹)
  have hqR : 1 ≤ (q : ℝ) := by exact_mod_cast hq
  have hMR : 1 ≤ (M : ℝ) := by exact_mod_cast hM
  have hQ : 1 ≤ Q := one_le_pow₀ hqR
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hNx : 0 ≤ (N : ℝ) / Q := by positivity
  have hx : 0 ≤ x := Real.rpow_nonneg hNx _
  have hfloor : (M : ℝ) ≤ x := Nat.floor_le hx
  have hnext : x < (M : ℝ) + 1 := Nat.lt_floor_add_one x
  have hex : x^d = (N : ℝ) / Q := by
    dsimp only [x]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNx, inv_mul_cancel₀ hdR, Real.rpow_one]
  constructor
  · calc
      (M : ℝ)^d ≤ x^d := pow_le_pow_left₀ (Nat.cast_nonneg _) hfloor _
      _ = (N : ℝ) / Q := hex
      _ ≤ N := div_le_self (Nat.cast_nonneg _) hQ
  · change (N : ℝ) ≤ Q * (2 * (M : ℝ))^d
    have hx2 : x ≤ 2 * (M : ℝ) := by linarith only [hnext, hMR]
    have hp := pow_le_pow_left₀ hx hx2 d
    calc
      (N : ℝ) = Q * x^d := by rw [hex, mul_div_cancel₀ _ (by positivity : Q ≠ 0)]
      _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)

private theorem sqrt_bound_of_subexponential (N q J : ℕ) (hN : 1 ≤ N)
    (hq : (q : ℝ) ≤ Real.exp ((Real.log (N : ℝ))^(1 / 10 : ℝ))) :
    (q : ℝ)^J ≤ Real.exp ((J : ℝ) * (2 * J + 1)) * Real.sqrt (N : ℝ) := by
  let u := (Real.log (N : ℝ))^(1 / 10 : ℝ)
  have hNR : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hNR
  have hu : 0 ≤ u := Real.rpow_nonneg hlog _
  have huPow : u^(10 : ℕ) = Real.log (N : ℝ) := by
    dsimp only [u]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hlog]
    norm_num
  have hdom : (J : ℝ) * u ≤ (J : ℝ) * (2 * J + 1) + Real.log (N : ℝ) / 2 := by
    by_cases hsmall : u ≤ 2 * (J : ℝ) + 1
    · linarith [mul_le_mul_of_nonneg_left hsmall (Nat.cast_nonneg J)]
    · have huone : 1 ≤ u := by linarith [(show (0 : ℝ) ≤ J from Nat.cast_nonneg J)]
      have h := pow_le_pow_right₀ huone (by norm_num : (2 : ℕ) ≤ 10)
      rw [huPow] at h
      nlinarith only [h, not_le.mp hsmall, mul_le_mul_of_nonneg_right
        (show 2 * (J : ℝ) ≤ u by linarith) hu, show (0 : ℝ) ≤ (J : ℝ) * (2 * J + 1) by positivity]
  calc
    (q : ℝ)^J ≤ (Real.exp u)^J := pow_le_pow_left₀ (Nat.cast_nonneg q) hq _
    _ = Real.exp ((J : ℝ)*u) := by rw [Real.exp_nat_mul]
    _ ≤ Real.exp ((J : ℝ)*(2 * J + 1) + Real.log (N : ℝ) / 2) := Real.exp_le_exp.mpr hdom
    _ = _ := by
      rw [Real.exp_add]
      congr 1
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by positivity : (0 : ℝ) < N)]
      ring_nf

/-- The small parameter-scale alternative yields a polynomial upper bound
for the spatial scale when the modulus is subexponential in its logarithm. -/
theorem space_bound_of_small_parameterLength (d E : ℕ) (B : ℝ) (hB : 0 < B) (hd : 0 < d) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N q : ℕ) (ρ : ℝ), 0 < N → 0 < q → 0 < ρ →
      (q : ℝ) ≤ Real.exp ((Real.log (N : ℝ))^(1 / 10 : ℝ)) →
      0 < parameterLength N q d →
      (parameterLength N q d : ℝ) ≤ B * ((q : ℝ) / ρ)^E →
      (N : ℝ) ≤ K * ρ^(-((2 * E * d : ℕ) : ℝ)) := by
  let J := d - 1 + E * d
  let K₀ := (2 * B)^d * Real.exp ((J : ℝ) * (2 * J + 1))
  have hK₀ : 0 < K₀ := by positivity
  refine ⟨K₀^2, sq_pos_of_pos hK₀, ?_⟩
  intro N q ρ hN hq hρ hqBound hM hSmall
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hSq := parameterLength_bounds hN hq hd hM
  dsimp only at hSq
  have hUpper : (N : ℝ) ≤ (2 * B)^d * (q : ℝ)^J / ρ^(E*d) := by
    calc
      (N : ℝ) ≤ (q : ℝ)^(d - 1) * (2 * (parameterLength N q d : ℝ))^d := hSq.2
      _ ≤ (q : ℝ)^(d - 1) * (2 * (B * ((q : ℝ) / ρ)^E))^d := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply pow_le_pow_left₀ (by positivity)
        gcongr
      _ = _ := by
        dsimp only [J]
        rw [show 2 * (B * ((q : ℝ) / ρ)^E) = (2 * B) * ((q : ℝ) / ρ)^E by ring,
          mul_pow, ← pow_mul, div_pow, pow_add]
        ring
  have hSqrt : (0 : ℝ) < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hNR
  have hUpper' := hUpper.trans
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (sqrt_bound_of_subexponential N q J (by omega) hqBound)
        (show 0 ≤ (2 * B)^d by positivity))
      (show 0 ≤ ρ^(E*d) by positivity))
  have hcancel : Real.sqrt (N : ℝ) ≤ K₀ / ρ^(E*d) := by
    apply le_of_mul_le_mul_right _ hSqrt
    rw [← pow_two, Real.sq_sqrt hNR.le]
    convert hUpper' using 1
    dsimp only [K₀]
    ring
  calc
    (N : ℝ) = (Real.sqrt (N : ℝ))^2 := (Real.sq_sqrt hNR.le).symm
    _ ≤ (K₀ / ρ^(E*d))^2 := pow_le_pow_left₀ hSqrt.le hcancel _
    _ = _ := by
      rw [div_pow, ← pow_mul, Real.rpow_neg hρ.le, Real.rpow_natCast, div_eq_mul_inv]
      congr 2
      ring


set_option maxHeartbeats 1000000 in
/-- Uniform numerical choices after collecting differentiated inverse
witnesses. The alternative is small (M), while the second conclusion has
the fixed power (q^{b₀}), the required block length and a quantitative
phase correlation. -/
private theorem weighted_phase_of_difference_witnesses_using
    (C : ℝ) (hC : 1 ≤ C) {N M q d e E b₀ : ℕ}
    (hN : 0 < N) (hM : 0 < M) (hq : 0 < q)
    (he : 0 < e) (hed : e ≤ d) (hMd : (M : ℝ)^d ≤ N)
    (ρ A a β b : ℝ) (hρ : 0 < ρ) (hρ₁ : ρ < 1)
    (hA : 0 < A) (ha : 0 < a) (hβ : 0 < β) (hb : 0 < b)
    (hE : β + (b₀ : ℝ) + b ≤ (E : ℝ))
    (G : Finset ℤ) (hG : G.Nonempty) (f : ℤ → ℂ)
    (hfS : SupportedOn (spatialInterval C N) f) (hf : ∀ x, ‖f x‖ ≤ 1)
    (hW : (∀ h ∈ G, ∃ (q' b' : ℕ), 0 < q' ∧ b' ≤ b₀ ∧
      (q' : ℝ) ≤ A * ρ^(-β) ∧ ∃ φ : ℤ → ℂ, (∀ x, ‖φ x‖ ≤ 1) ∧
      a * ρ^b * (N : ℝ) ≤ ‖∑ x ∈ spatialInterval C N,
        spatialMultiplicativeDifference f h x * φ x‖ ∧
      ∀ x t : ℤ, ‖φ (x + (q' : ℤ) * (q : ℤ)^b' * t) - φ x‖ ≤
        A * ((q : ℝ)/ρ)^β * (M : ℝ)^(-(e : ℝ)) * |(t : ℝ)|) ∨
      (∀ h ∈ G, ∃ φ : ℤ → ℂ, (∀ x, ‖φ x‖ ≤ 1) ∧
        a * ρ^b * (N : ℝ) ≤ ‖∑ x ∈ spatialInterval C N,
          spatialMultiplicativeDifference f h x * φ x‖ ∧
        ∀ x t : ℤ, ‖φ (x + ((q^b₀ : ℕ) : ℤ) * t) - φ x‖ ≤
          A * ((q : ℝ)/ρ)^β * (M : ℝ)^(-(e : ℝ)) * (q : ℝ)^b₀ * |(t : ℝ)|)) :
    let a₀ := min 1 (a / (2 * (2*C+2) * A))
    let u := (q : ℝ) / ρ
    (M : ℝ) ≤ (2 / a₀) * u^E ∨
    ∃ (V : ℕ) (s γ : (ℤ × ℤ) → ℝ),
      0 < V ∧ (a₀ / 2) * (M : ℝ)^e / u^E ≤ V ∧
      V ≤ M^e ∧ q^b₀ * V ≤ N ∧
      (G.card : ℝ) * (a * ρ^b)^2 ≤
        (4 * (A + 1)^4 * ρ^(-(4*β)) * (2*C+1) * (2*C+2)) *
          ‖∑ x ∈ spatialInterval C N, f x * localBlockPhase (q^b₀) V s γ x‖ := by
  let a₀ := min 1 (a / (2 * (2*C+2) * A))
  let u := (q : ℝ) / ρ
  let z := a₀ * (M : ℝ)^e / u^E
  let L := q^b₀
  let Q := ⌈A * ρ^(-β)⌉₊
  let D := A * u^β * (M : ℝ)^(-(e : ℝ)) * u^(b₀ : ℝ)
  let R := a * ρ^b * (N : ℝ)
  let X := spatialInterval C N
  have ha₀ : 0 < a₀ := lt_min one_pos (by positivity)
  have ha₀one : a₀ ≤ 1 := min_le_left _ _
  have ha₀err : a₀ ≤ a / (2 * (2*C+2) * A) := min_le_right _ _
  have hM₁ : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hq₁ : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hu : 0 < u := by positivity
  have huq : (q : ℝ) ≤ u := by
    dsimp [u]
    exact le_div_self (Nat.cast_nonneg _) hρ hρ₁.le
  have hu₁ : 1 ≤ u := hq₁.trans huq
  have hwE : b₀ ≤ E := by
    have : (b₀ : ℝ) ≤ E := by linarith
    exact_mod_cast this
  have hMp : (M : ℝ)^e ≤ N := (pow_le_pow_right₀ hM₁ hed).trans hMd
  have hL : 0 < L := pow_pos hq _
  have hrPow : 0 < ρ^(-β) := Real.rpow_pos_of_pos hρ _
  have hQ : 0 < Q := Nat.ceil_pos.mpr (mul_pos hA hrPow)
  change (M : ℝ) ≤ (2 / a₀) * u^E ∨ _
  by_cases hz : z < 2
  · left
    refine (le_self_pow₀ hM₁ he.ne').trans ?_
    have hh : z ≤ 2 := hz.le
    change a₀ * (M : ℝ)^e / u^E ≤ 2 at hh
    have hh' := (div_le_iff₀ (pow_pos hu _)).mp hh
    apply le_of_mul_le_mul_left _ ha₀
    convert hh' using 1
    field_simp
  · right
    let V := ⌊z⌋₊
    have hBig : 2 ≤ z := le_of_not_gt hz
    have hVhalf : z / 2 ≤ (V : ℝ) := by
      have h := Nat.lt_floor_add_one z
      change z < (V : ℝ) + 1 at h
      linarith
    have hV : 0 < V := by
      exact_mod_cast (show (0 : ℝ) < (V : ℝ) by linarith)
    have hVmax : (V : ℝ) ≤ z := Nat.floor_le (by positivity)
    have hzMax : z ≤ (M : ℝ)^e := by
      change a₀ * (M : ℝ)^e / u^E ≤ (M : ℝ)^e
      exact (div_le_self (by positivity) (one_le_pow₀ hu₁)).trans
        (mul_le_of_le_one_left (by positivity) ha₀one)
    have hVM : V ≤ M^e := by exact_mod_cast hVmax.trans hzMax
    have hLE : (L : ℝ) ≤ u^E := by
      dsimp [L]
      simpa only [Nat.cast_pow] using
        (pow_le_pow_left₀ (Nat.cast_nonneg q) huq b₀).trans (pow_le_pow_right₀ hu₁ hwE)
    have hLVreal : (L : ℝ) * (V : ℝ) ≤ N := by
      calc
        _ ≤ u^E * z := mul_le_mul hLE hVmax (Nat.cast_nonneg _) (by positivity)
        _ = a₀ * (M : ℝ)^e := by
          dsimp only [z]
          field_simp
        _ ≤ (M : ℝ)^e := mul_le_of_le_one_left (by positivity) ha₀one
        _ ≤ N := hMp
    have hLV : L * V ≤ N := by exact_mod_cast hLVreal
    have hLoss : D * (V : ℝ) ≤ A * a₀ * ρ^b := by
      have hExp : β + (b₀ : ℝ) - E ≤ -b := by linarith
      have hInv : u^(-b) ≤ ρ^b := by
        rw [Real.rpow_neg hu.le, ← Real.inv_rpow hu.le]
        exact Real.rpow_le_rpow (inv_nonneg.mpr hu.le)
          (by dsimp [u]; rw [inv_div]; exact div_le_self hρ.le hq₁) hb.le
      calc
        _ ≤ D * z := mul_le_mul_of_nonneg_left hVmax (by positivity)
        _ = A * a₀ * u^(β + (b₀ : ℝ) - E) := by
          dsimp only [D,z]
          rw [Real.rpow_neg (Nat.cast_nonneg M), Real.rpow_natCast, Real.rpow_sub hu,
            Real.rpow_add hu, Real.rpow_natCast]
          field_simp
          ring
        _ ≤ A * a₀ * u^(-b) := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hu₁ hExp) (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_left hInv (by positivity)
    have hCard := occupiedLocalBlocks_spatial_card_mul_le C N L V (by linarith) hL hV hLV
    have hXCard := spatialInterval_real_card_le C N (by linarith) hN
    have hErr : ((occupiedLocalBlocks X L V).card : ℝ) * V * (D * (V : ℝ)) ≤ R / 2 := by
      have haFinal := (le_div_iff₀ (show 0 < 2 * (2 * C + 2) * A by positivity)).mp ha₀err
      calc
        _ ≤ ((2*C+2) * (N : ℝ)) * (A * a₀ * ρ^b) :=
          mul_le_mul hCard hLoss (by positivity) (by positivity)
        _ = (a₀ * (2 * (2*C+2) * A)) * ((N : ℝ) * ρ^b / 2) := by ring
        _ ≤ a * ((N : ℝ) * ρ^b / 2) := mul_le_mul_of_nonneg_right haFinal (by positivity)
        _ = R / 2 := by dsimp [R]; ring
    have hCrl : ∃ s γ, (G.card : ℝ) * R^2 ≤
        4 * (Q : ℝ)^4 * (X.card : ℝ) * ((occupiedLocalBlocks X L V).card : ℝ) * V *
          ‖∑ x ∈ X, f x * localBlockPhase L V s γ x‖ := by
      rcases hW with hW | hW
      · have hW' : ∀ h ∈ G, ∃ q' : ℕ, 0 < q' ∧ q' ≤ Q ∧ ∃ φ : ℤ → ℂ,
            (∀ x, ‖φ x‖ ≤ 1) ∧
            (∀ x t : ℤ, ‖φ (x + (q' : ℤ) * (L : ℤ) * t) - φ x‖ ≤ D * |(t : ℝ)|) ∧
            R ≤ ‖∑ x ∈ X, spatialMultiplicativeDifference f h x * φ x‖ := by
          intro h hh
          obtain ⟨q',b',hq',hb',hQ',φ,hφ,hCorr,hLip⟩ := hW h hh
          refine ⟨q', hq', (by exact_mod_cast hQ'.trans (Nat.le_ceil _)), φ, hφ, ?_, hCorr⟩
          intro x t
          refine (promote_modular_lipschitz φ hb'
            (A * u^β * (M : ℝ)^(-(e : ℝ))) hLip x t).trans ?_
          apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [Real.rpow_natCast]
          exact (pow_le_pow_left₀ (Nat.cast_nonneg q) huq _).trans
            (pow_le_pow_right₀ hu₁ (Nat.sub_le _ _))
        exact exists_localBlockPhase_of_modular_correlations X G hG f hfS hf
          hL hV hQ D R (by positivity) (by positivity) hErr hW'
      · have hLbound : (q : ℝ)^b₀ ≤ u^(b₀ : ℝ) := by
          simpa only [Real.rpow_natCast] using pow_le_pow_left₀ (Nat.cast_nonneg _) huq b₀
        obtain ⟨s, γ, hCrl⟩ := exists_localBlockPhase_of_fixed_step_correlations X G hG
          f hfS hf hL hV D R (by positivity) (by positivity) hErr (fun h hh => by
            obtain ⟨φ, hφ, hCorr, hLip⟩ := hW h hh
            refine ⟨φ, hφ, fun x t => (hLip x t).trans ?_, hCorr⟩
            apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
            exact mul_le_mul_of_nonneg_left hLbound (by positivity))
        refine ⟨s, γ, hCrl.trans ?_⟩
        have hQfour : (1 : ℝ) ≤ (Q : ℝ)^4 :=
          one_le_pow₀ (by exact_mod_cast hQ)
        calc
          _ = 4 * 1 * (X.card : ℝ) * ((occupiedLocalBlocks X L V).card : ℝ) * V *
              ‖∑ x ∈ X, f x * localBlockPhase L V s γ x‖ := by ring
          _ ≤ _ := by gcongr
    obtain ⟨s,γ,hCrl⟩ := hCrl
    refine ⟨V,s,γ,hV,?_,hVM,hLV,?_⟩
    · convert hVhalf using 1
      dsimp only [z]
      ring
    have hρNeg : 1 ≤ ρ^(-β) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hρ hρ₁.le (by linarith)
    have hQUpper : (Q : ℝ) ≤ (A+1)*ρ^(-β) := by
      have hh := Nat.ceil_lt_add_one (show 0 ≤ A * ρ^(-β) by positivity)
      have hn : (Q : ℝ) < A * ρ^(-β) + 1 := hh
      linarith
    have hpQ : (Q : ℝ)^4 ≤ (A+1)^4 * ρ^(-(4*β)) := by
      calc
        _ ≤ ((A+1) * ρ^(-β))^4 := pow_le_pow_left₀ (Nat.cast_nonneg _) hQUpper _
        _ = _ := by rw [mul_pow, ← Real.rpow_natCast (x := ρ^(-β)), ← Real.rpow_mul hρ.le]; ring
    let p := ‖∑ x ∈ X, f x * localBlockPhase L V s γ x‖
    change (G.card : ℝ) * (a * ρ^b)^2 ≤ _ * p
    have hNpos : 0 < (N : ℝ)^2 := by positivity
    apply le_of_mul_le_mul_right _ hNpos
    calc
      _ = (G.card : ℝ) * R^2 := by dsimp [R]; ring
      _ ≤ 4 * (Q : ℝ)^4 * (X.card : ℝ) * ((occupiedLocalBlocks X L V).card : ℝ) * V * p := hCrl
      _ = (4 * (Q : ℝ)^4) * ((X.card : ℝ) * (((occupiedLocalBlocks X L V).card : ℝ) * V)) * p := by ring
      _ ≤ (4 * ((A+1)^4 * ρ^(-(4*β)))) *
          (((2*C+1) * (N : ℝ)) * ((2*C+2) * (N : ℝ))) * p := by gcongr
      _ = _ := by ring


theorem weighted_phase_of_difference_witnesses
    (C : ℝ) (hC : 1 ≤ C) {N M q d e E b₀ : ℕ}
    (hN : 0 < N) (hM : 0 < M) (hq : 0 < q)
    (he : 0 < e) (hed : e ≤ d) (hMd : (M : ℝ)^d ≤ N)
    (ρ A a β b : ℝ) (hρ : 0 < ρ) (hρ₁ : ρ < 1)
    (hA : 0 < A) (ha : 0 < a) (hβ : 0 < β) (hb : 0 < b)
    (hE : β + (b₀ : ℝ) + b ≤ (E : ℝ))
    (G : Finset ℤ) (hG : G.Nonempty) (f : ℤ → ℂ)
    (hfS : SupportedOn (spatialInterval C N) f) (hf : ∀ x, ‖f x‖ ≤ 1)
    (hW : ∀ h ∈ G, ∃ (q' b' : ℕ), 0 < q' ∧ b' ≤ b₀ ∧
      (q' : ℝ) ≤ A * ρ^(-β) ∧ ∃ φ : ℤ → ℂ, (∀ x, ‖φ x‖ ≤ 1) ∧
      a * ρ^b * (N : ℝ) ≤ ‖∑ x ∈ spatialInterval C N,
        spatialMultiplicativeDifference f h x * φ x‖ ∧
      ∀ x t : ℤ, ‖φ (x + (q' : ℤ) * (q : ℤ)^b' * t) - φ x‖ ≤
        A * ((q : ℝ)/ρ)^β * (M : ℝ)^(-(e : ℝ)) * |(t : ℝ)|) :
    let a₀ := min 1 (a / (2 * (2*C+2) * A))
    let u := (q : ℝ) / ρ
    (M : ℝ) ≤ (2 / a₀) * u^E ∨
    ∃ (V : ℕ) (s γ : (ℤ × ℤ) → ℝ),
      0 < V ∧ (a₀ / 2) * (M : ℝ)^e / u^E ≤ V ∧
      V ≤ M^e ∧ q^b₀ * V ≤ N ∧
      (G.card : ℝ) * (a * ρ^b)^2 ≤
        (4 * (A + 1)^4 * ρ^(-(4*β)) * (2*C+1) * (2*C+2)) *
          ‖∑ x ∈ spatialInterval C N, f x * localBlockPhase (q^b₀) V s γ x‖ := by
  exact weighted_phase_of_difference_witnesses_using C hC hN hM hq he hed hMd ρ A a β b
    hρ hρ₁ hA ha hβ hb hE G hG f hfS hf (Or.inl hW)


/-- The quantitative conclusion of manuscript Lemma 5.1 with a specified
exponent (B₀) for its common modulus (q^B₀). -/
def WeightedLocalInverseEstimateOn (H : ℕ → ℝ → Prop) (C : ℝ) (d ℓ B₀ : ℕ)
    (K₀ D₀ c₁ D₁ c₂ D₂ : ℝ) : Prop :=
  ∀ (N q : ℕ), 3 ≤ N → 0 < q →
    (q : ℝ) ≤ Real.exp ((Real.log (N : ℝ))^(1 / 10 : ℝ)) →
    let M := parameterLength N q d
    0 < M →
    ∀ P : Fin (ℓ + 1) → Polynomial ℤ, FixedPolynomialFamily P →
    (P (Fin.last ℓ)).natDegree = d →
    (∀ i, i ≠ 0 → HasCoefficients C q (P i)) →
    ∀ (v : ℤ → ℂ) (f : Fin (ℓ + 1) → ℤ → ℂ),
    OneBoundedOn (positiveInterval M) v →
    (∀ i, OneBoundedOn (spatialInterval C N) (f i)) →
    (∀ i, SupportedOn (spatialInterval C N) (f i)) →
    ∀ δ : ℝ, 0 < δ → δ < 1/2 →
    δ ≤ ‖countingForm N M (spatialInterval C N) P v f‖ → H q δ →
    (N : ℝ) ≤ K₀ * δ^(-D₀) ∨
      ∀ i, i ≠ 0 → ∃ (V : ℕ) (s γ : (ℤ × ℤ) → ℝ),
        0 < V ∧ c₁ * (M : ℝ)^((P i).natDegree) * ((q : ℝ) / δ)^(-D₁) ≤ V ∧
        V ≤ M^((P i).natDegree) ∧ q^B₀ * V ≤ N ∧
        c₂ * δ^D₂ * (N : ℝ) ≤
          ‖∑ x ∈ spatialInterval C N, f i x * localBlockPhase (q^B₀) V s γ x‖

def WeightedLocalInverseEstimate (C : ℝ) (d ℓ B₀ : ℕ)
    (K₀ D₀ c₁ D₁ c₂ D₂ : ℝ) : Prop :=
  ∀ (N q : ℕ), 3 ≤ N → 0 < q →
    (q : ℝ) ≤ Real.exp ((Real.log (N : ℝ))^(1 / 10 : ℝ)) →
    let M := parameterLength N q d
    0 < M →
    ∀ P : Fin (ℓ + 1) → Polynomial ℤ, FixedPolynomialFamily P →
    (P (Fin.last ℓ)).natDegree = d →
    (∀ i, i ≠ 0 → HasCoefficients C q (P i)) →
    ∀ (v : ℤ → ℂ) (f : Fin (ℓ + 1) → ℤ → ℂ),
    OneBoundedOn (positiveInterval M) v →
    (∀ i, OneBoundedOn (spatialInterval C N) (f i)) →
    (∀ i, SupportedOn (spatialInterval C N) (f i)) →
    ∀ δ : ℝ, 0 < δ → δ < 1/2 →
    δ ≤ ‖countingForm N M (spatialInterval C N) P v f‖ →
    (N : ℝ) ≤ K₀ * δ^(-D₀) ∨
      ∀ i, i ≠ 0 → ∃ (V : ℕ) (s γ : (ℤ × ℤ) → ℝ),
        0 < V ∧ c₁ * (M : ℝ)^((P i).natDegree) * ((q : ℝ) / δ)^(-D₁) ≤ V ∧
        V ≤ M^((P i).natDegree) ∧ q^B₀ * V ≤ N ∧
        c₂ * δ^D₂ * (N : ℝ) ≤
          ‖∑ x ∈ spatialInterval C N, f i x * localBlockPhase (q^B₀) V s γ x‖

set_option maxHeartbeats 1500000 in
private theorem weighted_local_inverse_of_difference_witnesses
    {C : ℝ} (hC : 1 ≤ C) {d ℓ b₀ B₀ : ℕ} (hd : 0 < d) (hb₀ : b₀ ≤ B₀)
    {a A b B : ℝ} (ha : 0 < a) (hA : 0 < A) (hb : 0 < b) (hB : 0 < B)
    (hDiff : DifferenceWitnessEstimate C d ℓ b₀ a A b B)
    (Hguard : ℕ → ℝ → Prop) (fixedStep : Bool)
    (hFixedStep : fixedStep = true → ∀ (q : ℕ) (δ : ℝ), 0 < δ → δ < 1/2 →
      Hguard q δ → ∀ (r b' : ℕ), 0 < r → b' ≤ b₀ →
      (r : ℝ) ≤ A * (δ^2 / (2*(6*C)^2))^(-B) → r*q^b' ∣ q^B₀) :
    ∃ K₀ D₀ c₁ D₁ c₂ D₂ : ℝ,
      0 < K₀ ∧ 0 < D₀ ∧ 0 < c₁ ∧ 0 < D₁ ∧ 0 < c₂ ∧ 0 < D₂ ∧
      WeightedLocalInverseEstimateOn Hguard C d ℓ B₀ K₀ D₀ c₁ D₁ c₂ D₂ := by
  let E := ⌈B + (B₀ : ℝ) + b⌉₊
  let a₀ := min 1 (a / (2 * (2*C+2) * A))
  let U := max A (2 / a₀)
  let H := 2*(6*C)^2
  let S := (2 * E * d : ℕ)
  let F := 2*b + 4*B
  let T := 4 * (A+1)^4 * (2*C+1) * (2*C+2)
  have hE : B + (B₀ : ℝ) + b ≤ E := Nat.le_ceil _
  have hEpos : 0 < E := by
    exact_mod_cast (show 0 < (E : ℝ) by linarith)
  have hBUp : B ≤ E := by linarith
  have ha₀ : 0 < a₀ := lt_min one_pos (by positivity)
  have hU : 0 < U := hA.trans_le (le_max_left _ _)
  have hH : 0 < H := by positivity
  have hH₁ : 1 ≤ H := by
    dsimp [H]
    have hcS : (6 : ℝ)^2 ≤ (6*C)^2 := pow_le_pow_left₀ (by norm_num) (by linarith) _
    linarith
  have hF : 0 < F := by positivity
  have hT : 0 < T := by positivity
  obtain ⟨K,hK,hSpace⟩ := space_bound_of_small_parameterLength d E U hU hd
  let c₁ := (a₀ / 2) / H^E
  let c₂ := a^2 / ((2*(6*C)) * T * H^F)
  refine ⟨K * H^(S : ℝ), 2 * (S : ℝ), c₁, ((2*E : ℕ) : ℝ), c₂, 2+2*F,
    by positivity, by positivity, by positivity, by positivity, by positivity, by positivity, ?_⟩
  intro N q hN hq hqBound M hM P hP hTop hCoeff v f hv hf hfS δ hδ hδ' hc hGuard
  have hNpos : 0 < N := by omega
  let ρ := δ^2/H
  let u := (q : ℝ)/ρ
  have hρ : 0 < ρ := by positivity
  have hρ₁ : ρ < 1 := by
    apply (div_lt_iff₀ hH).mpr
    dsimp [ρ] at *
    rw [one_mul]
    have hδsq : δ^2 < 1 := by nlinarith
    exact hδsq.trans_le hH₁
  have hδ₁ : δ < 1 := by linarith
  have hρpow (s : ℝ) : ρ^s = δ^(2*s) / H^s := by
    dsimp only [ρ]
    rw [Real.div_rpow (sq_nonneg _) hH.le, ← Real.rpow_natCast (x := δ),
      ← Real.rpow_mul hδ.le, Nat.cast_two]
  by_cases hSmall : (M : ℝ) ≤ U * u^E
  · left
    have hs := hSpace N q ρ hNpos hq hρ hqBound hM hSmall
    change (N : ℝ) ≤ K * ρ^(-(S : ℝ)) at hs
    rw [hρpow, Real.rpow_neg hH.le, div_inv_eq_mul, mul_left_comm, mul_comm (δ ^ _)] at hs
    rw [show -(2 * (S : ℝ)) = -(S : ℝ)*2 by ring]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hs
  have hu : 0 < u := by positivity
  have hu₁ : 1 ≤ u := by
    apply (le_div_iff₀ hρ).mpr
    rw [one_mul]
    exact hρ₁.le.trans (by exact_mod_cast hq)
  have hNoDiffSmall : ¬((M : ℝ) ≤ A*u^B) := by
    intro h
    apply hSmall
    refine h.trans (mul_le_mul (le_max_left _ _) ?_
      (by positivity) hU.le)
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hu₁ hBUp
  have hRHS := hDiff N M q hNpos hq hM (by rfl) P hP hTop hCoeff v f hv hf hfS δ hδ hδ' hc
  obtain ⟨G,hGs,hGcard,hWitness⟩ := hRHS.resolve_left hNoDiffSmall
  have hG : G.Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast (lt_of_lt_of_le (by positivity : 0 < δ^2 * (N : ℝ) / (2*(6*C))) hGcard)
  right
  intro i hi
  let e := (P i).natDegree
  have he : 0 < e := (hCoeff i hi).2.2.1
  have hed : e ≤ d := hTop ▸ hP.2.2.2.monotone (Fin.le_last i)
  have hMd : (M : ℝ)^d ≤ N := (parameterLength_bounds hNpos hq hd hM).1
  have hFull : ∀ x, ‖f i x‖ ≤ 1 := oneBounded_of_supported (hf i) (hfS i)
  have hW := weighted_phase_of_difference_witnesses_using C hC hNpos hM hq he hed hMd ρ A a B b
    hρ hρ₁ hA ha hB hb hE G hG (f i) (hfS i) hFull (by
      by_cases hFix : fixedStep = true
      · right
        intro h hh
        obtain ⟨q',b',hq',_,hb',hq'_bound,hAll⟩ := hWitness h hh
        obtain ⟨φ,hφ,hCorr,hLip⟩ := hAll i hi
        have hdiv := hFixedStep hFix q δ hδ hδ' hGuard q' b' hq' hb' hq'_bound
        refine ⟨φ,hφ,hCorr,?_⟩
        have h := modular_lipschitz_of_dvd φ (mul_pos hq' (pow_pos hq b')) hdiv
          (D := A * u^B * (M : ℝ)^(-(e : ℝ))) (by positivity)
          (fun x t => by simpa only [Nat.cast_mul,Nat.cast_pow] using hLip x t)
        simpa only [Nat.cast_pow] using h
      · left
        intro h hh
        obtain ⟨q',b',hq',_,hb',hq'_bound,hAll⟩ := hWitness h hh
        exact ⟨q',b',hq',hb'.trans hb₀,hq'_bound,hAll i hi⟩)
  obtain ⟨V,s,γ,hV,hVlo,hVhi,hLV,hCorr⟩ := hW.resolve_left (fun h =>
    hSmall (h.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))))
  refine ⟨V,s,γ,hV,?_,hVhi,hLV,?_⟩
  · refine le_trans ?_ hVlo
    have hq₁ : 1 ≤ (q : ℝ) := by exact_mod_cast hq
    have huBound : u ≤ H * (((q : ℝ) / δ)^2) := by
      dsimp only [u,ρ]
      rw [div_div_eq_mul_div, div_pow, ← mul_div_assoc H]
      apply div_le_div_of_nonneg_right _ (sq_nonneg δ)
      have hh := le_self_pow₀ hq₁ (show (2 : ℕ) ≠ 0 by decide)
      nlinarith only [mul_le_mul_of_nonneg_left hh hH.le]
    have huPow : u^E ≤ H^E * ((q : ℝ) / δ)^(2*E) := by
      simpa only [mul_pow, ← pow_mul] using pow_le_pow_left₀ hu.le huBound E
    calc
      _ = (a₀ / 2) * (M : ℝ)^e / (H^E * ((q : ℝ) / δ)^(2*E)) := by
        dsimp only [c₁]
        rw [Real.rpow_neg (by positivity : 0 ≤ (q : ℝ)/δ), Real.rpow_natCast]
        field_simp
        simp only [e]
        ring
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) huPow
  · let p := ‖∑ x ∈ spatialInterval C N, f i x * localBlockPhase (q^B₀) V s γ x‖
    have hCorr' : (G.card : ℝ) * (a * ρ^b)^2 ≤ T * ρ^(-(4*B)) * p :=
      hCorr.trans_eq (by dsimp only [T,p]; ring)
    have hPoly : δ^2 * (N : ℝ) / (2*(6*C)) * (a^2 * ρ^F) ≤ T * p := by
      have hm := mul_le_mul_of_nonneg_right hCorr' (Real.rpow_nonneg hρ.le (4*B))
      have hRight : T * ρ^(-(4*B)) * p * ρ^(4*B) = T * p := by
        rw [mul_comm (T * _) p, mul_assoc p, mul_assoc T, ← Real.rpow_add hρ,
          neg_add_cancel, Real.rpow_zero, mul_one, mul_comm p]
      rw [hRight] at hm
      calc
        _ ≤ (G.card : ℝ) * (a^2 * ρ^F) :=
          mul_le_mul_of_nonneg_right hGcard (by positivity)
        _ = (G.card : ℝ) * (a * ρ^b)^2 * ρ^(4*B) := by
          dsimp only [F]
          rw [Real.rpow_add hρ, mul_pow, ← Real.rpow_natCast (x := ρ^b), ← Real.rpow_mul hρ.le,
            Nat.cast_two]
          ring_nf
        _ ≤ _ := hm
    apply le_of_mul_le_mul_left _ hT
    calc
      _ = δ^2 * (N : ℝ) / (2*(6*C)) * (a^2 * ρ^F) := by
        dsimp only [c₂]
        rw [hρpow, Real.rpow_add hδ, Real.rpow_two]
        field_simp
        ring
      _ ≤ _ := hPoly


set_option maxHeartbeats 1500000 in
/-- The weighted local inverse deduction preserves the bound on the power
of the base modulus in the unweighted KMTT theorem. -/
theorem weighted_local_inverse_of_inverse_with_exponent
    {C : ℝ} (hC : 1 ≤ C) {d ℓ B₀ : ℕ} (hd : 0 < d)
    (hInv : KMTTLocalInverseWithExponent C d ℓ B₀) :
    ∃ K₀ D₀ c₁ D₁ c₂ D₂ : ℝ,
      0 < K₀ ∧ 0 < D₀ ∧ 0 < c₁ ∧ 0 < D₁ ∧ 0 < c₂ ∧ 0 < D₂ ∧
      WeightedLocalInverseEstimate C d ℓ B₀ K₀ D₀ c₁ D₁ c₂ D₂ := by
  obtain ⟨a,A,b,B,ha,hA,hb,hB,hDiff⟩ := difference_witnesses_of_inverse_with_exponent hC hInv
  obtain ⟨K₀,D₀,c₁,D₁,c₂,D₂,hK₀,hD₀,hc₁,hD₁,hc₂,hD₂,hEstimate⟩ :=
    weighted_local_inverse_of_difference_witnesses hC hd le_rfl ha hA hb hB hDiff
      (fun _ _ => True) false (by simp)
  refine ⟨K₀,D₀,c₁,D₁,c₂,D₂,hK₀,hD₀,hc₁,hD₁,hc₂,hD₂,?_⟩
  intro N q hN hq hBound M hM P hP hDeg hCoeff v f hv hf hfs δ hδ hδ' hc
  exact hEstimate N q hN hq hBound hM P hP hDeg hCoeff v f hv hf hfs δ hδ hδ' hc trivial

/-- On an lcm-divisible modulus KMTT's auxiliary steps fit in a single
further power of the base modulus. The derivative correlation then uses
frequency zero on every atom. -/
theorem weighted_local_inverse_on_lcm_moduli
    {C : ℝ} (hC : 1 ≤ C) {d ℓ b₀ : ℕ} (hd : 0 < d)
    (hInv : KMTTLocalInverseWithExponent C d ℓ b₀) :
    ∃ (U E K₀ D₀ c₁ D₁ c₂ D₂ : ℝ),
      0 < U ∧ 0 < E ∧ 0 < K₀ ∧ 0 < D₀ ∧ 0 < c₁ ∧ 0 < D₁ ∧ 0 < c₂ ∧ 0 < D₂ ∧
      WeightedLocalInverseEstimateOn
        (fun q δ => initialModulus ⌈U*δ^(-E)⌉₊ ∣ q) C d ℓ (b₀+1) K₀ D₀ c₁ D₁ c₂ D₂ := by
  obtain ⟨a,A,b,B,ha,hA,hb,hB,hDiff⟩ := difference_witnesses_of_inverse_with_exponent hC hInv
  let H := 2*(6*C)^2
  have hH : 0 < H := by dsimp [H]; positivity
  let U := A*H^B
  have hU : 0 < U := by dsimp [U]; positivity
  obtain ⟨K₀,D₀,c₁,D₁,c₂,D₂,hK₀,hD₀,hc₁,hD₁,hc₂,hD₂,hEst⟩ :=
    weighted_local_inverse_of_difference_witnesses hC hd (Nat.le_succ b₀) ha hA hb hB hDiff
      (fun q δ => initialModulus ⌈U*δ^(-(2*B))⌉₊ ∣ q) true (by
        intro _ q δ hδ _ hDiv r b' hr hb' hrBound
        have hPower : A*(δ^2/H)^(-B) = U*δ^(-(2*B)) := by
          rw [Real.div_rpow (sq_nonneg δ) hH.le, ← Real.rpow_natCast (x := δ),
            ← Real.rpow_mul hδ.le, Nat.cast_two, Real.rpow_neg hH.le, div_inv_eq_mul]
          dsimp [U]
          ring
        have hrBound' : (r : ℝ) ≤ U*δ^(-(2*B)) := hrBound.trans_eq hPower
        exact auxiliary_step_dvd_fixed_power hr
          (by exact_mod_cast hrBound'.trans (Nat.le_ceil _)) hDiv hb')
  exact ⟨U,2*B,K₀,D₀,c₁,D₁,c₂,D₂,hU,by positivity,hK₀,hD₀,hc₁,hD₁,hc₂,hD₂,hEst⟩

/-- Lemma 5.1 with constants chosen after fixing (C), (d) and the
family length, as sufficient to deduce the local generalized von Neumann
estimate. -/
theorem weighted_local_inverse_of_kmtt (hInv : KMTTLocalInverse)
    {C : ℝ} (hC : 1 ≤ C) {d ℓ : ℕ} (hd : 0 < d) (hℓ : 0 < ℓ) :
    ∃ (K₀ D₀ c₁ D₁ c₂ D₂ : ℝ) (B₀ : ℕ),
      0 < K₀ ∧ 0 < D₀ ∧ 0 < c₁ ∧ 0 < D₁ ∧ 0 < c₂ ∧ 0 < D₂ ∧
      WeightedLocalInverseEstimate C d ℓ B₀ K₀ D₀ c₁ D₁ c₂ D₂ := by
  obtain ⟨a, A, b, B, B₀, ha, hA, hb, hB, hInv⟩ := hInv C d ℓ hC hℓ
  obtain ⟨K₀, D₀, c₁, D₁, c₂, D₂, hK₀, hD₀, hc₁, hD₁, hc₂, hD₂, hEst⟩ :=
    weighted_local_inverse_of_inverse_with_exponent hC hd
      (show KMTTLocalInverseWithExponent C d ℓ B₀ from ⟨a, A, b, B, ha, hA, hb, hB, hInv⟩)
  exact ⟨K₀, D₀, c₁, D₁, c₂, D₂, B₀, hK₀, hD₀, hc₁, hD₁, hc₂, hD₂, hEst⟩

/-- Lemma 5.1 with the printed degree-only bound on the exponent of the
common modulus. The remaining quantitative constants may depend on (C),
(d) and the family length. -/
theorem weighted_local_inverse_of_kmtt_degree_uniform
    (hInv : KMTTLocalInverseDegreeUniform) {d : ℕ} (hd : 0 < d) :
    ∃ B₀ : ℕ, ∀ (C : ℝ) (ℓ : ℕ), 1 ≤ C → 0 < ℓ →
      ∃ K₀ D₀ c₁ D₁ c₂ D₂ : ℝ,
        0 < K₀ ∧ 0 < D₀ ∧ 0 < c₁ ∧ 0 < D₁ ∧ 0 < c₂ ∧ 0 < D₂ ∧
        WeightedLocalInverseEstimate C d ℓ B₀ K₀ D₀ c₁ D₁ c₂ D₂ := by
  obtain ⟨B₀, hInv⟩ := hInv d
  exact ⟨B₀, fun C ℓ hC hℓ =>
    weighted_local_inverse_of_inverse_with_exponent hC hd (hInv C ℓ hC hℓ)⟩

end NilBohr
