import NilBohr.BareSelectorComparison
import NilBohr.Sieve

/-! Arithmetic, scale bounds and exact progression reindexing for Proposition 6.2. -/

open Filter
open scoped BigOperators Topology

namespace NilBohr

/-- An interval with at least one complete period meets every residue class. -/
theorem localProgression_nonempty_of_step_le_card {l r u : ℤ} {m : ℕ}
    (hm : 0 < m) (hI : m ≤ (Finset.Icc l r).card) :
    (localProgression l r u m).Nonempty := by
  have hmZ : (0 : ℤ) < m := by exact_mod_cast hm
  have hCard : (m : ℤ) ≤ r + 1 - l := by
    rw [Int.card_Icc] at hI
    have hpos : 0 ≤ r + 1 - l := by
      by_contra! hh
      have hzero := Int.toNat_of_nonpos hh.le
      omega
    exact_mod_cast (Int.toNat_of_nonneg hpos ▸ (show (m : ℤ) ≤ ((r+1-l).toNat : ℤ)
      by exact_mod_cast hI) : (m : ℤ) ≤ r+1-l)
  let y := l + (u-l) % (m : ℤ)
  refine ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_,?_⟩,?_⟩⟩
  · exact le_add_of_nonneg_right (Int.emod_nonneg _ hmZ.ne')
  · have h := Int.emod_lt_of_pos (u-l) hmZ
    dsimp [y]
    omega
  · apply Int.modEq_iff_dvd.mpr
    refine ⟨(u-l) / (m : ℤ), ?_⟩
    have h := Int.emod_add_ediv (u-l) (m : ℤ)
    dsimp [y]
    omega

/-- Under the map `y ↦ q*y+1`, an interval/residue intersection becomes the
full interval/residue intersection between the transformed endpoints. -/
theorem primeProgression_affine_image (l r u : ℤ) {m q : ℕ} (hq : 0 < q) :
    (localProgression l r u m).image (fun y => (q : ℤ)*y+1) =
      localProgression ((q : ℤ)*l+1) ((q : ℤ)*r+1) ((q : ℤ)*u+1) (q*m) := by
  have hqZ : (0 : ℤ) < q := by exact_mod_cast hq
  ext z
  simp only [Finset.mem_image, localProgression, Finset.mem_filter, Finset.mem_Icc,
    Int.modEq_iff_dvd, Nat.cast_mul]
  constructor
  · rintro ⟨y,⟨⟨hy₁,hy₂⟩,⟨k,hk⟩⟩,rfl⟩
    refine ⟨⟨?_,?_⟩,k,?_⟩
    · exact add_le_add_right (mul_le_mul_of_nonneg_left hy₁ hqZ.le) _
    · exact add_le_add_right (mul_le_mul_of_nonneg_left hy₂ hqZ.le) _
    · linear_combination (q : ℤ)*hk
  · rintro ⟨⟨hz₁,hz₂⟩,⟨k,hk⟩⟩
    let y := u - (m : ℤ)*k
    have hz : (q : ℤ)*y+1 = z := by dsimp [y]; linear_combination hk
    have hy₁ : l ≤ y := by
      apply le_of_mul_le_mul_left _ hqZ
      omega
    have hy₂ : y ≤ r := by
      apply le_of_mul_le_mul_left _ hqZ
      omega
    refine ⟨y,⟨⟨hy₁,hy₂⟩,k,?_⟩,hz⟩
    dsimp [y]
    ring

/-- The residue in the shifted-prime image is reduced. -/
theorem primeProgression_residue_coprime (q b : ℕ) (u : ℤ) :
    IsCoprime ((q : ℤ)*u+1) (((q^(b+1) : ℕ)) : ℤ) := by
  have h : IsCoprime ((q : ℤ)*u+1) (q : ℤ) :=
    IsCoprime.mul_add_left_left isCoprime_one_left u
  simpa only [Nat.cast_pow] using (h.pow_right (n := b+1))

/-- Under the shifted-prime change of variables, a polynomial phase on `P`
becomes a polynomial phase of the same degree bound on the image of `P`. -/
theorem primeProgression_phaseNorm_le_affine_image {s q : ℕ} (hs : 0 < s) (hq : 0 < q)
    (P : Finset ℤ) (g : ℤ → ℂ) :
    phaseNorm s P (fun y => g ((q : ℤ)*y+1)) ≤
      phaseNorm s (P.image (fun y => (q : ℤ)*y+1)) g := by
  classical
  let f : ℤ → ℤ := fun y => (q : ℤ)*y+1
  let L : Polynomial ℝ := Polynomial.C ((q : ℝ)⁻¹) * (Polynomial.X - 1)
  have hqZ : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hinj : Function.Injective f := fun a b h => mul_left_cancel₀ hqZ (add_right_cancel h)
  have hL : L.natDegree ≤ 1 := by
    apply (Polynomial.natDegree_C_mul_le _ _).trans
    rw [sub_eq_add_neg]
    exact Polynomial.natDegree_add_le_of_degree_le (by simp) (by simp)
  have hEval (t : ℤ) : L.eval (f t : ℝ) = (t : ℝ) := by
    simp only [L, f, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_one, Int.cast_add, Int.cast_mul, Int.cast_one, Int.cast_natCast, add_sub_cancel_right]
    rw [← mul_assoc, inv_mul_cancel₀ hqR, one_mul]
  unfold phaseNorm
  refine csSup_le ⟨‖phaseAverage P _ 0‖,0,by simpa using hs,rfl⟩ ?_
  rintro c ⟨φ,hφ,rfl⟩
  have hφL : (φ.comp L).natDegree < s :=
    (Polynomial.natDegree_comp_le.trans (by simpa using Nat.mul_le_mul_left φ.natDegree hL)).trans_lt hφ
  have heq : phaseAverage P (fun t => g (f t)) φ = phaseAverage (P.image f) g (φ.comp L) := by
    simp only [phaseAverage, Finset.card_image_of_injective _ hinj,
      Finset.sum_image (fun _ _ _ _ h => hinj h)]
    congr 1
    apply Finset.sum_congr rfl
    intro t _
    simp only [Polynomial.eval_comp,hEval]
  change ‖phaseAverage P (fun t => g (f t)) φ‖ ≤ _
  rw [heq]
  exact norm_phaseAverage_le_phaseNorm g (φ.comp L) hφL

set_option maxHeartbeats 1000000 in
/-- The exact finite reparametrization at the start of Proposition 6.2,
including the transformed residue, count and ambient interval. -/
theorem primeProgression_as_affine {l r u : ℤ} {M q b : ℕ} (hq : 0 < q)
    (hI : Finset.Icc l r ⊆ positiveInterval M)
    (hP : (localProgression l r u (q^b)).Nonempty) :
    let P := localProgression l r u (q^b)
    let P' := P.image (fun y => (q : ℤ)*y+1)
    P'.card = P.card ∧ P' ⊆ positiveInterval (q*M+1) ∧
      P' = localProgression ((q : ℤ)*l+1) ((q : ℤ)*r+1) ((q : ℤ)*u+1) (q^(b+1)) ∧
      IsCoprime ((q : ℤ)*u+1) (((q^(b+1) : ℕ)) : ℤ) ∧
      ((Finset.Icc l r).card : ℝ) / ((q^b : ℕ) : ℝ) - 1 < (P'.card : ℝ) ∧
      ∃ a : ℤ, P' = (positiveInterval P'.card).image
        (fun t => a + (((q^(b+1) : ℕ)) : ℤ)*t) := by
  let P := localProgression l r u (q^b)
  let P' := P.image (fun y => (q : ℤ)*y+1)
  have hqZ : (0 : ℤ) < q := by exact_mod_cast hq
  have hinj : Function.Injective (fun y : ℤ => (q : ℤ)*y+1) :=
    fun i j h => mul_left_cancel₀ hqZ.ne' (add_right_cancel h)
  have hc : P'.card = P.card := Finset.card_image_of_injective _ hinj
  have hSub : P' ⊆ positiveInterval (q*M+1) := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hy₁, hy₂⟩ := Finset.mem_Icc.mp (hI (Finset.mem_filter.mp hy).1)
    refine Finset.mem_Icc.mpr ⟨?_,?_⟩
    · nlinarith only [mul_nonneg hqZ.le (show 0 ≤ y by omega)]
    · push_cast
      exact add_le_add_right (mul_le_mul_of_nonneg_left hy₂ hqZ.le) _
  have hResidue := primeProgression_affine_image l r u (m := q^b) hq
  rw [← pow_succ'] at hResidue
  obtain ⟨a,hLen,hRepr⟩ := localProgression_as_affine (pow_pos hq b) hP
  change P = _ at hRepr
  refine ⟨hc,hSub,hResidue,primeProgression_residue_coprime q b u,?_,(q : ℤ)*a+1,?_⟩
  · change _ < (P'.card : ℝ)
    rw [hc]
    exact hLen
  change P' = (positiveInterval P'.card).image _
  rw [hc]
  change Finset.image _ P = _
  conv_lhs => rw [hRepr, Finset.image_image]
  congr 1
  ext t
  simp only [Function.comp_apply, Nat.cast_pow]
  rw [pow_succ]
  ring

/-- A sieve divisor coprime to the original step selects a full progression
in its index coordinate. Its cardinality loses at most one from division. -/
theorem primeProgression_divisible_as_affine
    (a : ℤ) {s H D X : ℕ} (hs : 0 < s) (hD : 0 < D) (hDH : D ≤ H)
    (hCo : s.Coprime D)
    (hP : ((positiveInterval H).image (fun t => a + (s : ℤ)*t)) ⊆ positiveInterval X) :
    let P := (positiveInterval H).image (fun t => a + (s : ℤ)*t)
    let P₀ := P.filter (fun m => (D : ℤ) ∣ m)
    (H : ℝ)/(D : ℝ)-1 < (P₀.card : ℝ) ∧
      ∃ z : ℤ, P₀ = (positiveInterval P₀.card).image (fun t => z+((s*D : ℕ) : ℤ)*t) := by
  let P := (positiveInterval H).image (fun t => a + (s : ℤ)*t)
  let P₀ := P.filter (fun m => (D : ℤ) ∣ m)
  have hstart : 1 ≤ a + (s : ℤ) := by
    have hFirst : (1 : ℤ) ∈ positiveInterval H :=
      Finset.mem_Icc.mpr ⟨le_rfl, by exact_mod_cast hD.trans_le hDH⟩
    have hVal : a + (s : ℤ) * (1 : ℤ) ∈ positiveInterval X :=
      hP (Finset.mem_image_of_mem _ hFirst)
    simpa only [mul_one] using (Finset.mem_Icc.mp hVal).1
  obtain ⟨v,hv⟩ := exists_modEq_of_dvd_affine (a + (s : ℤ)).toNat s D hD hCo
  let w : ℤ := (v : ℤ)+1
  have hFilter (t : ℤ) (ht : t ∈ positiveInterval H) :
      (D : ℤ) ∣ a+(s : ℤ)*t ↔ t ≡ w [ZMOD (D : ℤ)] := by
    have ht₁ : 1 ≤ t := (Finset.mem_Icc.mp ht).1
    let n := (t-1).toNat
    have hn : (n : ℤ) = t-1 := Int.toNat_of_nonneg (by omega)
    have he : a+(s : ℤ)*t = ((((a+(s : ℤ)).toNat + s*n : ℕ)) : ℤ) := by
      push_cast
      rw [Int.toNat_of_nonneg (by omega : 0 ≤ a+(s : ℤ)),hn]
      ring
    rw [he, Int.natCast_dvd_natCast, hv n, ← Int.natCast_modEq_iff, hn]
    constructor
    · intro h
      simpa only [w, sub_add_cancel] using h.add_right 1
    · intro h
      simpa only [w, add_sub_cancel_right] using h.sub_right 1
  let I := localProgression 1 (H : ℤ) w D
  have hId : P₀ = I.image (fun t => a+(s : ℤ)*t) := by
    ext m
    constructor
    · intro hm
      obtain ⟨hm,hDiv⟩ := Finset.mem_filter.mp hm
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hm
      exact Finset.mem_image.mpr ⟨t, Finset.mem_filter.mpr ⟨ht,(hFilter t ht).mp hDiv⟩, rfl⟩
    · intro hm
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hm
      obtain ⟨ht,hv⟩ := Finset.mem_filter.mp ht
      exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ ht,(hFilter t ht).mpr hv⟩
  have hsZ : (s : ℤ) ≠ 0 := by exact_mod_cast hs.ne'
  have hinj : Function.Injective (fun t : ℤ => a+(s : ℤ)*t) :=
    fun t u h => mul_left_cancel₀ hsZ (add_left_cancel h)
  have hc : P₀.card = I.card := by rw [hId,Finset.card_image_of_injective _ hinj]
  have hI : I.Nonempty := localProgression_nonempty_of_step_le_card hD
    (by simpa [positiveInterval, Int.card_Icc] using hDH)
  obtain ⟨c,hLen,hRepr⟩ := localProgression_as_affine hD hI
  refine ⟨?_,a+(s : ℤ)*c,?_⟩
  · change _ < (P₀.card : ℝ)
    rw [hc, ← card_positiveInterval H]
    exact hLen
  · change P₀ = Finset.image _ (positiveInterval P₀.card)
    change I = Finset.image _ (positiveInterval I.card) at hRepr
    rw [hc,hId]
    conv_lhs => rw [hRepr,Finset.image_image]
    congr 1
    ext t
    simp only [Function.comp_apply,Nat.cast_mul]
    ring

theorem prime_not_dvd_sieve_step {q b D r : ℕ} (hq : 0 < q)
    (hr : r.Prime) (hqr : q < r) (hD : ¬ r ∣ D) : ¬ r ∣ q^(b+1)*D := by
  rw [hr.dvd_mul]
  exact not_or_intro (fun h => (not_le_of_gt hqr)
    (Nat.le_of_dvd hq (hr.dvd_of_dvd_pow h))) hD

/-- Moving from a zero-based natural index to the ambient positive prime
variable preserves the exact sieve divisor count. -/
theorem primeProgression_abs_card_dvd_sub_le_one
    (a : ℤ) {s H D X : ℕ} (hs : 0 < s) (hD : 0 < D) (hCo : s.Coprime D)
    (hP : ((positiveInterval H).image (fun t => a + (s : ℤ)*t)) ⊆ positiveInterval X) :
    let P := (positiveInterval H).image (fun t => a+(s : ℤ)*t)
    |(((P.filter (fun m => (D : ℤ) ∣ m)).card : ℝ) - (H : ℝ)/(D : ℝ))| ≤ 1 := by
  rcases H.eq_zero_or_pos with rfl | hH
  · simp [positiveInterval]
  let offset := (a+(s : ℤ)).toNat
  let P := (positiveInterval H).image (fun t => a+(s : ℤ)*t)
  let good := (Finset.range H).filter (fun t => D ∣ offset + s*t)
  let affine : ℕ → ℤ := fun n => a + (s : ℤ)*((n : ℤ)+1)
  have ha : 1 ≤ a+(s : ℤ) := by
    have hFirst : (1 : ℤ) ∈ positiveInterval H :=
      Finset.mem_Icc.mpr ⟨le_rfl, by exact_mod_cast hH⟩
    have hVal : a+(s : ℤ)*(1 : ℤ) ∈ positiveInterval X :=
      hP (Finset.mem_image_of_mem _ hFirst)
    simpa only [mul_one] using (Finset.mem_Icc.mp hVal).1
  have hMap (n : ℕ) : affine n = ((offset+s*n : ℕ) : ℤ) := by
    dsimp [affine,offset]
    push_cast
    rw [Int.toNat_of_nonneg (show 0 ≤ a+(s : ℤ) by omega)]
    ring
  have heq : P.filter (fun m => (D : ℤ) ∣ m) = good.image affine := by
    ext m
    constructor
    · intro hm
      obtain ⟨hm,hDiv⟩ := Finset.mem_filter.mp hm
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hm
      obtain ⟨ht₁,ht₂⟩ := Finset.mem_Icc.mp ht
      let n := (t-1).toNat
      have hn : (n : ℤ)+1 = t := by dsimp [n]; omega
      have heval : affine n = a+(s : ℤ)*t := by dsimp only [affine]; rw [hn]
      have hnDiv := hDiv
      rw [← heval, hMap, Int.natCast_dvd_natCast] at hnDiv
      refine Finset.mem_image.mpr ⟨n,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_,hnDiv⟩,heval⟩
      omega
    · intro hm
      obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hm
      obtain ⟨hn,hnDiv⟩ := Finset.mem_filter.mp hn
      have ht : (n : ℤ)+1 ∈ positiveInterval H := by
        refine Finset.mem_Icc.mpr ⟨by omega,?_⟩
        have := Finset.mem_range.mp hn
        omega
      refine Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ ht,?_⟩
      rw [hMap, Int.natCast_dvd_natCast]
      exact hnDiv
  have hsZ : (s : ℤ) ≠ 0 := by exact_mod_cast hs.ne'
  have hinj : Function.Injective affine := by
    intro x y h
    dsimp only [affine] at h
    have he := add_right_cancel (mul_left_cancel₀ hsZ (add_left_cancel h))
    exact_mod_cast he
  change |(((P.filter (fun m => (D : ℤ) ∣ m)).card : ℝ) - (H : ℝ)/(D : ℝ))| ≤ 1
  rw [heq,Finset.card_image_of_injective _ hinj]
  exact abs_card_dvd_affine_sub_le_one offset s D H hD hCo

/-- Uniform scale preparation for the prime variable in Proposition 6.2. -/
theorem primeProgression_log_scales {d : ℕ} (hd : 0 < d) (B K L : ℝ)
    (hB : 0 ≤ B) (hK : 0 ≤ K) (hL : 0 ≤ L) :
    ∀ᶠ N : ℕ in atTop, ∀ {q b : ℕ}, 0 < q → (q : ℝ) ≤ (Real.log N)^L →
      (b : ℝ) ≤ B →
      let t := Real.log (N : ℝ)
      let M := parameterLength N q d
      let X := q*M+1
      1 ≤ t ∧ 0 < M ∧ t/(2*(d : ℝ)) ≤ Real.log (M : ℝ) ∧
      t/(2*(d : ℝ)) ≤ Real.log (X : ℝ) ∧ Real.log (X : ℝ) ≤ 2*t ∧
      2 ≤ (M : ℝ) * t^(-K) / ((q^b : ℕ) : ℝ) ∧
      ((q^(b+1) : ℕ) : ℝ) ≤ (X : ℝ)^(1/20000 : ℝ) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hd₁ : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hN : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hF := hN.eventually (eventually_linearSqrt_lt (show (0 : ℝ) < 1/2 by norm_num)
    (2*((d-1 : ℕ) : ℝ)*L) ((d : ℝ)*Real.log 2))
  have hQ := hN.eventually (eventually_linearSqrt_lt (show (0 : ℝ) < 1 by norm_num)
    (2*L) (Real.log 2))
  have hS := hN.eventually (eventually_linearSqrt_lt (show 0 < 1/(40000*(d : ℝ)) by positivity)
    (2*(B+1)*L) 0)
  have hW := hN.eventually (eventually_linearSqrt_lt (show 0 < 1/(2*(d : ℝ)) by positivity)
    (2*(K+B*L)) (Real.log 2))
  filter_upwards [eventually_ge_atTop (1 : ℕ), hN.eventually_ge_atTop 1, hF, hQ, hS, hW]
    with N hN₁ hT hF hQ hS hW
  intro q b hq hqBound hb
  let t := Real.log (N : ℝ)
  let M := parameterLength N q d
  let X := q*M+1
  have ht : 0 < t := zero_lt_one.trans_le hT
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN₁
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hq₁ : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hlogq : Real.log q ≤ L * Real.log t := by
    have h := Real.log_le_log hqR hqBound
    rwa [Real.log_rpow ht] at h
  have hlogsqrt := log_le_two_sqrt_density ht
  have hlogqS : Real.log q ≤ 2*L*Real.sqrt t := by
    calc
      _ ≤ _ := hlogq
      _ ≤ L * (2*Real.sqrt t) := mul_le_mul_of_nonneg_left hlogsqrt hL
      _ = _ := by ring
  have hlogq₀ : 0 ≤ Real.log q := Real.log_nonneg hq₁
  have hfloor : ((d-1 : ℕ) : ℝ)*Real.log q + (d : ℝ)*Real.log 2 ≤ t/2 := by
    calc
      _ ≤ ((d-1 : ℕ) : ℝ)*(2*L*Real.sqrt t) + (d : ℝ)*Real.log 2 :=
        add_le_add_right (mul_le_mul_of_nonneg_left hlogqS (by positivity)) _
      _ ≤ _ := by change 2 * ↑(d-1) * L * Real.sqrt t + ↑d * Real.log 2 < 1/2*t at hF
                  linarith
  let R := ((N : ℝ) / (q : ℝ)^(d-1))^((d : ℝ)⁻¹)
  have hR := Real.rpow_pos_of_pos (div_pos hNR (pow_pos hqR (d-1))) ((d : ℝ)⁻¹)
  have hscale : 2 ≤ R := by
    apply (Real.log_le_log_iff (by norm_num) hR).mp
    dsimp only [R]
    rw [Real.log_rpow (div_pos hNR (pow_pos hqR _)), Real.log_div hNR.ne' (pow_pos hqR _).ne',
      Real.log_pow, ← div_eq_inv_mul]
    apply (le_div_iff₀ hdR).mpr
    change Real.log 2 * (d : ℝ) ≤ t - ↑(d-1) * Real.log q
    linarith
  have hMlog : t/(2*(d : ℝ)) ≤ Real.log (M : ℝ) := by
    have h := log_parameterLength_lower (show 0 < N by omega) hq hscale
    change (d : ℝ)⁻¹ * (t - ↑(d-1)*Real.log q) - Real.log 2 ≤ Real.log (M : ℝ) at h
    have hm : t/2 / (d : ℝ) + Real.log 2 ≤ (t-↑(d-1)*Real.log q)/(d : ℝ) := by
      apply (le_div_iff₀ hdR).mpr
      rw [add_mul, div_mul_cancel₀ _ hdR.ne']
      linarith
    rw [← div_eq_inv_mul] at h
    rw [← div_div]
    linarith
  have hMpos : 0 < M := by
    have hf : R < (M : ℝ)+1 := Nat.lt_floor_add_one R
    exact_mod_cast (show (0 : ℝ) < M by linarith)
  have hMR : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hM₁ : (1 : ℝ) ≤ M := by exact_mod_cast hMpos
  have hXlow : (M : ℝ) ≤ X := by
    change (M : ℝ) ≤ ((q*M+1 : ℕ) : ℝ)
    push_cast
    nlinarith only [mul_nonneg (sub_nonneg.mpr hq₁) hMR.le]
  have hXR : (0 : ℝ) < X := hMR.trans_le hXlow
  have hXlog := hMlog.trans (Real.log_le_log hMR hXlow)
  have hMle : (M : ℝ) ≤ N := calc
    _ ≤ (M : ℝ)^d := by simpa only [pow_one] using pow_le_pow_right₀ hM₁ hd
    _ ≤ (q : ℝ)^(d-1)*(M : ℝ)^d := le_mul_of_one_le_left (by positivity) (one_le_pow₀ hq₁)
    _ ≤ _ := parameterLength_power_le hq hd
  have hXupper : (X : ℝ) ≤ 2*(q : ℝ)*(M : ℝ) := by
    change ((q*M+1 : ℕ) : ℝ) ≤ 2*(q : ℝ)*(M : ℝ)
    push_cast
    have := mul_le_mul hq₁ hM₁ (show (0 : ℝ) ≤ 1 by norm_num) hqR.le
    nlinarith only [this]
  have hXlogUpper : Real.log (X : ℝ) ≤ 2*t := by
    have hh := Real.log_le_log hXR hXupper
    rw [Real.log_mul (mul_pos (by norm_num) hqR).ne' hMR.ne',
      Real.log_mul (by norm_num) hqR.ne'] at hh
    have hm := Real.log_le_log hMR hMle
    change 2 * L * Real.sqrt t + Real.log 2 < 1*t at hQ
    linarith
  have hWidth : 2 ≤ (M : ℝ)*t^(-K) / ((q^b : ℕ) : ℝ) := by
    push_cast
    apply (Real.log_le_log_iff (by norm_num) (by positivity)).mp
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul hMR.ne' (by positivity),
      Real.log_rpow ht, Real.log_pow]
    have hbl : (b : ℝ)*Real.log q ≤ B*L*Real.log t := calc
      _ ≤ B*Real.log q := mul_le_mul_of_nonneg_right hb hlogq₀
      _ ≤ B*(L*Real.log t) := mul_le_mul_of_nonneg_left hlogq hB
      _ = _ := by ring
    have htot := mul_le_mul_of_nonneg_left hlogsqrt (show 0 ≤ K+B*L by positivity)
    change 2*(K+B*L)*Real.sqrt t+Real.log 2 < 1/(2*(d : ℝ))*t at hW
    rw [div_mul_eq_mul_div,one_mul] at hW
    linarith
  have hStep : ((q^(b+1) : ℕ) : ℝ) ≤ (X : ℝ)^(1/20000 : ℝ) := by
    push_cast
    apply (Real.log_le_log_iff (pow_pos hqR _) (Real.rpow_pos_of_pos hXR _)).mp
    rw [Real.log_pow, Real.log_rpow hXR]
    push_cast
    have hh := mul_le_mul_of_nonneg_right (add_le_add_right hb 1) hlogq₀
    have hh' := mul_le_mul_of_nonneg_left hlogqS (show 0 ≤ B+1 by positivity)
    have hx := mul_le_mul_of_nonneg_left hXlog (show (0 : ℝ) ≤ 1/20000 by norm_num)
    have he : t/(40000*(d : ℝ)) = 1/20000 * (t/(2*(d : ℝ))) := by ring
    change 2*(B+1)*L*Real.sqrt t+0 < 1/(40000*(d : ℝ))*t at hS
    rw [div_mul_eq_mul_div,one_mul,he] at hS
    linarith
  exact ⟨hT,hMpos,hMlog,hXlog,hXlogUpper,hWidth,hStep⟩

set_option maxHeartbeats 1200000 in
/-- The shifted progression and every eligible progression in its sieve expansion
have the uniform sizes and step bounds used in Proposition 6.2. -/
theorem primeProgression_sieve_scales {d : ℕ} (hd : 0 < d) (B K L : ℝ)
    (hB : 0 ≤ B) (hK : 0 ≤ K) (hL : 0 ≤ L) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ N : ℕ in atTop, ∀ {q b : ℕ} {l r u : ℤ}, 0 < q →
        (q : ℝ) ≤ (Real.log N)^L → (b : ℝ) ≤ B →
        let M := parameterLength N q d
        let X := q*M+1
        Finset.Icc l r ⊆ positiveInterval M →
        (M : ℝ)*(Real.log N)^(-K) ≤ ((Finset.Icc l r).card : ℝ) →
        let P := localProgression l r u (q^b)
        let P' := P.image (fun y => (q : ℤ)*y+1)
        let T := K+(B+1)*L
        P'.card = P.card ∧ P' ⊆ positiveInterval X ∧
        (Real.log N)/(2*(d : ℝ)) ≤ Real.log (X : ℝ) ∧
        Real.log (X : ℝ) ≤ 2*Real.log N ∧
        c*(X : ℝ)*(Real.log (X : ℝ))^(-T) ≤ (P'.card : ℝ) ∧
        ∀ {D : ℕ}, 0 < D → (D : ℝ) ≤ (X : ℝ)^(1/20000 : ℝ) → (q^ (b+1)).Coprime D →
          let P₀ := P'.filter (fun m => (D : ℤ) ∣ m)
          ((q^(b+1)*D : ℕ) : ℝ) ≤ (X : ℝ)^(1/10000 : ℝ) ∧
          (X : ℝ)^(1/2 : ℝ) ≤ (P₀.card : ℝ) ∧
          ∃ z : ℤ, P₀ = (positiveInterval P₀.card).image
            (fun t => z + ((q^(b+1)*D : ℕ) : ℤ)*t) := by
  let T := K+(B+1)*L
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  let c := ((2*(d : ℝ))^T * 4)⁻¹
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c,hc,?_⟩
  have hNt : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall := hNt.eventually (eventually_linearSqrt_lt (show 0 < 1/(20*(d : ℝ)) by positivity)
    (2*T) (Real.log 8))
  filter_upwards [primeProgression_log_scales hd B K L hB hK hL, hsmall] with N hScale hsmall
  intro q b l r u hq hqBound hb
  let t := Real.log (N : ℝ)
  let M := parameterLength N q d
  let X := q*M+1
  change Finset.Icc l r ⊆ positiveInterval M → _
  intro hI hIcard
  let P := localProgression l r u (q^b)
  let P' := P.image (fun y => (q : ℤ)*y+1)
  obtain ⟨ht,hM,_,hXlogLow,hXlogUp,hWidth,hStep⟩ := hScale hq hqBound hb
  change t/(2*(d : ℝ)) ≤ Real.log (X : ℝ) at hXlogLow
  change 2 ≤ (M : ℝ)*t^(-K)/((q^b : ℕ) : ℝ) at hWidth
  change (M : ℝ)*t^(-K) ≤ ((Finset.Icc l r).card : ℝ) at hIcard
  have htpos : 0 < t := zero_lt_one.trans_le ht
  have hq₁ : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hM₁ : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hqR : (0 : ℝ) < q := zero_lt_one.trans_le hq₁
  have hX₁ : (1 : ℝ) ≤ X := by
    change (1 : ℝ) ≤ ((q*M+1 : ℕ) : ℝ)
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le (q*M))
  have hXR : (0 : ℝ) < X := zero_lt_one.trans_le hX₁
  have hV : (0 : ℝ) < ((q^b : ℕ) : ℝ) := by exact_mod_cast pow_pos hq b
  have hIperiod : q^b ≤ (Finset.Icc l r).card := by
    have hWidth' := (le_div_iff₀ hV).mp hWidth
    exact_mod_cast (show ((q^b : ℕ) : ℝ) ≤ ((Finset.Icc l r).card : ℝ) by linarith)
  have hP : P.Nonempty := localProgression_nonempty_of_step_le_card (pow_pos hq _) hIperiod
  obtain ⟨hCard,hSub,_,_,hCLow,a,hAP⟩ := primeProgression_as_affine hq hI hP
  change P'.card = P.card at hCard
  change P' ⊆ positiveInterval X at hSub
  change _ < (P'.card : ℝ) at hCLow
  change P' = _ at hAP
  have hqstep : ((q^(b+1) : ℕ) : ℝ) ≤ t^((B+1)*L) := by
    push_cast
    calc
      (q : ℝ)^(b+1) ≤ (t^L)^(b+1) := pow_le_pow_left₀ hqR.le hqBound _
      _ = t^(L*((b+1 : ℕ) : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul htpos.le]
      _ ≤ _ := by
        apply Real.rpow_le_rpow_of_exponent_le ht
        push_cast
        have hh := mul_le_mul_of_nonneg_left (add_le_add_right hb 1) hL
        linarith only [hh]
  have htLower : (X : ℝ)/(4*t^T) ≤ (P'.card : ℝ) := by
    have hRaw := (div_le_div_of_nonneg_right hIcard hV.le)
    have hX : (X : ℝ) ≤ 2*(q : ℝ)*(M : ℝ) := by
      change ((q*M+1 : ℕ) : ℝ) ≤ 2*(q : ℝ)*(M : ℝ)
      push_cast
      have := mul_le_mul hq₁ hM₁ (show (0 : ℝ) ≤ 1 by norm_num) hqR.le
      nlinarith only [this]
    have haux : (X : ℝ)/(4*t^T) ≤ ((M : ℝ)*t^(-K) / ((q^b : ℕ) : ℝ))/2 := by
      rw [show T = K+(B+1)*L by rfl, Real.rpow_add htpos, Real.rpow_neg htpos.le]
      have hposK := Real.rpow_pos_of_pos htpos K
      have hposL := Real.rpow_pos_of_pos htpos ((B+1)*L)
      have hstep : (q : ℝ) * ((q^b : ℕ) : ℝ) ≤ t^((B+1)*L) := by
        push_cast
        simpa only [pow_succ', Nat.cast_mul, Nat.cast_pow] using hqstep
      rw [div_div, ← div_eq_mul_inv, div_div]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      have hstep' := mul_le_mul_of_nonneg_left hstep (show 0 ≤ (M : ℝ) * t^K by positivity)
      have hX' := mul_le_mul_of_nonneg_right hX (show 0 ≤ t^K * (((q^b : ℕ) : ℝ) * 2) by positivity)
      calc
        _ ≤ _ := hX'
        _ = 4 * ((M : ℝ)*t^K*((q : ℝ)*((q^b : ℕ) : ℝ))) := by ring
        _ ≤ 4 * ((M : ℝ)*t^K*t^((B+1)*L)) := mul_le_mul_of_nonneg_left hstep' (by norm_num)
        _ = (M : ℝ) * (4 * (t^K*t^((B+1)*L))) := by ring
    linarith only [hRaw,hWidth,hCLow,haux]
  have hXlogPos : 0 < Real.log (X : ℝ) :=
    (div_pos htpos (by positivity : 0 < 2*(d : ℝ))).trans_le hXlogLow
  have hLogCard : c*(X : ℝ)*(Real.log (X : ℝ))^(-T) ≤ (P'.card : ℝ) := by
    have htl : t ≤ 2*(d : ℝ)*Real.log (X : ℝ) := (div_le_iff₀ (by positivity)).mp hXlogLow |>.trans_eq (by ring)
    have hPow := Real.rpow_le_rpow htpos.le htl hT
    rw [Real.mul_rpow (by positivity : 0 ≤ 2*(d : ℝ)) hXlogPos.le] at hPow
    calc
      _ = (X : ℝ) / (4 * ((2*(d : ℝ))^T * (Real.log (X : ℝ))^T)) := by
        change _⁻¹*(X : ℝ)*(Real.log (X : ℝ))^(-T) = _
        rw [Real.rpow_neg hXlogPos.le]
        have hD := Real.rpow_pos_of_pos (show 0 < 2*(d : ℝ) by positivity) T
        have hLog := Real.rpow_pos_of_pos hXlogPos T
        field_simp [hD.ne', hLog.ne']; ring; simp
      _ ≤ (X : ℝ)/(4*t^T) := div_le_div_of_nonneg_left hXR.le (by positivity)
        (mul_le_mul_of_nonneg_left hPow (by norm_num))
      _ ≤ _ := htLower
  have hLogSmall : 8*t^T ≤ (X : ℝ)^(1/10 : ℝ) := by
    apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
    rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos htpos _).ne', Real.log_rpow htpos,
      Real.log_rpow hXR]
    have h₁ := mul_le_mul_of_nonneg_left (log_le_two_sqrt_density htpos) hT
    have h₂ := mul_le_mul_of_nonneg_left hXlogLow (show (0 : ℝ) ≤ 1/10 by norm_num)
    change 2*T*Real.sqrt t+Real.log 8 < 1/(20*(d : ℝ))*t at hsmall
    have hEq : 1/(20*(d : ℝ))*t = (1/10)*(t/(2*(d : ℝ))) := by ring
    rw [hEq] at hsmall
    calc
      _ ≤ 2*T*Real.sqrt t + Real.log 8 := by
        convert add_le_add_left h₁ (Real.log 8) using 1
        ring
      _ ≤ _ := hsmall.le.trans h₂
  have hLargeCard : 2*(X : ℝ)^(9/10 : ℝ) ≤ (P'.card : ℝ) := calc
    _ = (X : ℝ) / ((X : ℝ)^(1/10 : ℝ)/2) := by
      have hPower : (X : ℝ)^(9/10 : ℝ) = (X : ℝ)/(X : ℝ)^(1/10 : ℝ) := by
        simpa only [Real.rpow_one, show (1 : ℝ) - 1/10 = 9/10 by norm_num] using
          (Real.rpow_sub hXR (1 : ℝ) (1/10 : ℝ))
      rw [hPower, div_div_eq_mul_div]
      ring
    _ ≤ (X : ℝ)/(4*t^T) := div_le_div_of_nonneg_left hXR.le (by positivity) (by linarith)
    _ ≤ _ := htLower
  change P'.card = P.card ∧ P' ⊆ positiveInterval X ∧ _
  refine ⟨hCard,hSub,hXlogLow,hXlogUp,hLogCard,?_⟩
  intro D hD hDupper hCo
  let P₀ := P'.filter (fun m => (D : ℤ) ∣ m)
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hPowDiv : (D : ℝ)*(X : ℝ)^(1/2 : ℝ) ≤ (X : ℝ)^(9/10 : ℝ) := calc
    _ ≤ (X : ℝ)^(1/20000 : ℝ)*(X : ℝ)^(1/2 : ℝ) :=
      mul_le_mul_of_nonneg_right hDupper (by positivity)
    _ = (X : ℝ)^(1/20000+1/2 : ℝ) := (Real.rpow_add hXR _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hX₁ (by norm_num)
  have hSqrtOne : 1 ≤ (X : ℝ)^(1/2 : ℝ) := Real.one_le_rpow hX₁ (by norm_num)
  have hDH : D ≤ P'.card := by
    exact_mod_cast (show (D : ℝ) ≤ (P'.card : ℝ) from
      (le_mul_of_one_le_right hDR.le hSqrtOne).trans (hPowDiv.trans (by linarith [hLargeCard])))
  have hs := pow_pos hq (b+1)
  have hAP' : P' = (positiveInterval P'.card).image (fun t => a+((q^(b+1) : ℕ) : ℤ)*t) := hAP
  have hadd := primeProgression_divisible_as_affine a hs hD hDH hCo (hAP' ▸ hSub)
  dsimp only at hadd
  rw [← hAP'] at hadd
  obtain ⟨hDP,z,hDP'⟩ := hadd
  change _ < (P₀.card : ℝ) at hDP
  have hMin : (X : ℝ)^(1/2 : ℝ) ≤ (P₀.card : ℝ) := by
    have hDouble : 2*(X : ℝ)^(1/2 : ℝ) ≤ (P'.card : ℝ)/(D : ℝ) := by
      apply (le_div_iff₀ hDR).mpr
      nlinarith only [hLargeCard,hPowDiv]
    linarith only [hDouble,hDP,hSqrtOne]
  have hTotalStep : ((q^(b+1)*D : ℕ) : ℝ) ≤ (X : ℝ)^(1/10000 : ℝ) := by
    rw [Nat.cast_mul]
    calc
      _ ≤ (X : ℝ)^(1/20000 : ℝ)*(X : ℝ)^(1/20000 : ℝ) :=
        mul_le_mul hStep hDupper hDR.le (by positivity)
      _ = _ := by rw [← Real.rpow_add hXR]; norm_num
  exact ⟨hTotalStep,hMin,z,hDP'⟩

end NilBohr
