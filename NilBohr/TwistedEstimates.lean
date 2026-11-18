import NilBohr.TwistedOrbit

/-! Uniform scales in the twisted Heisenberg estimate. -/

open Filter Polynomial Asymptotics

namespace NilBohr

private theorem eventually_log_rpow_le_rpow (b : ℝ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ X : ℝ in atTop, Real.log X ^ b ≤ X^c := by
  have h := (isLittleO_log_rpow_rpow_atTop b hc).bound (show 0 < (1 : ℝ) by norm_num)
  filter_upwards [h, eventually_ge_atTop (Real.exp 1)] with X hX hlarge
  have hX₀ : 0 < X := (Real.exp_pos 1).trans_le hlarge
  have hlog : 0 < Real.log X := zero_lt_one.trans_le ((Real.le_log_iff_exp_le hX₀).mpr hlarge)
  simpa only [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hlog _),
    abs_of_pos (Real.rpow_pos_of_pos hX₀ _), one_mul] using hX

/-- The asymptotic book-keeping for the proof of the twisted estimate.
The horizontal and scalar premises are the already proved dilated
estimates with a common denominator witness. -/
theorem twisted_heisenberg_log_saving_of_dilated
    (hGT : ProductHeisenbergObstruction) {r : ℕ → ℕ} {α β : ℝ}
    (hprime : ∀ j, (r j).Prime)
    (hrlarge : ∀ E B : ℝ, 0 < E → 0 < B →
      ∀ᶠ X : ℝ in atTop, ∀ j : ℕ, X^(1/100 : ℝ) < (r (j+1) : ℝ) →
        B*Real.log X ^ E < (r j : ℝ))
    (hhorizontal : ∀ A L D : ℝ, 0 < L → ∀ᶠ X : ℝ in atTop,
      ∀ j : ℕ, (r j : ℝ) ≤ X^(1/100 : ℝ) → X^(1/100 : ℝ) < (r (j+1) : ℝ) →
      ∀ (v s K : ℕ) (k l : ℤ), 0 < v → (v : ℝ) ≤ X^(1/5000 : ℝ) → ¬ r j ∣ v →
      0 < s → (s : ℝ) ≤ Real.log X ^ D → X^(1/3 : ℝ) ≤ (K : ℝ) →
      0 < max |(k : ℝ)| |(l : ℝ)| → max |(k : ℝ)| |(l : ℝ)| ≤ Real.log X ^ L →
      Real.log X ^ A < (K : ℝ) * torusNorm ((v : ℝ)*(k*α+l*β)/s))
    (hscalar : ∀ B E : ℝ, 0 < B → ∀ᶠ X : ℝ in atTop,
      ∀ j : ℕ, (r j : ℝ) ≤ X^(1/100 : ℝ) → X^(1/100 : ℝ) < (r (j+1) : ℝ) →
      ∀ (a : ℤ) (v s K : ℕ), 0 < v → (v : ℝ) ≤ X^(1/5000 : ℝ) → ¬ r j ∣ v →
      0 < s → (s : ℝ) ≤ Real.log X ^ E → X^(1/3 : ℝ) ≤ (K : ℝ) →
      ∀ (Φ : HeisenbergPoint → ℂ) (U : ℝ), HeisenbergLipschitzNormLE Φ U →
      ‖heisenbergOrbitAverage α β a v s K Φ - heisenbergChartMean Φ‖ ≤
        Real.log X ^ (-B) * U)
    {d : ℕ} (hd : 0 < d) {A L : ℝ} (hA : 0 < A) (hL : 0 < L) :
    ∀ᶠ X : ℝ in atTop, ∀ j : ℕ, (r j : ℝ) ≤ X^(1/100 : ℝ) → X^(1/100 : ℝ) < (r (j+1) : ℝ) →
      ∀ (a : ℤ) (v K : ℕ), 0 < v → (v : ℝ) ≤ X^(1/10000 : ℝ) → ¬ r j ∣ v →
      X^(1/2 : ℝ) ≤ (K : ℝ) →
      ∀ Φ : HeisenbergPoint → ℂ, HeisenbergLipschitzNormLE Φ (Real.log X ^ L) →
      (∀ x y, (∫ z in (0 : ℝ)..1, Φ (x,y,z)) = 0) →
      ∀ p : Polynomial ℝ, p.natDegree ≤ d →
      ‖heisenbergTwistedSum Φ α β a v K (fun t => p.eval (t : ℝ)) / (K : ℂ)‖ ≤
        2*Real.log X ^ (-A) := by
  obtain ⟨C,D,C₁,hC,hD,hC₁,hmain⟩ := norm_heisenbergTwistedAverage_le_of_product_obstruction hGT d hd
  obtain ⟨C₂,hC₂,hcover⟩ := heisenbergCoverTest_lipschitz
  let g := A+L+1
  let E := g*D+1
  let B := A+E+2
  let L' := L+2*E+1
  have hg : 0 < g := by dsimp [g]; positivity
  have hE : 0 < E := by dsimp [E]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hL' : 0 < L' := by dsimp [L']; positivity
  have hscalarB := hscalar (B+L') E (add_pos hB hL')
  have hRlarge := Real.tendsto_log_atTop.eventually (eventually_ge_atTop
    (max C (max (d.factorial : ℝ) (max (1+C₁*d) (3+2*C₂)))))
  have hδlarge := ((tendsto_rpow_atTop hg).comp Real.tendsto_log_atTop).eventually
    (eventually_ge_atTop (3 : ℝ))
  have hrbound := hrlarge E (d.factorial : ℝ) hE (by exact_mod_cast Nat.factorial_pos d)
  have hvsmall := eventually_log_rpow_le_rpow (E+1) (by norm_num : (0 : ℝ) < 1/10000)
  have hshort := eventually_log_rpow_le_rpow (A+L+2*E+3) (by norm_num : (0 : ℝ) < 1/6)
  filter_upwards [eventually_ge_atTop (Real.exp 1), hRlarge, hδlarge, hrbound,
    hvsmall, hshort, hscalarB, hhorizontal E E 0 hE] with X hX hRlarge hδlarge hrbound
      hvsmall hshort hSer hHor
  intro j hj₀ hj₁ a v K hv hvX hvr hK Φ hΦ hmean p hp
  let R := Real.log X
  let U := R^L
  let δ := R^(-g)
  let ε := R^(-B)
  let τ := X^(1/3 : ℝ)
  have hXpos : 0 < X := (Real.exp_pos 1).trans_le hX
  have hXone : 1 < X := (Real.one_lt_exp_iff.mpr zero_lt_one).trans_le hX
  have hRone : 1 ≤ R := (Real.le_log_iff_exp_le hXpos).mpr hX
  have hRpos : 0 < R := zero_lt_one.trans_le hRone
  have hU : 0 < U := Real.rpow_pos_of_pos hRpos L
  have hRE : 1 ≤ R^E := Real.one_le_rpow hRone hE.le
  have hRE2 : 1 ≤ R^(2*E) := Real.one_le_rpow hRone (by positivity)
  have hRe : R^E ≤ R^(2*E) := Real.rpow_le_rpow_of_exponent_le hRone (by linarith)
  have hKone : 1 < K := by
    exact_mod_cast (Real.one_lt_rpow hXone (by norm_num : (0:ℝ) < 1/2)).trans_le hK
  have hδpos : 0 < δ := Real.rpow_pos_of_pos hRpos _
  have hδlt : δ < 1/2 := by
    dsimp only [δ]
    rw [Real.rpow_neg hRpos.le, ← one_div]
    exact (div_lt_iff₀ (Real.rpow_pos_of_pos hRpos _)).mpr (by
      change (3 : ℝ) ≤ R^g at hδlarge
      linarith)
  let H := C*δ^(-D)
  have hHpos : 0 ≤ H := by dsimp [H]; positivity
  have hH : H ≤ R^E := by
    have h : δ^(-D) = R^(g*D) := by
      dsimp only [δ]
      rw [← Real.rpow_mul hRpos.le, neg_mul_neg]
    change C*δ^(-D) ≤ R^E
    rw [h]
    have hCR : C ≤ R := (le_max_left _ _).trans hRlarge
    calc
      _ ≤ R*R^(g*D) := mul_le_mul_of_nonneg_right hCR (Real.rpow_nonneg hRpos.le _)
      _ = R^E := by
        simpa only [E, Real.rpow_one, mul_comm] using (Real.rpow_add hRpos (g*D) 1).symm
  have hKlo : τ ≤ (K : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hXone.le (by norm_num : (1/3 : ℝ) ≤ 1/2)).trans hK
  have hvbig : (v : ℝ) ≤ X^(1/5000 : ℝ) :=
    hvX.trans (Real.rpow_le_rpow_of_exponent_le hXone.le (by norm_num))
  have hboundHoriz (k l : ℤ) (hkl : k ≠ 0 ∨ l ≠ 0)
      (hsize : max |(k : ℝ)| |(l : ℝ)| ≤ H) :
      H < (K : ℝ)*torusNorm ((v : ℝ)*(k*α+l*β)) := by
    have hkpos : 0 < max |(k : ℝ)| |(l : ℝ)| := by
      rcases hkl with hk | hl
      · exact (abs_pos.mpr (by exact_mod_cast hk)).trans_le (le_max_left _ _)
      · exact (abs_pos.mpr (by exact_mod_cast hl)).trans_le (le_max_right _ _)
    have hy := hHor j hj₀ hj₁ v 1 K k l hv hvbig hvr (by decide) (by simp)
      hKlo hkpos (hsize.trans hH)
    exact hH.trans_lt (by simpa only [Nat.cast_one, div_one] using hy)
  have hLmax : H*(d.factorial : ℝ) ≤ R^(E+1) := by
    have hdR : (d.factorial : ℝ) ≤ R :=
      ((le_max_left _ _).trans (le_max_right _ _)).trans hRlarge
    calc
      _ ≤ R^E*R := mul_le_mul hH hdR (by positivity) (by positivity)
      _ = R^(E+1) := by
        simpa only [Real.rpow_one] using (Real.rpow_add hRpos E 1).symm
  have hlong (k l m : ℤ) (hm : m ≠ 0)
      (hkm : max |(k : ℝ)| (max |(l : ℝ)| |(m : ℝ)|) ≤ H)
      (i : ℕ) (_hi : i < m.natAbs*d.factorial) (J : ℕ) (hJ : τ ≤ (J : ℝ)) :
      ‖heisenbergOrbitAverage α β
        (a+(v : ℤ)*((i : ℤ)+1-(m.natAbs*d.factorial : ℕ)))
        (v*(m.natAbs*d.factorial)) m.natAbs J (heisenbergCoverTest Φ k l m)‖ ≤ ε := by
    let s := m.natAbs
    let M := s*d.factorial
    have hs : 0 < s := Int.natAbs_pos.mpr hm
    have hM : 0 < M := Nat.mul_pos hs (Nat.factorial_pos _)
    have hsH : (s : ℝ) ≤ H := by
      have h := (le_max_right |(l : ℝ)| |(m : ℝ)|).trans ((le_max_right _ _).trans hkm)
      simpa only [s, ← Int.cast_abs, ← Int.natCast_natAbs] using h
    have hsR : (s : ℝ) ≤ R^E := hsH.trans hH
    have hkR : |(k : ℝ)| ≤ R^E := (le_max_left _ _).trans (hkm.trans hH)
    have hlR : |(l : ℝ)| ≤ R^E :=
      (le_max_left _ _).trans ((le_max_right _ _).trans (hkm.trans hH))
    have hMR : (M : ℝ) ≤ H*(d.factorial : ℝ) := by
      simpa only [M, Nat.cast_mul] using mul_le_mul_of_nonneg_right hsH (by positivity : 0 ≤ (d.factorial : ℝ))
    have hMr : M < r j := by
      exact_mod_cast (hMR.trans ((mul_le_mul_of_nonneg_right hH (by positivity)).trans_eq (mul_comm _ _))).trans_lt
        (hrbound j hj₁)
    have hvs : ((v*M : ℕ) : ℝ) ≤ X^(1/5000 : ℝ) := by
      rw [Nat.cast_mul]
      have hMR' : (M : ℝ) ≤ X^(1/10000 : ℝ) := hMR.trans (hLmax.trans hvsmall)
      simpa only [← Real.rpow_add hXpos, show (1/10000 : ℝ)+1/10000=1/5000 by norm_num] using
        mul_le_mul hvX hMR' (by positivity) (by positivity)
    have hvd : ¬ r j ∣ v*M := by
      intro hh
      rcases (hprime j).dvd_mul.mp hh with h | h
      · exact hvr h
      · exact (not_lt_of_ge (Nat.le_of_dvd hM h)) hMr
    let U' := U*(1+(s : ℝ)^2+C₂*(|(k : ℝ)|+|(l : ℝ)|))+1
    have hU' : U' ≤ R^L' := by
      have hs2 : (s : ℝ)^2 ≤ R^(2*E) := by
        rw [mul_comm (2 : ℝ), Real.rpow_mul hRpos.le, Real.rpow_two]
        exact pow_le_pow_left₀ (by positivity : 0 ≤ (s : ℝ)) hsR 2
      have hshape : 1+(s : ℝ)^2+C₂*(|(k : ℝ)|+|(l : ℝ)|) ≤ (2+2*C₂)*R^(2*E) := by
        have hw := mul_le_mul_of_nonneg_left
          (add_le_add (hkR.trans hRe) (hlR.trans hRe)) hC₂
        linarith
      have hRU : U*R^(2*E) = R^(L+2*E) := (Real.rpow_add hRpos _ _).symm
      have h1 : 1 ≤ R^(L+2*E) := Real.one_le_rpow hRone (by positivity)
      have hcR : 3+2*C₂ ≤ R :=
        ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hRlarge
      calc
        U' ≤ U*((2+2*C₂)*R^(2*E))+1 := add_le_add_right
          (mul_le_mul_of_nonneg_left hshape hU.le) 1
        _ = (2+2*C₂)*R^(L+2*E)+1 := by rw [← hRU]; ring
        _ ≤ (3+2*C₂)*R^(L+2*E) := by linarith
        _ ≤ R*R^(L+2*E) := mul_le_mul_of_nonneg_right hcR (by positivity)
        _ = R^L' := by
          simpa only [L', Real.rpow_one, mul_comm] using (Real.rpow_add hRpos (L+2*E) 1).symm
    have hObs := hSer j hj₀ hj₁ (a+(v : ℤ)*((i : ℤ)+1-M)) (v*M) s J
      (Nat.mul_pos hv hM) hvs hvd hs hsR hJ
      (heisenbergCoverTest Φ k l m) U' (hcover Φ U hΦ k l hm)
    rw [heisenbergCoverTest_chartMean_eq_zero_of_lipschitz Φ U hΦ k l hm hmean, sub_zero] at hObs
    apply hObs.trans
    calc
      _ ≤ R^(-(B+L'))*R^L' := mul_le_mul_of_nonneg_left hU' (by positivity)
      _ = ε := by rw [← Real.rpow_add hRpos, show -(B+L')+L' = -B by ring]
  have hfin := hmain α β U δ ε τ a v K Φ p hv hKone hδpos hδlt
    (Real.rpow_nonneg hRpos.le _) (Real.rpow_nonneg hXpos.le _) hΦ hp hboundHoriz hlong
  apply hfin.trans
  apply max_le
  · have hδU : δ*U = R^(-A-1) := by
      dsimp only [δ,U,g]
      rw [← Real.rpow_add hRpos, show -(A+L+1)+L = -A-1 by ring]
    rw [hδU]
    exact (Real.rpow_le_rpow_of_exponent_le hRone (by linarith : -A-1 ≤ -A)).trans
      (le_mul_of_one_le_left (by positivity) (by norm_num))
  · have hfactor : 1+C₁*((d : ℝ)*H) ≤ R^(E+1) := by
      have hcR : 1+C₁*d ≤ R :=
        ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hRlarge
      have hb := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hH (by positivity : 0 ≤ (d : ℝ))) hC₁
      calc
        _ ≤ (1+C₁*(d : ℝ))*R^E := by nlinarith
        _ ≤ R*R^E := mul_le_mul_of_nonneg_right hcR (by positivity)
        _ = R^(E+1) := by
          simpa only [Real.rpow_one, mul_comm] using (Real.rpow_add hRpos E 1).symm
    have hratio : τ/(K : ℝ) ≤ X^(-(1/6 : ℝ)) := by
      calc
        _ ≤ τ/X^(1/2 : ℝ) := div_le_div_of_nonneg_left (by positivity)
          (Real.rpow_pos_of_pos hXpos _) hK
        _ = _ := by
          dsimp only [τ]
          rw [← Real.rpow_sub hXpos, show (1/3 : ℝ)-1/2= -(1/6 : ℝ) by norm_num]
    have hshort' : R^(A+L+2*E+3) * X^(-(1/6 : ℝ)) ≤ 1 := by
      rw [Real.rpow_neg hXpos.le, ← div_eq_mul_inv]
      exact (div_le_one (Real.rpow_pos_of_pos hXpos _)).mpr hshort
    have hshortfinal :
        R^(E+1)*(R^(E+1)*X^(-(1/6 : ℝ))*U) ≤ R^(-A-1) := by
      have h : R^(E+1)*(R^(E+1)*X^(-(1/6 : ℝ))*U) =
          R^(-A-1) * (R^(A+L+2*E+3)*X^(-(1/6 : ℝ))) := by
        dsimp only [U]
        calc
          _ = (R^(E+1)*R^(E+1)*R^L)*X^(-(1/6 : ℝ)) := by ring
          _ = R^(L+2*E+2)*X^(-(1/6 : ℝ)) := by
            rw [← Real.rpow_add hRpos, ← Real.rpow_add hRpos]
            congr 2
            ring
          _ = _ := by
            rw [← mul_assoc, ← Real.rpow_add hRpos]
            congr 2
            ring
      rw [h]
      exact mul_le_of_le_one_right (by positivity) hshort'
    have hlongfinal : R^(E+1)*ε = R^(-A-1) := by
      dsimp only [ε,B]
      rw [← Real.rpow_add hRpos, show E+1 + -(A+E+2)= -A-1 by ring]
    have hsmallRight : (H*(d.factorial : ℝ))*τ*U/(K : ℝ) ≤
        R^(E+1)*X^(-(1/6 : ℝ))*U := by
      rw [show (H*(d.factorial : ℝ))*τ*U/(K : ℝ) =
        (H*(d.factorial : ℝ))*(τ/(K : ℝ))*U by ring]
      gcongr
    calc
      _ ≤ R^(E+1)*(ε+R^(E+1)*X^(-(1/6 : ℝ))*U) := by gcongr
      _ ≤ 2*R^(-A-1) := by rw [mul_add, hlongfinal]; linarith
      _ ≤ 2*R^(-A) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hRone (by linarith : -A-1 ≤ -A)) (by norm_num)

/-- Proposition 4.3's twisted Heisenberg estimate, conditional on the
scalar and product forms of the quantitative horizontal obstruction. The
degree, logarithmic exponents, and slope witnesses are fixed before the
large-scale threshold. The progression origin, step, length, test, and
polynomial phase are uniform after that threshold. -/
theorem twisted_heisenberg_log_saving_for_denominators
    (hGT : ProductHeisenbergObstruction) (hScalar : ScalarHeisenbergObstruction)
    {α β : ℝ} (hα : BadlyApproximable α) {r : ℕ → ℕ} (hβ : AdmissibleBetaDenominators β r)
    {d : ℕ} (hd : 0 < d) {A L : ℝ} (hA : 0 < A) (hL : 0 < L) :
    ∀ᶠ X : ℝ in atTop, ∀ j : ℕ, (r j : ℝ) ≤ X^(1/100 : ℝ) → X^(1/100 : ℝ) < (r (j+1) : ℝ) →
      ∀ (a : ℤ) (v K : ℕ), 0 < v → (v : ℝ) ≤ X^(1/10000 : ℝ) → ¬ r j ∣ v →
      X^(1/2 : ℝ) ≤ (K : ℝ) →
      ∀ Φ : HeisenbergPoint → ℂ, HeisenbergLipschitzNormLE Φ (Real.log X ^ L) →
      (∀ x y, (∫ z in (0 : ℝ)..1, Φ (x,y,z)) = 0) →
      ∀ p : Polynomial ℝ, p.natDegree ≤ d →
      ‖heisenbergTwistedSum Φ α β a v K (fun t => p.eval (t : ℝ)) / (K : ℂ)‖ ≤
        2*Real.log X ^ (-A) := by
  have hhoriz := heisenberg_horizontal_dilated_for_denominators α β hα hβ
  have hscalar := scalar_heisenberg_equidistribution_for_denominators hScalar α β hα hβ
  obtain ⟨_, a, _, hprime, c, C, _, hc, hC, _, hscale⟩ := hβ
  refine twisted_heisenberg_log_saving_of_dilated hGT (fun j => (hprime j).1) ?_
    hhoriz hscalar hd hA hL
  intro E B hE hB
  filter_upwards [horizontal_scale_bounds c C E B hc hC hE hB] with X hX
  intro j hj
  exact (hX (r j) (r (j+1)) (hprime j).1.pos (hscale j).1 (hscale j).2.1 hj).1

/-- The degree-zero case uses the same estimate applied to a test of degree
at most one. This permits every natural degree bound in the manuscript. -/
theorem twisted_heisenberg_log_saving
    (hGT : ProductHeisenbergObstruction) (hScalar : ScalarHeisenbergObstruction)
    {α β : ℝ} (hα : BadlyApproximable α) {r : ℕ → ℕ} (hβ : AdmissibleBetaDenominators β r)
    (d : ℕ) {A L : ℝ} (hA : 0 < A) (hL : 0 < L) :
    ∀ᶠ X : ℝ in atTop, ∀ j : ℕ, (r j : ℝ) ≤ X^(1/100 : ℝ) → X^(1/100 : ℝ) < (r (j+1) : ℝ) →
      ∀ (a : ℤ) (v K : ℕ), 0 < v → (v : ℝ) ≤ X^(1/10000 : ℝ) → ¬ r j ∣ v →
      X^(1/2 : ℝ) ≤ (K : ℝ) →
      ∀ Φ : HeisenbergPoint → ℂ, HeisenbergLipschitzNormLE Φ (Real.log X ^ L) →
      (∀ x y, (∫ z in (0 : ℝ)..1, Φ (x,y,z)) = 0) →
      ∀ p : Polynomial ℝ, p.natDegree ≤ d →
      ‖heisenbergTwistedSum Φ α β a v K (fun t => p.eval (t : ℝ)) / (K : ℂ)‖ ≤
        2*Real.log X ^ (-A) := by
  have hd : 0 < max d 1 := zero_lt_one.trans_le (le_max_right _ _)
  filter_upwards [twisted_heisenberg_log_saving_for_denominators hGT hScalar hα hβ hd hA hL]
    with X hX
  intro j hj hj' a v K hv hvX hcop hK Φ hΦ hmean p hp
  exact hX j hj hj' a v K hv hvX hcop hK Φ hΦ hmean p (hp.trans (le_max_left _ _))

/-- The supremum formulation of the twisted bound in Proposition 4.3. -/
theorem twisted_heisenberg_phaseNorm
    (hGT : ProductHeisenbergObstruction) (hScalar : ScalarHeisenbergObstruction)
    {α β : ℝ} (hα : BadlyApproximable α) {r : ℕ → ℕ} (hβ : AdmissibleBetaDenominators β r)
    (d : ℕ) {A L : ℝ} (hA : 0 < A) (hL : 0 < L) :
    ∀ᶠ X : ℝ in atTop, ∀ j : ℕ, (r j : ℝ) ≤ X^(1/100 : ℝ) → X^(1/100 : ℝ) < (r (j+1) : ℝ) →
      ∀ (a : ℤ) (v K : ℕ), 0 < v → (v : ℝ) ≤ X^(1/10000 : ℝ) → ¬ r j ∣ v →
      X^(1/2 : ℝ) ≤ (K : ℝ) →
      ∀ Φ : HeisenbergPoint → ℂ, HeisenbergLipschitzNormLE Φ (Real.log X ^ L) →
      (∀ x ∈ Set.Ico (0 : ℝ) 1, ∀ y ∈ Set.Ico (0 : ℝ) 1,
        (∫ z in (0 : ℝ)..1, Φ (x,y,z)) = 0) →
      phaseNorm (d+1) (positiveInterval K) (fun t => Φ (heisenbergOrbit α β (a+(v : ℤ)*t))) ≤
        2*Real.log X ^ (-A) := by
  filter_upwards [twisted_heisenberg_log_saving hGT hScalar hα hβ d hA hL] with X hX
  intro j hj hj' a v K hv hvX hcop hK Φ hΦ hmean
  unfold phaseNorm
  apply csSup_le
  · exact ⟨_, 0, Nat.zero_lt_succ _, rfl⟩
  · rintro _ ⟨p, hp, rfl⟩
    rw [phaseAverage_eq_heisenbergTwistedSum]
    exact hX j hj hj' a v K hv hvX hcop hK Φ hΦ
      ((heisenberg_verticalMean_iff_unitChart Φ hΦ).mpr hmean) p (Nat.le_of_lt_succ hp)

end NilBohr
