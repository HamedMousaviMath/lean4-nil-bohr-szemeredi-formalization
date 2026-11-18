import NilBohr.GowersMultiplier

/-! The two estimates for the prime discrepancy in Theorem 3.2.
The geometric cutoff decomposition and scalar boundary occupancy are
separate from these estimates. -/

open Filter AddCircle Polynomial
open scoped Topology BigOperators

namespace NilBohr

/-- The normalized weighted count with supported unit-bounded inputs is
dominated by the mean absolute weight. -/
theorem norm_countingForm_le_mean_weight {k : ℕ} {N M : ℕ} (hN : 0 < N)
    (P : Fin k → Polynomial ℤ) (f : Fin k → ℤ → ℂ)
    (hf : ∀ i, OneBoundedOn (positiveInterval N) (f i))
    (hf' : ∀ i, SupportedOn (positiveInterval N) (f i)) (v : ℤ → ℂ) :
    ‖countingForm N M (positiveInterval N) P v f‖ ≤
      (∑ y ∈ positiveInterval M, ‖v y‖) / (M : ℝ) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  unfold countingForm
  rw [norm_div, norm_mul]
  simp only [Complex.norm_natCast]
  have hs : ‖∑ x ∈ positiveInterval N,
      ∑ y ∈ positiveInterval M, v y * ∏ i, f i (x + (P i).eval y)‖ ≤
      (N : ℝ) * (∑ y ∈ positiveInterval M, ‖v y‖) := by
    refine (norm_sum_le _ _).trans ?_
    have hsum (x : ℤ) :
        ‖∑ y ∈ positiveInterval M, v y * ∏ i, f i (x+(P i).eval y)‖ ≤
          ∑ y ∈ positiveInterval M, ‖v y‖ := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => ?_)
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (by
        rw [norm_prod]
        exact Finset.prod_le_one (fun i _ => norm_nonneg _) fun i _ =>
          oneBounded_of_supported (hf i) (hf' i) _)
    refine (Finset.sum_le_sum fun x _ => hsum x).trans_eq ?_
    rw [Finset.sum_const, card_positiveInterval, nsmul_eq_mul]
  refine (div_le_div_of_nonneg_right hs (by positivity)).trans_eq ?_
  rw [mul_div_mul_left _ _ hNpos.ne']

private theorem continuous_countingForm_weight {k : ℕ} (N M : ℕ) (X : Finset ℤ)
    (P : Fin k → Polynomial ℤ) (f : Fin k → ℤ → ℂ) :
    Continuous (fun v : ℤ → ℂ => countingForm N M X P v f) := by
  unfold countingForm
  refine (continuous_finset_sum _ fun x _ => continuous_finset_sum _ fun y _ => ?_).div_const _
  exact (continuous_apply y).mul continuous_const

private theorem countingForm_sum_weight {ι : Type*} {k : ℕ} (N M : ℕ) (X : Finset ℤ)
    (P : Fin k → Polynomial ℤ) (f : Fin k → ℤ → ℂ) (I : Finset ι) (v : ι → ℤ → ℂ) :
    countingForm N M X P (fun y => ∑ i ∈ I, v i y) f =
      ∑ i ∈ I, countingForm N M X P (v i) f := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [countingForm]
  | insert i I hi ih =>
    simp only [Finset.sum_insert hi, countingForm_add_weight, ih]

/-- The Fourier estimate of the interior count for one chart piece.
The hypothesis on the count is the weighted generalized von Neumann
inequality for the given tuple. -/
theorem norm_countingForm_localized_selector_le {k : ℕ} {N M S : ℕ} (hM : 0 < M)
    (hS : 3 ≤ S) (hG : NormalizedGowersLaws S)
    (P : Fin k → Polynomial ℤ) (f : Fin k → ℤ → ℂ)
    (C : ℝ) (hC : 0 ≤ C) (hCount : ∀ v : ℤ → ℂ,
      ‖countingForm N M (positiveInterval N) P v f‖ ≤
        C * normalizedGowers S 1 (M : ℤ) v)
    (α β : ℝ) (q : ℕ) (u : ℤ → ℂ) (F χ : C(Circle, ℂ))
    (hF : Summable fun h : ℤ => ‖fourierCoeff F h‖)
    (hAbs : Summable fun h : ℤ => ‖fourierCoeff χ h‖)
    (lo hi : ℝ) (hshort : 2*(hi-lo) < 1)
    (hχ : ∀ x : ℝ, x ∈ Set.Ico (0 : ℝ) 1 → χ (x : Circle) ≠ 0 → x ∈ Set.Icc lo hi) :
    ‖countingForm N M (positiveInterval N) P
      (fun t => u t * F (heisenbergPhase α β ((q : ℤ)*t) : Circle) *
        χ ((β*(((q : ℤ)*t : ℤ) : ℝ) : ℝ) : Circle)) f‖ ≤
      (∑' h : ℤ, ‖fourierCoeff F h‖) *
        (C * (∑' h : ℤ, ‖fourierCoeff χ h‖) * normalizedGowers S 1 (M : ℤ) u) := by
  let A (t : ℤ) := heisenbergPhase α β ((q : ℤ)*t)
  let B (t : ℤ) := β*(((q : ℤ)*t : ℤ) : ℝ)
  let T (v : ℤ → ℂ) := countingForm N M (positiveInterval N) P v f
  let v (h : ℤ) (t : ℤ) := u t * χ (B t : Circle) * phaseExponential ((h : ℝ)*A t)
  let w (h : ℤ) (t : ℤ) := fourierCoeff F h * v h t
  let D := C * (∑' h : ℤ, ‖fourierCoeff χ h‖) * normalizedGowers S 1 (M : ℤ) u
  have hI : (1 : ℤ) ≤ M := by exact_mod_cast hM
  have hv (h : ℤ) : ‖T (v h)‖ ≤ D := by
    have hm := localized_vertical_fourier_multiplier 1 (M : ℤ) hI S hS hG χ hAbs
      lo hi hshort hχ α β 0 q h u
    refine (hCount (v h)).trans ?_
    have hh : normalizedGowers S 1 (M : ℤ) (v h) ≤
        (∑' h : ℤ, ‖fourierCoeff χ h‖) * normalizedGowers S 1 (M : ℤ) u := by
      simpa [v, A, B] using hm
    simpa [D, mul_assoc] using mul_le_mul_of_nonneg_left hh hC
  have hMode (h : ℤ) : ‖T (w h)‖ ≤ ‖fourierCoeff F h‖ * D := by
    change ‖countingForm _ _ _ _ (fun t => fourierCoeff F h * v h t) f‖ ≤ _
    rw [countingForm_mul_weight, norm_mul]
    exact mul_le_mul_of_nonneg_left (hv h) (norm_nonneg _)
  have hSeries (t : ℤ) : HasSum (fun h => w h t)
      (u t * F (A t : Circle) * χ (B t : Circle)) := by
    have hFour (h : ℤ) : fourier h (A t : Circle) = phaseExponential ((h : ℝ)*A t) := by
      rw [fourier_coe_apply]
      unfold phaseExponential
      congr 1
      push_cast
      ring
    have hs := has_pointwise_sum_fourier_series_of_summable hF.of_norm (A t : Circle)
    simp_rw [smul_eq_mul, hFour] at hs
    simpa [w, v, mul_left_comm, mul_assoc, mul_comm] using
      hs.mul_left (u t * χ (B t : Circle))
  have hL : Tendsto (fun I : Finset ℤ => ‖T (fun t => ∑ h ∈ I, w h t)‖) atTop
      (𝓝 ‖T (fun t => u t * F (A t : Circle) * χ (B t : Circle))‖) :=
    (((continuous_countingForm_weight N M (positiveInterval N) P f).norm).tendsto _).comp
      (tendsto_pi_nhds.mpr hSeries)
  refine le_of_tendsto_of_tendsto hL (hF.hasSum.mul_right D) ?_
  filter_upwards [] with I
  change ‖countingForm _ _ _ _ (fun t => ∑ h ∈ I, w h t) f‖ ≤ _
  rw [countingForm_sum_weight]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun h _ => hMode h)

noncomputable def continuousCircleOfReal (ψ : C(Circle, ℝ)) : C(Circle, ℂ) :=
  ⟨fun t => (ψ t : ℂ), Complex.continuous_ofReal.comp ψ.continuous⟩

/-- The boundary loss is controlled by the scalar occupancy and Gowers
norm. The lower bound `-1 ≤ u` is the positivity of the prime weight
before subtracting one. -/
theorem norm_countingForm_selector_boundary_le {k : ℕ} {N M S : ℕ} (hN : 0 < N)
    (hM : 0 < M) (hS : 2 ≤ S) (hG : NormalizedGowersLaws S)
    (E : ℝ) (hE : 0 < E) (hMean : ∀ v : ℤ → ℂ,
      ‖(∑ t ∈ positiveInterval M, v t) / (M : ℂ)‖ ≤ E * normalizedGowers S 1 (M : ℤ) v)
    (P : Fin k → Polynomial ℤ) (f : Fin k → ℤ → ℂ)
    (hf : ∀ i, OneBoundedOn (positiveInterval N) (f i))
    (hf' : ∀ i, SupportedOn (positiveInterval N) (f i))
    (α β : ℝ) (q : ℕ) (u : ℤ → ℝ) (hu : ∀ t, -1 ≤ u t)
    (F : C(Circle, ℂ)) (ψ : C(Circle, ℝ)) (hψ : ∀ x, 0 ≤ ψ x)
    (hAbs : Summable fun h : ℤ => ‖fourierCoeff (continuousCircleOfReal ψ) h‖) :
    ‖countingForm N M (positiveInterval N) P
        (fun t => (u t : ℂ) * F (heisenbergPhase α β ((q : ℤ)*t) : Circle) *
          (ψ ((β*(((q : ℤ)*t : ℤ) : ℝ) : ℝ) : Circle) : ℂ)) f‖ ≤
        ‖F‖ * (2 * ((∑ t ∈ positiveInterval M, ψ ((β*(((q : ℤ)*t : ℤ) : ℝ) : ℝ) : Circle)) / (M : ℝ)) +
          E * (∑' h : ℤ, ‖fourierCoeff (continuousCircleOfReal ψ) h‖) *
            normalizedGowers S 1 (M : ℤ) (fun t => (u t : ℂ))) := by
  let A (t : ℤ) := heisenbergPhase α β ((q : ℤ)*t)
  let b (t : ℤ) := ψ ((β*(((q : ℤ)*t : ℤ) : ℝ) : ℝ) : Circle)
  let weight (t : ℤ) := (u t : ℂ)*F (A t : Circle)*(b t : ℂ)
  let I := positiveInterval M
  have hI : (1 : ℤ) ≤ M := by exact_mod_cast hM
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have wBound (t : ℤ) : ‖weight t‖ ≤ ‖F‖ * ((u t + 2) * b t) := by
    have hb : 0 ≤ b t := hψ _
    have hU : |u t| ≤ u t+2 := abs_le.mpr ⟨by linarith [hu t], by linarith⟩
    simp only [weight, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb]
    have hpp := mul_le_mul hU (F.norm_coe_le_norm (A t : Circle))
      (norm_nonneg _) (by linarith [hu t] : 0 ≤ u t+2)
    linarith [mul_le_mul_of_nonneg_right hpp hb]
  have hBound := norm_countingForm_le_mean_weight (M := M) hN P f hf hf' weight
  have hMult := normalizedGowers_mul_circle_pullback 1 (M : ℤ) hI S hS hG
    (continuousCircleOfReal ψ) hAbs (β*(q : ℝ)) 0 (fun t => (u t : ℂ))
  have hbfun (t : ℤ) : continuousCircleOfReal ψ (((β*(q : ℝ))*(t : ℝ)+0 : ℝ) : Circle) =
      (b t : ℂ) := by
    unfold continuousCircleOfReal b
    push_cast
    simp [add_zero, mul_assoc]
  simp_rw [hbfun] at hMult
  have hMeanB := (hMean (fun t => (u t : ℂ)*(b t : ℂ))).trans
    (mul_le_mul_of_nonneg_left hMult hE.le)
  have hRealMean : (∑ t ∈ I, u t*b t) / (M : ℝ) ≤
      E * (∑' h : ℤ, ‖fourierCoeff (continuousCircleOfReal ψ) h‖) *
        normalizedGowers S 1 (M : ℤ) (fun t => (u t : ℂ)) := by
    have hCast : ((∑ t ∈ I, (u t : ℂ)*(b t : ℂ)) / (M : ℂ)) =
        (((∑ t ∈ I, u t*b t) / (M : ℝ) : ℝ) : ℂ) := by push_cast; rfl
    rw [hCast, Complex.norm_real, Real.norm_eq_abs] at hMeanB
    exact (le_abs_self _).trans (by simpa [mul_assoc] using hMeanB)
  refine hBound.trans ?_
  calc
    (∑ t ∈ I, ‖weight t‖) / (M : ℝ) ≤
        (∑ t ∈ I, ‖F‖*((u t+2)*b t)) / (M : ℝ) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum fun t _ => wBound t) hMR.le
    _ = ‖F‖ * (((∑ t ∈ I, u t*b t) / (M : ℝ)) + 2*((∑ t ∈ I, b t) / (M : ℝ))) := by
      simp only [← Finset.mul_sum, add_mul, Finset.sum_add_distrib,
        add_div, mul_div_assoc]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      linarith [hRealMean]


/-- The interior and boundary estimates combined for a finite chart
decomposition. All three kinds of input are explicit: the weighted counting
bound, the cutoff Fourier sizes, and the scalar mean on the boundary. -/
theorem norm_countingForm_selector_discrepancy_le {ι : Type*} {k N M S : ℕ}
    (hN : 0 < N) (hM : 0 < M) (hS : 3 ≤ S) (hG : NormalizedGowersLaws S)
    (E : ℝ) (hE : 0 < E) (hMean : ∀ v : ℤ → ℂ,
      ‖(∑ t ∈ positiveInterval M, v t) / (M : ℂ)‖ ≤ E * normalizedGowers S 1 (M : ℤ) v)
    (P : Fin k → Polynomial ℤ) (f : Fin k → ℤ → ℂ)
    (hf : ∀ i, OneBoundedOn (positiveInterval N) (f i))
    (hf' : ∀ i, SupportedOn (positiveInterval N) (f i))
    (C : ℝ) (hC : 0 ≤ C) (hCount : ∀ v : ℤ → ℂ,
      ‖countingForm N M (positiveInterval N) P v f‖ ≤ C * normalizedGowers S 1 (M : ℤ) v)
    (α β : ℝ) (q : ℕ) (u : ℤ → ℝ) (hu : ∀ t, -1 ≤ u t)
    (F : C(Circle, ℂ)) (hF : Summable fun h : ℤ => ‖fourierCoeff F h‖)
    (J : Finset ι) (pieces : ι → C(Circle, ℂ)) (lo hi : ι → ℝ)
    (hAbs : ∀ j ∈ J, Summable fun h : ℤ => ‖fourierCoeff (pieces j) h‖)
    (hshort : ∀ j ∈ J, 2*(hi j-lo j) < 1)
    (hsupport : ∀ j ∈ J, ∀ t : ℝ,
      t ∈ Set.Ico (0 : ℝ) 1 → pieces j (t : Circle) ≠ 0 → t ∈ Set.Icc (lo j) (hi j))
    (ψ : C(Circle, ℝ)) (hψ : ∀ x, 0 ≤ ψ x)
    (hψAbs : Summable fun h : ℤ => ‖fourierCoeff (continuousCircleOfReal ψ) h‖)
    (hDecomp : ∀ x : Circle, (∑ j ∈ J, pieces j x) + (ψ x : ℂ) = 1) :
    ‖countingForm N M (positiveInterval N) P
        (fun t => (u t : ℂ) * F (heisenbergPhase α β ((q : ℤ)*t) : Circle)) f‖ ≤
      (∑' h : ℤ, ‖fourierCoeff F h‖) * C *
        (∑ j ∈ J, ∑' h : ℤ, ‖fourierCoeff (pieces j) h‖) *
        normalizedGowers S 1 (M : ℤ) (fun t => (u t : ℂ)) +
      ‖F‖ * (2 * ((∑ t ∈ positiveInterval M, ψ ((β*(((q : ℤ)*t : ℤ) : ℝ) : ℝ) : Circle)) / (M : ℝ)) +
        E * (∑' h : ℤ, ‖fourierCoeff (continuousCircleOfReal ψ) h‖) *
          normalizedGowers S 1 (M : ℤ) (fun t => (u t : ℂ))) := by
  let B (t : ℤ) := ((β*(((q : ℤ)*t : ℤ) : ℝ) : ℝ) : Circle)
  let V (t : ℤ) := (u t : ℂ)*F (heisenbergPhase α β ((q : ℤ)*t) : Circle)
  let W (j : ι) (t : ℤ) := V t * pieces j (B t)
  let R (t : ℤ) := V t * (ψ (B t) : ℂ)
  let G := normalizedGowers S 1 (M : ℤ) (fun t => (u t : ℂ))
  let K := ∑' h : ℤ, ‖fourierCoeff F h‖
  let D (j : ι) := ∑' h : ℤ, ‖fourierCoeff (pieces j) h‖
  let T (v : ℤ → ℂ) := countingForm N M (positiveInterval N) P v f
  have hSplit : V = fun t => (∑ j ∈ J, W j t) + R t := by
    funext t
    simp only [W, R, ← Finset.mul_sum, ← mul_add, hDecomp, mul_one]
  have hT : T V = (∑ j ∈ J, T (W j)) + T R := by
    unfold T
    rw [hSplit, countingForm_add_weight, countingForm_sum_weight]
  have hPiece (j : ι) (hj : j ∈ J) : ‖T (W j)‖ ≤ K*(C*D j*G) :=
    norm_countingForm_localized_selector_le hM hS hG P f C hC hCount α β q
      (fun t => (u t : ℂ)) F (pieces j) hF (hAbs j hj) (lo j) (hi j)
      (hshort j hj) (hsupport j hj)
  have hInterior : ‖∑ j ∈ J, T (W j)‖ ≤ K*C*(∑ j ∈ J,D j)*G := by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hPiece).trans_eq ?_)
    calc
      (∑ j ∈ J, K*(C*D j*G)) = ∑ j ∈ J, (K*C*G)*D j :=
        Finset.sum_congr rfl fun j _ => by ring
      _ = (K*C*G)*(∑ j ∈ J, D j) := (Finset.mul_sum _ _ _).symm
      _ = K*C*(∑ j ∈ J, D j)*G := by ring
  have hBoundary := norm_countingForm_selector_boundary_le hN hM
    (show 2 ≤ S by omega) hG E hE hMean P f hf hf' α β q u hu F ψ hψ hψAbs
  change ‖T V‖ ≤ _
  rw [hT]
  exact (norm_add_le _ _).trans (add_le_add hInterior hBoundary)

/-- The scalar optimization of the cutoff parameter in the selector
comparison. The norm of the prime discrepancy supplies the square
of the cutoff scale. -/
theorem selector_error_absorb {ε B D K L A F : ℝ}
    (hε : 0 < ε) (hD : 0 ≤ D) (hK : 0 ≤ K)
    (hA : 0 ≤ A) (hF : 0 ≤ F)
    {g interior boundary mean : ℝ} (hg₀ : 0 ≤ g)
    (hg : g ≤ B * ε^2) (hi : interior ≤ K/ε) (hb : boundary ≤ K/ε)
    (hMean : mean ≤ L*ε) :
    A*interior*g + F*(2*mean + D*boundary*g) ≤
      (A*K*B + F*(2*L+D*K*B))*ε := by
  have hKε : 0 ≤ K/ε := div_nonneg hK hε.le
  have hmain : K/ε*g ≤ K*B*ε := by
    calc
      K/ε*g ≤ K/ε*(B*ε^2) := mul_le_mul_of_nonneg_left hg hKε
      _ = K*B*ε := by field_simp; ring
  have hi' : A*interior*g ≤ A*K*B*ε := by
    have h := mul_le_mul_of_nonneg_left
      ((mul_le_mul_of_nonneg_right hi hg₀).trans hmain) hA
    simpa [mul_assoc] using h
  have hb' : D*boundary*g ≤ D*K*B*ε := by
    have h := mul_le_mul_of_nonneg_left
      ((mul_le_mul_of_nonneg_right hb hg₀).trans hmain) hD
    simpa [mul_assoc] using h
  have htotal : F*(2*mean + D*boundary*g) ≤ F*(2*L*ε+D*K*B*ε) :=
    mul_le_mul_of_nonneg_left (add_le_add (by linarith) hb') hF
  nlinarith [add_le_add hi' htotal]

end NilBohr
