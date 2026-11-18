import NilBohr.Horizontal

open Filter MeasureTheory

namespace NilBohr

/-- The diagonal dilation `D_(1/s)` in the proof of Proposition 4.3,
applied to the integer Heisenberg orbit before taking a quotient. -/
noncomputable def dilatedHeisenbergOrbit (α β : ℝ) (s : ℕ) (n : ℤ) : ℝ × ℝ × ℝ :=
  let g := heisenbergOrbit α β n
  (g.1/s, g.2.1/s, g.2.2/(s : ℝ)^2)

/-- A horizontal character with integer coefficients sees no constant term
in the `C∞[K]` seminorm. This is the exact linear coefficient at step `v`. -/
theorem dilated_horizontal_character_difference (α β : ℝ) (s : ℕ) (a v k l t : ℤ) :
    let g := dilatedHeisenbergOrbit α β s (a+v*(t+1))
    let g' := dilatedHeisenbergOrbit α β s (a+v*t)
    (k : ℝ)*g.1 + (l : ℝ)*g.2.1 - ((k : ℝ)*g'.1 + (l : ℝ)*g'.2.1) =
      (v : ℝ)*(k*α+l*β)/s := by
  simp only [dilatedHeisenbergOrbit, heisenbergOrbit, Int.cast_add, Int.cast_mul,
    Int.cast_one]
  ring

/-- Dilated horizontal obstruction estimate using any fixed admissible
prime-denominator sequence. -/
theorem heisenberg_horizontal_dilated_for_denominators (α β : ℝ)
    (hα : BadlyApproximable α) {r : ℕ → ℕ} (hβ : AdmissibleBetaDenominators β r) :
      ∀ A L D : ℝ, 0 < L → ∀ᶠ X : ℝ in atTop,
      ∀ j : ℕ, (r j : ℝ) ≤ X^(1/100 : ℝ) → X^(1/100 : ℝ) < (r (j+1) : ℝ) →
      ∀ (v s K : ℕ) (k l : ℤ), 0 < v → (v : ℝ) ≤ X^(1/5000 : ℝ) → ¬ r j ∣ v →
      0 < s → (s : ℝ) ≤ Real.log X ^ D → X^(1/3 : ℝ) ≤ (K : ℝ) →
      0 < max |(k : ℝ)| |(l : ℝ)| → max |(k : ℝ)| |(l : ℝ)| ≤ Real.log X ^ L →
      Real.log X ^ A < (K : ℝ) * torusNorm ((v : ℝ)*(k*α+l*β)/s) := by
  obtain ⟨_, _, η, hη, hDio⟩ := heisenberg_horizontal_for_denominators α β hα hβ
  intro A L D hL
  have hlogs := (isLittleO_log_rpow_rpow_atTop (A+D) (show (0 : ℝ) < 17/60 by norm_num)).bound
    (show 0 < η/2 by positivity)
  filter_upwards [eventually_ge_atTop (2 : ℝ), hDio L hL, hlogs] with X hX hDio hlogs
  intro j hj₀ hj₁ v s K k l hv hvX hvr hs hsX hK hfreq₀ hfreq₁
  have hXpos : 0 < X := by linarith
  have hlogpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hspos : 0 < (s : ℝ) := by exact_mod_cast hs
  let x : ℝ := (v : ℝ)*(k*α+l*β)
  have hx := hDio j hj₀ hj₁ v k l hv hvX hvr hfreq₀ hfreq₁
  have hsbound := torusNorm_mul_nat_le s (x/s)
  rw [mul_div_cancel₀ x (by positivity : (s : ℝ) ≠ 0)] at hsbound
  have hxbound := hx.trans hsbound
  have hlower : η * X^(17/60 : ℝ) ≤ (K : ℝ) * torusNorm (x/s) * s := by
    calc
      η * X^(17/60 : ℝ) = X^(1/3 : ℝ) * (η * X^(-(1/20 : ℝ))) := by
        rw [← mul_left_comm, ← Real.rpow_add hXpos]
        congr 1
        norm_num
      _ ≤ (K : ℝ) * ((s : ℝ) * torusNorm (x/s)) := by gcongr
      _ = (K : ℝ) * torusNorm (x/s) * s := by ring
  have hlogs' : (Real.log X)^(A+D) ≤ (η/2) * X^(17/60 : ℝ) := by
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hlogpos _),
      abs_of_pos (Real.rpow_pos_of_pos hXpos _)] using hlogs
  have hstrict : (Real.log X)^A * (s : ℝ) < (K : ℝ) * torusNorm (x/s) * s := by
    calc
      (Real.log X)^A * (s : ℝ) ≤ (Real.log X)^A * (Real.log X)^D := by gcongr
      _ = (Real.log X)^(A+D) := (Real.rpow_add hlogpos _ _).symm
      _ ≤ (η/2) * X^(17/60 : ℝ) := hlogs'
      _ < η * X^(17/60 : ℝ) := mul_lt_mul_of_pos_right (by linarith) (by positivity)
      _ ≤ (K : ℝ) * torusNorm (x/s) * s := hlower
  exact (mul_lt_mul_right hspos).mp hstrict

/-- In the full progression range of the scalar equidistribution proof,
the horizontal obstruction cannot occur, even after a polylogarithmic
finite dilation and for the shorter prefix lengths in the twisted proof. -/
theorem heisenberg_horizontal_dilated (α β : ℝ) (hα : BadlyApproximable α)
    (hβ : AdmissibleBeta β) :
    ∃ r : ℕ → ℕ, StrictMono r ∧
      (∀ᶠ X : ℝ in atTop, ∃ j : ℕ,
        (r j : ℝ) ≤ X^(1/100 : ℝ) ∧ X^(1/100 : ℝ) < (r (j+1) : ℝ)) ∧
      ∀ A L D : ℝ, 0 < L → ∀ᶠ X : ℝ in atTop,
      ∀ j : ℕ, (r j : ℝ) ≤ X^(1/100 : ℝ) → X^(1/100 : ℝ) < (r (j+1) : ℝ) →
      ∀ (v s K : ℕ) (k l : ℤ), 0 < v → (v : ℝ) ≤ X^(1/5000 : ℝ) → ¬ r j ∣ v →
      0 < s → (s : ℝ) ≤ Real.log X ^ D → X^(1/3 : ℝ) ≤ (K : ℝ) →
      0 < max |(k : ℝ)| |(l : ℝ)| → max |(k : ℝ)| |(l : ℝ)| ≤ Real.log X ^ L →
      Real.log X ^ A < (K : ℝ) * torusNorm ((v : ℝ)*(k*α+l*β)/s) := by
  obtain ⟨_, _, r, hr⟩ := (admissibleBeta_iff_exists_denominators β).mp hβ
  exact ⟨r, hr.1, (heisenberg_horizontal_for_denominators α β hα hr).1,
    heisenberg_horizontal_dilated_for_denominators α β hα hr⟩

/-- A real Heisenberg point in matrix coordinates `(x,y,z)`. -/
abbrev HeisenbergPoint := ℝ × ℝ × ℝ

noncomputable def heisenbergInv (g : HeisenbergPoint) : HeisenbergPoint :=
  (-g.1, -g.2.1, -g.2.2 + g.1*g.2.1)

/-- Sup norm of the Mal'cev coordinates for the ordered horizontal basis
and then the central basis vector. -/
noncomputable def heisenbergMalcevNorm (g : HeisenbergPoint) : ℝ :=
  max |g.1| (max |g.2.1| |g.2.2 - g.1*g.2.1|)

/-- The chain length in Green–Tao Definition 2.2, in the fixed coordinates. -/
noncomputable def heisenbergGroupDistance (g h : HeisenbergPoint) : ℝ :=
  sInf {d : ℝ | ∃ (n : ℕ) (x : ℕ → HeisenbergPoint), x 0 = g ∧ x n = h ∧
    d = ∑ i ∈ Finset.range n,
      min (heisenbergMalcevNorm (heisenbergMul (x i) (heisenbergInv (x (i+1)))))
          (heisenbergMalcevNorm (heisenbergMul (x (i+1)) (heisenbergInv (x i))))}

/-- The right lattice quotient distance formula from Green–Tao Definition 2.2. -/
noncomputable def heisenbergQuotientDistance (g h : HeisenbergPoint) : ℝ :=
  sInf {d : ℝ | ∃ u v w : ℤ,
    d = heisenbergGroupDistance g (heisenbergMul h ((u : ℝ), (v : ℝ), (w : ℝ)))}

def HeisenbergLipschitzNormLE (Φ : HeisenbergPoint → ℂ) (bound : ℝ) : Prop :=
  (∀ g (u v w : ℤ), Φ (heisenbergMul g ((u : ℝ), (v : ℝ), (w : ℝ))) = Φ g) ∧
  ∃ S M : ℝ, 0 ≤ S ∧ 0 ≤ M ∧ S+M ≤ bound ∧
    (∀ g, ‖Φ g‖ ≤ S) ∧
    (∀ g h, ‖Φ g - Φ h‖ ≤ M * heisenbergQuotientDistance g h)

/-- The scalar mean in the unit fundamental chart, expressed as an iterated
Lebesgue integral. The quotient Haar identification is proved in
`GreenTaoHaarAmbient.lean`. -/
noncomputable def heisenbergChartMean (Φ : HeisenbergPoint → ℂ) : ℂ :=
  intervalIntegral (fun x => intervalIntegral (fun y =>
    intervalIntegral (fun z => Φ (x,y,z)) 0 1 volume) 0 1 volume) 0 1 volume

noncomputable def heisenbergOrbitAverage (α β : ℝ) (a : ℤ) (v s K : ℕ)
    (Φ : HeisenbergPoint → ℂ) : ℂ :=
  (∑ t ∈ positiveInterval K, Φ (dilatedHeisenbergOrbit α β s (a + (v : ℤ)*t))) / (K : ℂ)

/-- Adaptation of Green–Tao Theorem 2.9 for scalar tests on the fixed
Heisenberg quotient. The checked deduction from the general theorem is
`scalarHeisenbergObstruction_of_greenTao`. -/
def ScalarHeisenbergObstruction : Prop :=
  ∃ C D : ℝ, 1 ≤ C ∧ 0 < D ∧
    ∀ (α β : ℝ) (a : ℤ) (v s K : ℕ), 0 < v → 0 < s → 1 < K →
    ∀ (Φ : HeisenbergPoint → ℂ) (U δ : ℝ), 0 < δ → δ < 1/2 →
    HeisenbergLipschitzNormLE Φ U →
      δ * U < ‖heisenbergOrbitAverage α β a v s K Φ - heisenbergChartMean Φ‖ →
    ∃ k l : ℤ, 0 < max |(k : ℝ)| |(l : ℝ)| ∧ max |(k : ℝ)| |(l : ℝ)| ≤ C * δ^(-D) ∧
      (K : ℝ) * torusNorm ((v : ℝ)*(k*α+l*β)/s) ≤ C * δ^(-D)

/-- The dilated scalar estimate, using the same admissible denominators as
the mixed horizontal-frequency exclusion. -/
theorem scalar_heisenberg_equidistribution_for_denominators
    (hGT : ScalarHeisenbergObstruction) (α β : ℝ)
    (hα : BadlyApproximable α) {r : ℕ → ℕ} (hβ : AdmissibleBetaDenominators β r) :
      ∀ B E : ℝ, 0 < B → ∀ᶠ X : ℝ in atTop,
      ∀ j : ℕ, (r j : ℝ) ≤ X^(1/100 : ℝ) → X^(1/100 : ℝ) < (r (j+1) : ℝ) →
      ∀ (a : ℤ) (v s K : ℕ), 0 < v → (v : ℝ) ≤ X^(1/5000 : ℝ) → ¬ r j ∣ v →
      0 < s → (s : ℝ) ≤ Real.log X ^ E → X^(1/3 : ℝ) ≤ (K : ℝ) →
      ∀ (Φ : HeisenbergPoint → ℂ) (U : ℝ), HeisenbergLipschitzNormLE Φ U →
      ‖heisenbergOrbitAverage α β a v s K Φ - heisenbergChartMean Φ‖ ≤
        Real.log X ^ (-B) * U := by
  obtain ⟨C, D, hC, hD, hcriterion⟩ := hGT
  have hhoriz := heisenberg_horizontal_dilated_for_denominators α β hα hβ
  intro B E hB
  let L := B*D+1
  have hL : 0 < L := by dsimp [L]; positivity
  have hlarge := (tendsto_rpow_atTop hB).comp Real.tendsto_log_atTop
  filter_upwards [eventually_ge_atTop (2 : ℝ), hlarge.eventually (eventually_ge_atTop (3 : ℝ)),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop C), hhoriz L L E hL] with X hX hlarge hlogC hh
  intro j hj₀ hj₁ a v s K hv hvX hvr hs hsX hK Φ U hΦ
  by_contra! hfail
  have hXpos : 0 < X := by linarith
  have hlogpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hKpos : 1 < K := by
    have hKreal := (Real.one_lt_rpow (by linarith : 1 < X) (by norm_num : (0 : ℝ) < 1/3)).trans_le hK
    exact_mod_cast hKreal
  let δ := Real.log X ^ (-B)
  have hδ : 0 < δ := by dsimp [δ]; exact Real.rpow_pos_of_pos hlogpos _
  have hδhalf : δ < 1/2 := by
    dsimp [δ]
    rw [Real.rpow_neg hlogpos.le, ← one_div]
    change (3 : ℝ) ≤ Real.log X ^ B at hlarge
    exact (div_lt_iff₀ (Real.rpow_pos_of_pos hlogpos _)).mpr (by linarith)
  obtain ⟨k, l, hk, hfreq, herror⟩ := hcriterion α β a v s K hv hs hKpos Φ U δ hδ hδhalf hΦ hfail
  have hbound : C * δ^(-D) ≤ Real.log X ^ L := by
    have hd : δ^(-D) = Real.log X ^ (B*D) := by
      dsimp [δ]
      rw [← Real.rpow_mul hlogpos.le, neg_mul_neg]
    rw [hd]
    calc
      C * Real.log X ^ (B*D) ≤ Real.log X * Real.log X ^ (B*D) :=
        mul_le_mul_of_nonneg_right hlogC (Real.rpow_nonneg hlogpos.le _)
      _ = Real.log X ^ L := by
        dsimp [L]
        rw [Real.rpow_add hlogpos, Real.rpow_one, mul_comm]
  exact (not_lt_of_ge (herror.trans hbound))
    (hh j hj₀ hj₁ v s K k l hv hvX hvr hs hsX hK hk (hfreq.trans hbound))

/-- Conditional scalar part of Proposition 4.3 in the stronger dilated
progression range used in its proof. The hypothesis supplies only the
small-horizontal-character criterion. -/
theorem scalar_heisenberg_equidistribution (hGT : ScalarHeisenbergObstruction)
    (α β : ℝ) (hα : BadlyApproximable α) (hβ : AdmissibleBeta β) :
    ∃ r : ℕ → ℕ, StrictMono r ∧
      (∀ᶠ X : ℝ in atTop, ∃ j : ℕ,
        (r j : ℝ) ≤ X^(1/100 : ℝ) ∧ X^(1/100 : ℝ) < (r (j+1) : ℝ)) ∧
      ∀ B E : ℝ, 0 < B → ∀ᶠ X : ℝ in atTop,
      ∀ j : ℕ, (r j : ℝ) ≤ X^(1/100 : ℝ) → X^(1/100 : ℝ) < (r (j+1) : ℝ) →
      ∀ (a : ℤ) (v s K : ℕ), 0 < v → (v : ℝ) ≤ X^(1/5000 : ℝ) → ¬ r j ∣ v →
      0 < s → (s : ℝ) ≤ Real.log X ^ E → X^(1/3 : ℝ) ≤ (K : ℝ) →
      ∀ (Φ : HeisenbergPoint → ℂ) (U : ℝ), HeisenbergLipschitzNormLE Φ U →
      ‖heisenbergOrbitAverage α β a v s K Φ - heisenbergChartMean Φ‖ ≤
        Real.log X ^ (-B) * U := by
  obtain ⟨_, _, r, hr⟩ := (admissibleBeta_iff_exists_denominators β).mp hβ
  exact ⟨r, hr.1, (heisenberg_horizontal_for_denominators α β hα hr).1,
    scalar_heisenberg_equidistribution_for_denominators hGT α β hα hr⟩

/-- Equation `e:heisenberg-equidistribution` in the manuscript's stated
undilated progression range. -/
theorem scalar_heisenberg_log_saving (hGT : ScalarHeisenbergObstruction)
    (α β : ℝ) (hα : BadlyApproximable α) (hβ : AdmissibleBeta β) :
    ∃ r : ℕ → ℕ, StrictMono r ∧
      (∀ᶠ X : ℝ in atTop, ∃ j : ℕ,
        (r j : ℝ) ≤ X^(1/100 : ℝ) ∧ X^(1/100 : ℝ) < (r (j+1) : ℝ)) ∧
      ∀ A L : ℝ, 0 < A → 0 < L → ∀ᶠ X : ℝ in atTop,
      ∀ j : ℕ, (r j : ℝ) ≤ X^(1/100 : ℝ) → X^(1/100 : ℝ) < (r (j+1) : ℝ) →
      ∀ (a : ℤ) (v K : ℕ), 0 < v → (v : ℝ) ≤ X^(1/10000 : ℝ) → ¬ r j ∣ v →
      X^(1/2 : ℝ) ≤ (K : ℝ) → ∀ Φ : HeisenbergPoint → ℂ,
      HeisenbergLipschitzNormLE Φ (Real.log X ^ L) →
      ‖heisenbergOrbitAverage α β a v 1 K Φ - heisenbergChartMean Φ‖ ≤ Real.log X ^ (-A) := by
  obtain ⟨r, hr, hbracket, hscalar⟩ := scalar_heisenberg_equidistribution hGT α β hα hβ
  refine ⟨r, hr, hbracket, fun A L hA hL => ?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℝ),
    hscalar (A+L) 0 (add_pos hA hL)] with X hX hscalar
  intro j hj₀ hj₁ a v K hv hvX hvr hK Φ hΦ
  have hXone : 1 ≤ X := by linarith
  have hlogpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hvbig := hvX.trans (Real.rpow_le_rpow_of_exponent_le hXone (by norm_num : (1/10000:ℝ) ≤ 1/5000))
  have hKbig := (Real.rpow_le_rpow_of_exponent_le hXone (by norm_num : (1/3:ℝ) ≤ 1/2)).trans hK
  have h := hscalar j hj₀ hj₁ a v 1 K hv hvbig hvr (by decide) (by simp) hKbig Φ _ hΦ
  rw [← Real.rpow_add hlogpos, show -(A+L)+L = -A by ring] at h
  exact h

end NilBohr
