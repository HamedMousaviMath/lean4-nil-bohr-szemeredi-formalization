import NilBohr.DensityCounting
import NilBohr.External

/-! Application of the quoted local weak regularity lemma to the indicator count. -/

open scoped BigOperators

namespace NilBohr

/-- On a finite support partition, the projection of an indicator is the
density of the set on the unique atom containing the spatial coordinate. -/
theorem localFactorProjection_indicator {I A : Finset ℤ} (hA : A ⊆ I)
    (factor : Finset (Finset ℤ))
    (hcover : ∀ x, x ∈ I ↔ ∃! B, B ∈ factor ∧ x ∈ B)
    (hatoms : ∀ B ∈ factor, B ⊆ I) :
    ∃ key : ℤ → Finset ℤ,
      (∀ x ∈ I, key x ∈ factor ∧ x ∈ key x) ∧
      (∀ x ∈ I, (I.filter (fun z => key z = key x)) = key x) ∧
      (∀ x, localFactorProjection factor (fun z => if z ∈ A then 1 else 0) x =
        (localFactorDensity I A key x : ℂ)) := by
  classical
  let key (x : ℤ) := if hx : x ∈ I then Classical.choose ((hcover x).mp hx).exists else ∅
  have hkey (x : ℤ) (hx : x ∈ I) : key x ∈ factor ∧ x ∈ key x := by
    simp only [key, dif_pos hx]
    exact Classical.choose_spec ((hcover x).mp hx).exists
  have hsame (x : ℤ) (hx : x ∈ I) (B : Finset ℤ) (hB : B ∈ factor) (hxB : x ∈ B) :
      key x = B := ((hcover x).mp hx).unique (hkey x hx) ⟨hB, hxB⟩
  have hfibre (x : ℤ) (hx : x ∈ I) : (I.filter (fun z => key z = key x)) = key x := by
    ext z
    rw [Finset.mem_filter]
    constructor
    · rintro ⟨hz, heq⟩
      exact heq ▸ (hkey z hz).2
    · intro hz
      have hzI := hatoms _ (hkey x hx).1 hz
      exact ⟨hzI, hsame z hzI _ (hkey x hx).1 hz⟩
  refine ⟨key, hkey, hfibre, ?_⟩
  intro x
  by_cases hx : x ∈ I
  · have hAfibre : A.filter (fun z => key z = key x) = key x ∩ A := by
      ext z
      rw [Finset.mem_filter, Finset.mem_inter]
      constructor
      · intro hz
        exact ⟨(hfibre x hx) ▸ Finset.mem_filter.mpr ⟨hA hz.1, hz.2⟩, hz.1⟩
      · intro hz
        have hzf : z ∈ I.filter (fun z => key z = key x) := by
          rw [hfibre x hx]
          exact hz.1
        exact ⟨hz.2, (Finset.mem_filter.mp hzf).2⟩
    rw [localFactorProjection, Finset.sum_eq_single (key x)]
    · simp only [if_pos (hkey x hx).2, localFactorDensity, if_pos hx,
        hfibre x hx, hAfibre, Complex.ofReal_div, Complex.ofReal_natCast]
      congr 1
      rw [← Finset.sum_filter]
      simp [Finset.filter_mem_eq_inter]
    · intro B hB hne
      rw [if_neg (fun hxB => hne (hsame x hx B hB hxB).symm)]
    · exact fun hn => False.elim (hn (hkey x hx).1)
  · simp only [localFactorDensity, if_neg hx, Complex.ofReal_zero, localFactorProjection]
    exact Finset.sum_eq_zero (fun B hB => if_neg (fun h => hx (hatoms B hB h)))

/-- Pulling back the indicator along an injective finite progression preserves
its intersection cardinality. -/
theorem card_progressionPullback_eq {A B : Finset ℤ} {a : ℤ} {L n : ℕ}
    (hL : 0 < L) (hB : B = (positiveInterval n).image (fun x => a + (L : ℤ) * x)) :
    (progressionPullback A a L n).card = (B ∩ A).card := by
  let f : ℤ → ℤ := fun x => a + (L : ℤ) * x
  have hL' : (L : ℤ) ≠ 0 := by exact_mod_cast hL.ne'
  have hf : Function.Injective f := fun x y h => mul_left_cancel₀ hL' (add_left_cancel h)
  have hImage : (progressionPullback A a L n).image f = B ∩ A := by
    ext z
    simp only [progressionPullback, Finset.mem_image, Finset.mem_filter,
      Finset.mem_inter, hB]
    constructor
    · rintro ⟨t, ⟨ht, htA⟩, htZ⟩
      exact ⟨⟨t, ht, htZ⟩, htZ ▸ htA⟩
    · rintro ⟨⟨t, ht, htZ⟩, hzA⟩
      exact ⟨t, ⟨ht, htZ.symm ▸ hzA⟩, htZ⟩
  rw [← hImage, Finset.card_image_of_injective _ hf]

/-- A larger lcm modulus includes all the divisibility requirements at
a smaller cutoff. -/
theorem initialModulus_dvd_of_le {v w : ℕ} (h : v ≤ w) :
    initialModulus v ∣ initialModulus w := by
  unfold initialModulus
  exact Finset.lcm_dvd (fun _ hn => Finset.dvd_lcm
    (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1, (Finset.mem_Icc.mp hn).2.trans h⟩))

/-- At a scale beyond the small-scale alternative, the quoted local weak
regularity lemma and the two counting errors yield an actual denser progression.
The regularity resolution is made explicit. -/
theorem density_progression_of_count_comparison
    (hreg : KMTTLocalWeakRegularity) {C : ℝ} (hC : 1 ≤ C) {d ℓ : ℕ} (hℓ : 0 < ℓ) :
    ∃ (A₀ A₁ D₁ c₁ D₂ : ℝ) (B₀ : ℕ), 0 < A₀ ∧ 0 < A₁ ∧ 0 < D₁ ∧ 0 < c₁ ∧ 0 < D₂ ∧
      ∀ {N M q w : ℕ}, 0 < N → 0 < q → 0 < M → M ≤ parameterLength N q d →
      ∀ (P : Fin (ℓ + 1) → Polynomial ℤ), FixedPolynomialFamily P →
      (P (Fin.last ℓ)).natDegree = d → (∀ i, i ≠ 0 → HasCoefficients C q (P i)) →
      ∀ (A : Finset ℤ), A ⊆ positiveInterval N →
      ∀ (weight : ℤ → ℂ) {μ η v : ℝ}, 0 < μ → 0 ≤ η → 0 < v → v / 8 < 1 / 2 →
      (v / 8)^(-A₀) ≤ (w : ℝ) → initialModulus w ∣ q →
      A₁ * ((q : ℝ) / (v / 8))^D₁ < (M : ℝ) →
      let δ := setDensity A N
      let f : Fin (ℓ + 1) → ℤ → ℂ := fun _ x => if x ∈ A then 1 else 0
      ‖countingForm N M (positiveInterval N) P weight f‖ ≤ μ * v / 4 →
      ‖countingForm N M (positiveInterval N) P weight f -
        (μ : ℂ) * countingForm N M (positiveInterval N) P (fun _ => 1) f‖ ≤ μ * v / 4 →
      v ≤ ‖countingForm N M (positiveInterval N) P (fun _ => 1) (fun _ => densityModel N δ)‖ →
      (((ℓ + 1 : ℕ) : ℝ)) * (2 * η * δ) * ((1 + η) * δ)^ℓ < 3 * v / 8 →
      ∃ (B : ℕ) (a : ℤ) (N' : ℕ), 1 ≤ B ∧ B ≤ B₀ ∧
        (positiveInterval N').image (fun x => a + ((q ^ B : ℕ) : ℤ) * x) ⊆
          positiveInterval N ∧
        (1 + η) * δ * N' ≤ (progressionPullback A a (q ^ B) N').card ∧
        c₁ * ((q : ℝ) / (v / 8))^(-D₂) * (M : ℝ)^(P 1).natDegree ≤ (N' : ℝ) := by
  classical
  obtain ⟨A₀, A₁, D₁, c₁, D₂, B₀, hA₀, hA₁, hD₁, hc₁, hD₂, hlemma⟩ :=
    hreg C d ℓ hC hℓ
  refine ⟨A₀, A₁, D₁, c₁, D₂, B₀, hA₀, hA₁, hD₁, hc₁, hD₂, ?_⟩
  intro N M q w hN hq hM hPar P hP hPmax hcoeff A hA weight μ η v hμ hη hv hv₈ hw hdiv hlarge
    δ f hweighted hcompare hmodel hgain
  let ε := v / 8
  have hcut : ⌈ε^(-A₀)⌉₊ ≤ w := Nat.ceil_le.mpr hw
  have hdiv' : initialModulus ⌈ε^(-A₀)⌉₊ ∣ q := (initialModulus_dvd_of_le hcut).trans hdiv
  have hfbounded : ∀ i, OneBoundedOn (positiveInterval N) (f i) := by
    intro i z hz
    dsimp [f]
    split_ifs <;> simp
  have hfsupp : ∀ i, SupportedOn (positiveInterval N) (f i) := by
    intro i z hz
    dsimp [f]
    exact if_neg (fun hzA => hz (hA hzA))
  have hregular := hlemma N M q hN hq hM hPar ε (div_pos hv (by norm_num)) hv₈ hdiv'
    P hP hPmax hcoeff f hfbounded hfsupp
  rcases hregular with hsmall | ⟨B, R, factors, hB, hB₀, hR, hcover, hatoms, hcomparison⟩
  · exact False.elim (not_lt_of_ge hsmall hlarge)
  choose key hkey hkeyslice hproj using fun i =>
    localFactorProjection_indicator hA (factors i) (hcover i) (fun B hB => (hatoms i B hB).1)
  let H (i : Fin (ℓ + 1)) (z : ℤ) := localFactorDensity (positiveInterval N) A (key i) z
  let L := c₁ * ((q : ℝ) / ε)^(-D₂) * (M : ℝ)^(P 1).natDegree
  have hδ : 0 ≤ δ := by dsimp [δ, setDensity]; positivity
  have hqB : 0 < q^B := pow_pos hq _
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hHbound (i : Fin (ℓ + 1)) (z : ℤ) (hz : z ∈ positiveInterval N) :
    ∃ (a : ℤ) (N' : ℕ), 0 < N' ∧ L ≤ (N' : ℝ) ∧
      (positiveInterval N').image (fun x => a + ((q ^ B : ℕ) : ℤ) * x) ⊆
        positiveInterval N ∧
      H i z = setDensity (progressionPullback A a (q ^ B) N') N' := by
    obtain ⟨hBsub, hcard, _, a, ha⟩ := hatoms i (key i z) (hkey i z hz).1
    have hRpos := (hR i).1
    have hRbound := (hR i).2
    let ν := if i = 0 then (P 1).natDegree else (P i).natDegree
    have hdeg : (P 1).natDegree ≤ ν := by
      dsimp [ν]
      split_ifs with hi
      · exact le_rfl
      · exact hP.2.2.2.monotone (Fin.one_le_of_ne_zero hi)
    have hLR : L ≤ (R i : ℝ) :=
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hM1 hdeg) (by positivity)).trans hRbound
    have hcard' : (R i : ℝ) ≤ ((key i z).card : ℝ) := by exact_mod_cast hcard
    have ha' : key i z = (positiveInterval (key i z).card).image
        (fun x => a + ((q ^ B : ℕ) : ℤ) * x) := by
      push_cast
      exact ha
    refine ⟨a, (key i z).card, hRpos.trans_le hcard, hLR.trans hcard', ?_, ?_⟩
    · rw [← ha']
      exact hBsub
    · change localFactorDensity (positiveInterval N) A (key i) z =
        setDensity (progressionPullback A a (q ^ B) (key i z).card) (key i z).card
      rw [localFactorDensity, if_pos hz, hkeyslice i z hz, setDensity,
        card_progressionPullback_eq hqB ha']
      have hEq : (A.filter fun x => key i x = key i z) = key i z ∩ A := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_inter]
        constructor
        · intro hx
          exact ⟨(hkeyslice i z hz) ▸ Finset.mem_filter.mpr ⟨hA hx.1, hx.2⟩, hx.1⟩
        · intro hx
          have hxf : x ∈ (positiveInterval N).filter (fun x => key i x = key i z) := by
            rw [hkeyslice i z hz]
            exact hx.1
          exact ⟨hx.2, (Finset.mem_filter.mp hxf).2⟩
      rw [hEq]
  have hcomparison' : ‖countingForm N M (positiveInterval N) P (fun _ => 1)
      (fun i z => (H i z : ℂ)) -
        countingForm N M (positiveInterval N) P (fun _ => 1) f‖ ≤ v / 8 := by
    change ‖countingForm N M (positiveInterval N) P (fun _ => 1)
      (fun i z => (H i z : ℂ)) -
        countingForm N M (positiveInterval N) P (fun _ => 1) f‖ ≤ ε
    have hfun : (fun i => localFactorProjection (factors i) (f i)) =
        (fun i z => (H i z : ℂ)) := funext fun i => funext (hproj i)
    simpa only [hfun] using hcomparison
  obtain ⟨a, N', hlen, hsub, hg⟩ := density_increment_atom_from_count_inputs hN P A H
    hδ hη hμ (fun i z => localFactorDensity_nonneg _ _ (key i) z)
    (fun i z hz => localFactorDensity_eq_zero_off _ _ (key i) hz)
    (fun i => sum_localFactorDensity_on_interval hN A hA (key i)) hHbound weight
    hweighted hcompare hcomparison' hmodel (by simpa using hgain)
  exact ⟨B, a, N', hB, hB₀, hsub, hg, hlen⟩

end NilBohr
