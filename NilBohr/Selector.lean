import NilBohr.Arithmetic

open scoped ComplexConjugate

namespace NilBohr

/-- Integer floor values on a parallelogram have vanishing mixed difference
when all four fractional parts lie in a common interval of length less than 1/2. -/
theorem floor_parallelogram (lo hi a b c d : ℝ) (hs : 2 * (hi - lo) < 1)
    (hadd : a + d = b + c)
    (ha : Int.fract a ∈ Set.Icc lo hi) (hb : Int.fract b ∈ Set.Icc lo hi)
    (hc : Int.fract c ∈ Set.Icc lo hi) (hd : Int.fract d ∈ Set.Icc lo hi) :
    ⌊a⌋ + ⌊d⌋ = ⌊b⌋ + ⌊c⌋ := by
  simp only [Int.fract, Set.mem_Icc] at ha hb hc hd
  have hbounds :
      -1 < ((⌊a⌋ + ⌊d⌋ - ⌊b⌋ - ⌊c⌋ : ℤ) : ℝ) ∧
      ((⌊a⌋ + ⌊d⌋ - ⌊b⌋ - ⌊c⌋ : ℤ) : ℝ) < 1 := by
    push_cast
    constructor
    · linarith [ha.2, hb.1, hc.1, hd.2]
    · linarith [ha.1, hb.2, hc.2, hd.1]
  have hlow : (-1 : ℤ) < ⌊a⌋ + ⌊d⌋ - ⌊b⌋ - ⌊c⌋ := by exact_mod_cast hbounds.1
  have hhigh : ⌊a⌋ + ⌊d⌋ - ⌊b⌋ - ⌊c⌋ < (1 : ℤ) := by exact_mod_cast hbounds.2
  omega

/-- Every vertex of the cube with the given ordered directions satisfies `P`.
The vertices keep their multiplicities, even for a degenerate cube. -/
def cubeEvery : List ℤ → (ℤ → Prop) → ℤ → Prop
  | [], P, x => P x
  | t :: ts, P, x => cubeEvery ts P x ∧ cubeEvery ts P (x + t)

/-- The alternating sum of a real phase over the cube, with the manuscript's
sign convention `(-1)^|ω|`. -/
def cubeDifference : List ℤ → (ℤ → ℝ) → ℤ → ℝ
  | [], f, x => f x
  | t :: ts, f, x => cubeDifference ts f x - cubeDifference ts f (x + t)

/-- The conjugated product on an individual Gowers cube. -/
def cubeProduct : List ℤ → (ℤ → ℂ) → ℤ → ℂ
  | [], f, x => f x
  | t :: ts, f, x => cubeProduct ts f x * conj (cubeProduct ts f (x + t))

private theorem cubeDifference_three_heisenberg (α β lo hi : ℝ) (n u v w : ℤ)
    (hs : 2 * (hi - lo) < 1)
    (h : cubeEvery [u, v, w] (fun t => Int.fract (β * (t : ℝ)) ∈ Set.Icc lo hi) n) :
    cubeDifference [u, v, w] (heisenbergPhase α β) n = 0 := by
  rcases h with ⟨⟨⟨h₀, hw⟩, ⟨hv, hvw⟩⟩, ⟨⟨hu, huw⟩, ⟨huv, huvw⟩⟩⟩
  let B : ℤ → ℝ := fun t => ⌊β * (t : ℝ)⌋
  have hface (x a b : ℤ)
      (h₀ : Int.fract (β * (x : ℝ)) ∈ Set.Icc lo hi)
      (h₁ : Int.fract (β * ((x+a : ℤ) : ℝ)) ∈ Set.Icc lo hi)
      (h₂ : Int.fract (β * ((x+b : ℤ) : ℝ)) ∈ Set.Icc lo hi)
      (h₃ : Int.fract (β * ((x+a+b : ℤ) : ℝ)) ∈ Set.Icc lo hi) :
      B (x+a+b) = B (x+a) + B (x+b) - B x := by
    have hf := floor_parallelogram lo hi
      (β * (x : ℝ)) (β * ((x+a : ℤ) : ℝ))
      (β * ((x+b : ℤ) : ℝ)) (β * ((x+a+b : ℤ) : ℝ)) hs
      (by push_cast; ring) h₀ h₁ h₂ h₃
    simp only [B]
    exact_mod_cast (show ⌊β * ((x+a+b : ℤ) : ℝ)⌋ =
        ⌊β * ((x+a : ℤ) : ℝ)⌋ + ⌊β * ((x+b : ℤ) : ℝ)⌋ - ⌊β * (x : ℝ)⌋ from by omega)
  have hvw' := hface n v w h₀ hv hw hvw
  have huw' := hface n u w h₀ hu hw huw
  have huv' := hface n u v h₀ hu hv huv
  have huvw' := hface (n+u) v w hu huv huw huvw
  have hlast : B (n+u+v+w) = B (n+u) + B (n+v) + B (n+w) - 2 * B n := by
    linarith
  change cubeDifference [u, v, w]
    (fun t => α * β / 2 * (t : ℝ)^2 - α * β / 2 * t - α * t * B t) n = 0
  simp only [cubeDifference, hvw', huw', huv', hlast, Int.cast_add]
  ring

/-- The exact cancellation in the proof of equation `e:twolocalizednorm`, for
all cube orders at least three and arbitrary signed (including zero) steps. -/
theorem cubeDifference_heisenberg_of_short (α β lo hi : ℝ) (hs : 2 * (hi - lo) < 1)
    (steps : List ℤ) (n : ℤ) (horder : 3 ≤ steps.length)
    (h : cubeEvery steps (fun t => Int.fract (β * (t : ℝ)) ∈ Set.Icc lo hi) n) :
    cubeDifference steps (heisenbergPhase α β) n = 0 := by
  induction steps generalizing n with
  | nil => simp at horder
  | cons u steps ih =>
      by_cases htail : 3 ≤ steps.length
      · change cubeDifference steps (heisenbergPhase α β) n -
          cubeDifference steps (heisenbergPhase α β) (n + u) = 0
        rw [ih n htail h.1, ih (n + u) htail h.2, sub_self]
      · cases steps with
        | nil => simp at horder
        | cons v steps =>
            cases steps with
            | nil => simp at horder
            | cons w steps =>
                cases steps with
                | nil => exact cubeDifference_three_heisenberg α β lo hi n u v w hs h
                | cons z steps => simp only [List.length_cons] at htail; omega

/-- The additive character `e(t)=exp(2πit)`. -/
noncomputable def phaseExponential (t : ℝ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * t)

theorem phaseExponential_sub (x y : ℝ) :
    phaseExponential (x-y) = phaseExponential x * conj (phaseExponential y) := by
  unfold phaseExponential
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [Complex.ofReal_sub, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  ring

@[simp] theorem phaseExponential_zero : phaseExponential 0 = 1 := by
  simp [phaseExponential]

private theorem cubeEvery_mono {P Q : ℤ → Prop} (hPQ : ∀ x, P x → Q x)
    (steps : List ℤ) (x : ℤ) (h : cubeEvery steps P x) : cubeEvery steps Q x := by
  induction steps generalizing x with
  | nil => exact hPQ x h
  | cons t ts ih => exact ⟨ih x h.1, ih (x+t) h.2⟩

private theorem cubeEvery_affine (a v : ℤ) (P : ℤ → Prop) (steps : List ℤ) (x : ℤ) :
    cubeEvery steps (fun t => P (a+v*t)) x ↔
    cubeEvery (steps.map (v * ·)) P (a+v*x) := by
  induction steps generalizing x with
  | nil => rfl
  | cons t ts ih =>
      simp only [cubeEvery, List.map_cons, ih,
        show a + v * (x+t) = a + v*x + v*t by ring]

private theorem cubeDifference_affine (a v : ℤ) (f : ℤ → ℝ) (steps : List ℤ) (x : ℤ) :
    cubeDifference steps (fun t => f (a+v*t)) x =
    cubeDifference (steps.map (v * ·)) f (a+v*x) := by
  induction steps generalizing x with
  | nil => rfl
  | cons t ts ih =>
      simp only [cubeDifference, List.map_cons, ih,
        show a + v * (x+t) = a + v*x + v*t by ring]

private theorem cubeDifference_const_mul (c : ℝ) (f : ℤ → ℝ) (steps : List ℤ) (x : ℤ) :
    cubeDifference steps (fun t => c * f t) x = c * cubeDifference steps f x := by
  induction steps generalizing x with
  | nil => rfl
  | cons t ts ih => simp only [cubeDifference, ih, mul_sub]

theorem cubeProduct_mul (f g : ℤ → ℂ) (steps : List ℤ) (x : ℤ) :
    cubeProduct steps (fun t => f t * g t) x = cubeProduct steps f x * cubeProduct steps g x := by
  induction steps generalizing x with
  | nil => rfl
  | cons t ts ih => simp only [cubeProduct, ih, map_mul]; ring

theorem cubeProduct_phaseExponential (f : ℤ → ℝ) (steps : List ℤ) (x : ℤ) :
    cubeProduct steps (fun t => phaseExponential (f t)) x =
    phaseExponential (cubeDifference steps f x) := by
  induction steps generalizing x with
  | nil => rfl
  | cons t ts ih => simp only [cubeProduct, cubeDifference, ih, phaseExponential_sub]

private theorem cubeProduct_eq_zero_of_not_every_nonzero (f χ : ℤ → ℂ) (steps : List ℤ) (x : ℤ)
    (h : ¬cubeEvery steps (fun t => χ t ≠ 0) x) :
    cubeProduct steps (fun t => f t * χ t) x = 0 := by
  classical
  induction steps generalizing x with
  | nil =>
      change ¬χ x ≠ 0 at h
      simp only [cubeProduct, not_not.mp h, mul_zero]
  | cons t ts ih =>
      change ¬(cubeEvery ts (fun t => χ t ≠ 0) x ∧
        cubeEvery ts (fun t => χ t ≠ 0) (x+t)) at h
      rcases not_and_or.mp h with h | h
      · simp only [cubeProduct, ih x h, zero_mul]
      · simp only [cubeProduct, ih (x+t) h, map_zero, mul_zero]

/-- Multiplication by a localized vertical character preserves every individual
Gowers cube product of order at least three. This is the exact finite identity
underlying (but not including the norm inequality in) Lemma 6.2. -/
theorem cubeProduct_localized_vertical (α β lo hi : ℝ) (hs : 2 * (hi - lo) < 1)
    (a v h : ℤ) (f : ℤ → ℂ) (χ : ℝ → ℂ)
    (hχ : ∀ t, χ t ≠ 0 → t ∈ Set.Icc lo hi)
    (steps : List ℤ) (x : ℤ) (horder : 3 ≤ steps.length) :
    cubeProduct steps (fun t =>
      f t * χ (Int.fract (β * ((a+v*t : ℤ) : ℝ))) *
        phaseExponential ((h : ℝ) * heisenbergPhase α β (a+v*t))) x =
    cubeProduct steps (fun t => f t * χ (Int.fract (β * ((a+v*t : ℤ) : ℝ)))) x := by
  let cutoff (t : ℤ) := χ (Int.fract (β * ((a+v*t : ℤ) : ℝ)))
  by_cases hcut : cubeEvery steps (fun t => cutoff t ≠ 0) x
  · have hshort := cubeEvery_mono (fun t ht => hχ _ ht) steps x hcut
    have hshort' := (cubeEvery_affine a v
      (fun t => Int.fract (β * (t : ℝ)) ∈ Set.Icc lo hi) steps x).mp hshort
    have hzero := cubeDifference_heisenberg_of_short α β lo hi hs
      (steps.map (v * ·)) (a+v*x) (by simpa using horder) hshort'
    have hzero' := (cubeDifference_affine a v (heisenbergPhase α β) steps x).trans hzero
    simp only [cubeProduct_mul, cubeProduct_phaseExponential, cubeDifference_const_mul,
      hzero', mul_zero, phaseExponential_zero, mul_one]
  · have hzero := cubeProduct_eq_zero_of_not_every_nonzero f cutoff steps x hcut
    change cubeProduct steps (fun t => f t * cutoff t * _) x =
      cubeProduct steps (fun t => f t * cutoff t) x
    rw [cubeProduct_mul, hzero, zero_mul]

private theorem cubeEvery_base {P : ℤ → Prop} (steps : List ℤ) (x : ℤ)
    (h : cubeEvery steps P x) : P x := by
  induction steps generalizing x with
  | nil => exact h
  | cons t ts ih => exact ih x h.1

private theorem cubeEvery_singleStep {P : ℤ → Prop} (steps : List ℤ) (x t : ℤ)
    (hm : t ∈ steps) (h : cubeEvery steps P x) : P (x+t) := by
  induction steps generalizing x with
  | nil => simp at hm
  | cons u us ih =>
      rcases List.mem_cons.mp hm with rfl | hm
      · exact cubeEvery_base us (x+t) h.2
      · exact ih x hm h.1

/-- Values used in the finite cube sum are extended by zero off the closed
integer interval `[L,U]`. -/
def zeroOutside (L U : ℤ) (f : ℤ → ℂ) (t : ℤ) : ℂ :=
  if t ∈ Finset.Icc L U then f t else 0

/-- A nonzero cube product has base in the interval and every direction is
within its diameter. Thus the finite sum below contains every nonzero term
of the manuscript's sum on the integers. -/
theorem cubeProduct_nonzero_implies_bounds (L U : ℤ) (f : ℤ → ℂ) (steps : List ℤ) (x : ℤ)
    (h : cubeProduct steps (zeroOutside L U f) x ≠ 0) :
    L ≤ x ∧ x ≤ U ∧ ∀ t ∈ steps, -(U-L) ≤ t ∧ t ≤ U-L := by
  have hAll : cubeEvery steps (fun t => zeroOutside L U f t ≠ 0) x := by
    by_contra hn
    apply h
    simpa only [one_mul] using cubeProduct_eq_zero_of_not_every_nonzero
      (fun _ => 1) (zeroOutside L U f) steps x hn
  have hInt := cubeEvery_mono (P := fun t => zeroOutside L U f t ≠ 0)
    (Q := fun t => t ∈ Finset.Icc L U) (fun t hne => by
      by_contra hnot
      exact hne (if_neg hnot)) steps x hAll
  have hx := Finset.mem_Icc.mp (cubeEvery_base steps x hInt)
  refine ⟨hx.1, hx.2, fun t ht => ?_⟩
  have hxt := Finset.mem_Icc.mp (cubeEvery_singleStep steps x t ht hInt)
  omega

private def intervalDirections (L U : ℤ) (S : ℕ)
    (h : Fin S → Fin (2 * (U-L).toNat + 1)) : List ℤ :=
  List.ofFn fun j => ((h j).val : ℤ) - ((U-L).toNat : ℤ)

/-- The exact zero-extended `2^S`-th Gowers power. A direction in `[-W,W]`
has the unique index `h+W` in `Fin (2*W+1)`, where `W` is the diameter. -/
noncomputable def gowersCubePower (S : ℕ) (L U : ℤ) (f : ℤ → ℂ) : ℂ :=
  ∑ x ∈ Finset.Icc L U,
    ∑ h : Fin S → Fin (2 * (U-L).toNat + 1),
      cubeProduct (intervalDirections L U S h) (zeroOutside L U f) x

/-- The normalized quantity in `e:normalized-gowers` on a finite integer
interval. The exact invariance below compares identical powers and
normalization, independently of the proof of norm inequalities. -/
noncomputable def normalizedGowers (S : ℕ) (L U : ℤ) (f : ℤ → ℂ) : ℝ :=
  (gowersCubePower S L U f).re ^ ((2 : ℝ)^S)⁻¹ /
    (gowersCubePower S L U (fun _ => 1)).re ^ ((2 : ℝ)^S)⁻¹

theorem gowersCubePower_localized_vertical (S : ℕ) (hS : 3 ≤ S) (L U : ℤ)
    (α β lo hi : ℝ) (hs : 2 * (hi-lo) < 1) (a v h : ℤ) (f : ℤ → ℂ)
    (χ : ℝ → ℂ) (hχ : ∀ t, χ t ≠ 0 → t ∈ Set.Icc lo hi) :
    gowersCubePower S L U (fun t =>
      f t * χ (Int.fract (β * ((a+v*t : ℤ) : ℝ))) *
        phaseExponential ((h : ℝ) * heisenbergPhase α β (a+v*t))) =
    gowersCubePower S L U (fun t => f t * χ (Int.fract (β * ((a+v*t : ℤ) : ℝ)))) := by
  let cutoff (t : ℤ) := χ (Int.fract (β * ((a+v*t : ℤ) : ℝ)))
  let twist (t : ℤ) := phaseExponential ((h : ℝ) * heisenbergPhase α β (a+v*t))
  have h₁ : zeroOutside L U (fun t => f t * cutoff t * twist t) =
      (fun t => zeroOutside L U f t * cutoff t * twist t) := by
    funext t
    unfold zeroOutside
    split_ifs <;> simp
  have h₂ : zeroOutside L U (fun t => f t * cutoff t) =
      (fun t => zeroOutside L U f t * cutoff t) := by
    funext t
    unfold zeroOutside
    split_ifs <;> simp
  change gowersCubePower S L U (fun t => f t * cutoff t * twist t) =
    gowersCubePower S L U (fun t => f t * cutoff t)
  unfold gowersCubePower
  rw [h₁, h₂]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun hs' _ => ?_
  exact cubeProduct_localized_vertical α β lo hi hs a v h (zeroOutside L U f) χ hχ
    (intervalDirections L U S hs') x (by simpa [intervalDirections] using hS)

/-- Equation `e:twolocalizednorm`, before the Fourier-multiplier inequality. -/
theorem normalizedGowers_localized_vertical (S : ℕ) (hS : 3 ≤ S) (L U : ℤ)
    (α β lo hi : ℝ) (hs : 2 * (hi-lo) < 1) (a v h : ℤ) (f : ℤ → ℂ)
    (χ : ℝ → ℂ) (hχ : ∀ t, χ t ≠ 0 → t ∈ Set.Icc lo hi) :
    normalizedGowers S L U (fun t =>
      f t * χ (Int.fract (β * ((a+v*t : ℤ) : ℝ))) *
        phaseExponential ((h : ℝ) * heisenbergPhase α β (a+v*t))) =
    normalizedGowers S L U (fun t => f t * χ (Int.fract (β * ((a+v*t : ℤ) : ℝ)))) := by
  unfold normalizedGowers
  rw [gowersCubePower_localized_vertical S hS L U α β lo hi hs a v h f χ hχ]

end NilBohr
