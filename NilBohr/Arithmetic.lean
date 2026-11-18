import Mathlib

namespace NilBohr

noncomputable section

/-- Equation `e:heisenberg-phase`, as a real lift of the circle-valued phase. -/
def heisenbergPhase (α β : ℝ) (n : ℤ) : ℝ :=
  α * β / 2 * (n : ℝ)^2 - α * β / 2 * n - α * n * ⌊β * n⌋

/-- The bracket phase in equation `e:bracket-phase`. -/
def bracketPhase (α β : ℝ) (n : ℤ) : ℝ :=
  α * ((n : ℝ) + 1) * ⌊β * ((n : ℝ) + 1)⌋

/-- The exact change of origin and quadratic twist. -/
theorem bracketPhase_eq (α β : ℝ) (n : ℤ) :
    bracketPhase α β n =
      -heisenbergPhase α β (n + 1) + α * β / 2 * ((n : ℝ)^2 + n) := by
  simp only [bracketPhase, heisenbergPhase, Int.cast_add, Int.cast_one]
  ring

/-- The floor increment across the seam of the horizontal chart. The equality
case is included in the upper piece, as in the proof of the bracket pointwise theorem. -/
def horizontalCarry (β t : ℝ) : ℤ := if 1 - β ≤ t then 1 else 0

theorem floor_add_eq_floor_add_horizontalCarry (β x : ℝ) (hβ₀ : 0 ≤ β)
    (hβ₁ : β ≤ 1) :
    ⌊x + β⌋ = ⌊x⌋ + horizontalCarry β (Int.fract x) := by
  rw [horizontalCarry]
  split_ifs with h
  · apply Int.floor_eq_iff.mpr
    push_cast
    have hlo := Int.fract_nonneg x
    have hhi := Int.fract_lt_one x
    simp only [Int.fract] at h hlo hhi
    constructor <;> linarith
  · rw [add_zero]
    apply Int.floor_eq_iff.mpr
    have hlo := Int.fract_nonneg x
    simp only [Int.fract] at h hlo
    constructor <;> linarith

/-- The exact piecewise decomposition preceding `e:limitofprimesexp`. -/
theorem bracketPhase_add_heisenbergPhase (α β : ℝ) (n : ℤ)
    (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1) :
    bracketPhase α β n + heisenbergPhase α β n =
      α * β / 2 * ((n : ℝ)^2 + n) - α * Int.fract (β * n) +
        α * ((n : ℝ) + 1) * horizontalCarry β (Int.fract (β * n)) := by
  have h := floor_add_eq_floor_add_horizontalCarry β (β * n) hβ₀ hβ₁
  simp only [bracketPhase, heisenbergPhase, mul_add, mul_one, h, Int.cast_add, Int.fract]
  ring

/-- The floor identity used for the largest-cell proof of bracket recurrence. -/
theorem floor_next_of_near_int (β : ℝ) (n m : ℤ) (ε : ℝ)
    (hnear : |β * (n : ℝ) - m| < ε) (hleft : ε < β) (hright : ε < 1 - β) :
    ⌊β * ((n : ℝ) + 1)⌋ = m := by
  apply Int.floor_eq_iff.mpr
  have habs := abs_lt.mp hnear
  rw [mul_add, mul_one]
  constructor <;> linarith [habs.1, habs.2]

/-- Exact near-integer identity in the proof of the bracket recurrence corollary. -/
theorem bracketPhase_add_heisenbergPhase_near_int (α β : ℝ) (n m : ℤ) (ε : ℝ)
    (hnear : |β * (n : ℝ) - m| < ε) (hleft : ε < β) (hright : ε < 1 - β) :
    bracketPhase α β n + heisenbergPhase α β n =
      α * β / 2 * ((n : ℝ)^2 + n) + α * n * ((m : ℝ) - ⌊β * n⌋) -
        α * (β * n - m) := by
  simp only [bracketPhase, heisenbergPhase, floor_next_of_near_int β n m ε hnear hleft hright]
  ring

/-- The floor identity on multiples of an approximating denominator, under
exactly the one-sided error bound used in the introduction and appendix. -/
theorem floor_mul_eq_int_of_small_error (β : ℝ) (a r n m : ℤ) (hr : r ≠ 0)
    (hdvd : a * n = r * m)
    (hsmall₀ : 0 ≤ (β - (a : ℝ) / r) * n)
    (hsmall₁ : (β - (a : ℝ) / r) * n < 1) : ⌊β * n⌋ = m := by
  have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr
  have hprod : (a : ℝ) * n = (r : ℝ) * m := by exact_mod_cast hdvd
  have hrat : (a : ℝ) / r * n = m := by
    rw [div_mul_eq_mul_div, div_eq_iff hr']
    linarith
  apply Int.floor_eq_iff.mpr
  rw [sub_mul, hrat] at hsmall₀ hsmall₁
  constructor <;> linarith

/-- Exact quadratic approximation on the residue class in the appendix.
The displayed remainder is the source of the uniform `O((qM)²/rNext)` error. -/
theorem heisenbergPhase_rational_residue (α β : ℝ) (a r n : ℤ)
    (hr : r ≠ 0) (hdiv : r ∣ n)
    (hsmall₀ : 0 ≤ (β - (a : ℝ)/r) * n)
    (hsmall₁ : (β - (a : ℝ)/r) * n < 1) :
    heisenbergPhase α β n =
      -α * ((a : ℝ)/r) / 2 * ((n : ℝ)^2+n) +
        α * (β-(a : ℝ)/r) / 2 * ((n : ℝ)^2-n) := by
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr
  obtain ⟨m, hm⟩ := hdiv
  have hprod : a*n = r*(a*m) := by rw [hm]; ring
  have hfloor := floor_mul_eq_int_of_small_error β a r n (a*m) hr hprod hsmall₀ hsmall₁
  have hfloorR : (↑⌊β * (n : ℝ)⌋ : ℝ) = (a : ℝ)/r*n := by
    rw [hfloor, div_mul_eq_mul_div, eq_div_iff hrR]
    push_cast
    rw [show (n : ℝ) = (r : ℝ)*m by exact_mod_cast hm]
    ring
  unfold heisenbergPhase
  rw [hfloorR]
  ring

/-- The exact affine-lifting identity, formulated for the polynomial value
rather than division on integers. -/
theorem affine_lift_value (a q x shift value : ℤ) (h : q * shift = value) :
    a + q * (x + shift) = (a + q * x) + value := by
  rw [mul_add, h, add_assoc]

/-- An integer polynomial preserves congruence modulo any integer modulus. -/
theorem eval_modEq (P : Polynomial ℤ) (L x y : ℤ) (h : x ≡ y [ZMOD L]) :
    P.eval x ≡ P.eval y [ZMOD L] := by
  induction P using Polynomial.induction_on' with
  | add P Q ihP ihQ => simpa only [Polynomial.eval_add] using ihP.add ihQ
  | monomial n a =>
      simpa only [Polynomial.eval_monomial] using (Int.ModEq.refl a).mul (h.pow n)

/-- Integral realization of `P(qy)/q` for a polynomial with zero constant
coefficient. Dropping a putative constant coefficient makes the definition total. -/
def rescalePolynomial (q : ℤ) (P : Polynomial ℤ) : Polynomial ℤ :=
  Polynomial.X * P.divX.comp (Polynomial.C q * Polynomial.X)

@[simp] theorem coeff_zero_rescalePolynomial (q : ℤ) (P : Polynomial ℤ) :
    (rescalePolynomial q P).coeff 0 = 0 :=
  Polynomial.coeff_X_mul_zero _

theorem coeff_succ_rescalePolynomial (q : ℤ) (P : Polynomial ℤ) (j : ℕ) :
    (rescalePolynomial q P).coeff (j + 1) = P.coeff (j + 1) * q^j := by
  rw [rescalePolynomial, Polynomial.coeff_X_mul, Polynomial.comp_C_mul_X_coeff,
    Polynomial.coeff_divX]

theorem natDegree_rescalePolynomial (q : ℤ) (P : Polynomial ℤ) (hq : q ≠ 0) :
    (rescalePolynomial q P).natDegree = P.natDegree := by
  apply le_antisymm
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    cases n with
    | zero => exact coeff_zero_rescalePolynomial q P
    | succ j => simp [coeff_succ_rescalePolynomial, Polynomial.coeff_eq_zero_of_natDegree_lt hn]
  · cases he : P.natDegree with
    | zero => exact Nat.zero_le _
    | succ j =>
        apply Polynomial.le_natDegree_of_ne_zero
        rw [coeff_succ_rescalePolynomial]
        refine mul_ne_zero ?_ (pow_ne_zero _ hq)
        have hP : P ≠ 0 := by
          intro hP
          simp [hP] at he
        simpa only [← he, Polynomial.coeff_natDegree] using Polynomial.leadingCoeff_ne_zero.mpr hP

theorem eval_rescalePolynomial (q : ℤ) (P : Polynomial ℤ) (hP : P.coeff 0 = 0) (y : ℤ) :
    q * (rescalePolynomial q P).eval y = P.eval (q * y) := by
  have hdiv := congrArg (Polynomial.eval (q * y)) (Polynomial.X_mul_divX_add P)
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C,
    hP, add_zero] at hdiv
  simpa only [rescalePolynomial, Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_X,
    Polynomial.eval_C, mul_assoc] using hdiv

/-- The rescaling used to pass from modulus `q` to modulus `q*r`. -/
theorem eval_rescalePolynomial_mul (q r : ℤ) (P : Polynomial ℤ) (hP : P.coeff 0 = 0)
    (hq : q ≠ 0) (y : ℤ) :
    r * (rescalePolynomial (q*r) P).eval y = (rescalePolynomial q P).eval (r*y) := by
  apply mul_left_cancel₀ hq
  rw [← mul_assoc, eval_rescalePolynomial _ _ hP, eval_rescalePolynomial _ _ hP, mul_assoc]

/-- Coordinate product for the Heisenberg group used in the introduction. -/
def heisenbergMul (g h : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (g.1 + h.1, g.2.1 + h.2.1, g.2.2 + h.2.2 + g.1 * h.2.1)

/-- Coordinates of the integer orbit through the identity. -/
def heisenbergOrbit (α β : ℝ) (n : ℤ) : ℝ × ℝ × ℝ :=
  ((n : ℝ) * α, (n : ℝ) * β, α * β / 2 * ((n : ℝ)^2 - n))

theorem heisenbergOrbit_add (α β : ℝ) (m n : ℤ) :
    heisenbergOrbit α β (m + n) = heisenbergMul (heisenbergOrbit α β m) (heisenbergOrbit α β n) := by
  simp only [heisenbergOrbit, heisenbergMul, Int.cast_add, Prod.mk.injEq]
  exact ⟨by ring, by ring, by ring⟩

/-- The real lift of the vertical coordinate in the horizontal chart. -/
def reducedVertical (g : ℝ × ℝ × ℝ) : ℝ := g.2.2 - g.1 * ⌊g.2.1⌋

theorem reducedVertical_orbit (α β : ℝ) (n : ℤ) :
    reducedVertical (heisenbergOrbit α β n) = heisenbergPhase α β n := by
  simp only [reducedVertical, heisenbergOrbit, heisenbergPhase]
  rw [mul_comm (n : ℝ) β]
  ring

/-- Both chart coordinates are invariant under right multiplication by the
integer lattice. This proves the coordinate descent without any topological claim. -/
theorem heisenberg_chart_right_lattice (g : ℝ × ℝ × ℝ) (u v w : ℤ) :
    Int.fract ((heisenbergMul g ((u : ℝ), (v : ℝ), (w : ℝ))).2.1) =
      Int.fract g.2.1 ∧
    Int.fract (reducedVertical (heisenbergMul g ((u : ℝ), (v : ℝ), (w : ℝ)))) =
      Int.fract (reducedVertical g) := by
  constructor
  · exact Int.fract_add_intCast g.2.1 v
  · have h : reducedVertical (heisenbergMul g ((u : ℝ), (v : ℝ), (w : ℝ))) =
        reducedVertical g + (↑(w - u * (⌊g.2.1⌋ + v)) : ℝ) := by
      simp only [reducedVertical, heisenbergMul, Int.floor_add_intCast, Int.cast_sub,
        Int.cast_mul, Int.cast_add]
      ring
    rw [h, Int.fract_add_intCast]

/-- Distance to the nearest integer, represented by the norm on the unit circle. -/
noncomputable def torusNorm (x : ℝ) : ℝ := ‖(x : UnitAddCircle)‖

theorem torusNorm_eq (x : ℝ) : torusNorm x = |x - round x| := UnitAddCircle.norm_eq

theorem torusNorm_le_abs (x : ℝ) : torusNorm x ≤ |x| := by
  rw [torusNorm_eq]
  simpa using round_le x (0 : ℤ)

theorem torusNorm_sub_le (x y : ℝ) : torusNorm (x-y) ≤ torusNorm x + torusNorm y := by
  change ‖((x-y : ℝ) : UnitAddCircle)‖ ≤ _
  rw [AddCircle.coe_sub]
  exact norm_sub_le _ _

theorem torusNorm_add_le (x y : ℝ) : torusNorm (x+y) ≤ torusNorm x + torusNorm y := by
  change ‖((x+y : ℝ) : UnitAddCircle)‖ ≤ _
  rw [AddCircle.coe_add]
  exact norm_add_le _ _

theorem torusNorm_mul_nat_le (n : ℕ) (x : ℝ) : torusNorm (n*x) ≤ n * torusNorm x := by
  change ‖(((n : ℝ)*x : ℝ) : UnitAddCircle)‖ ≤ _
  rw [← nsmul_eq_mul, AddCircle.coe_nsmul]
  exact norm_nsmul_le

theorem torusNorm_mul_int_le (n : ℤ) (x : ℝ) : torusNorm (n*x) ≤ |(n : ℝ)| * torusNorm x := by
  change ‖(((n : ℝ)*x : ℝ) : UnitAddCircle)‖ ≤ _
  rw [← zsmul_eq_mul, AddCircle.coe_zsmul]
  simpa [Int.cast_natAbs] using (norm_zsmul_le n (x : UnitAddCircle))

theorem torusNorm_add_int (x : ℝ) (m : ℤ) : torusNorm (x+m) = torusNorm x := by
  have hm : (((m : ℝ)) : UnitAddCircle) = 0 :=
    (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨m, by simp [zsmul_eq_mul]⟩
  simp only [torusNorm, AddCircle.coe_add, hm, add_zero]

/-- Bad approximability stated for positive integers also gives the same
bound with a signed nonzero integer and its absolute value. -/
theorem badlyApproximable_bound_int {α c : ℝ}
    (h : ∀ m : ℕ, 0 < m → c ≤ (m : ℝ) * torusNorm ((m : ℝ) * α))
    (m : ℤ) (hm : m ≠ 0) : c ≤ |(m : ℝ)| * torusNorm ((m : ℝ) * α) := by
  have hnat := h m.natAbs (Int.natAbs_pos.mpr hm)
  have hnorm : torusNorm ((m.natAbs : ℝ) * α) = torusNorm ((m : ℝ) * α) := by
    obtain he | he := Int.natAbs_eq m
    · have he' : (m : ℝ) = (m.natAbs : ℝ) := by
        simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℝ)) he
      rw [he']
    · have he' : (m : ℝ) = -(m.natAbs : ℝ) := by exact_mod_cast he
      rw [he', neg_mul]
      simp [torusNorm, AddCircle.coe_neg]
  rwa [hnorm, Int.cast_natAbs, Int.cast_abs] at hnat

/-- The finite arithmetic estimate for the `k ≠ 0` case of Lemma 6.1. -/
theorem horizontal_nonzero_alpha_bound (α β c : ℝ) (r v : ℕ) (a k l : ℤ)
    (hr : 0 < r) (hv : 0 < v) (hk : k ≠ 0)
    (hα : ∀ m : ℕ, 0 < m → c ≤ (m : ℝ) * torusNorm ((m : ℝ) * α)) :
    c / (|(k : ℝ)| * v * (r : ℝ)^2) - |(l : ℝ)| * v * |β - (a : ℝ)/r| ≤
      torusNorm ((v : ℝ) * (k*α + l*β)) := by
  have hR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hV : 0 < (v : ℝ) := by exact_mod_cast hv
  have hK : 0 < |(k : ℝ)| := abs_pos.mpr (by exact_mod_cast hk)
  let x : ℝ := (v : ℝ) * (k*α + l*β)
  let e : ℝ := (v : ℝ) * l * (β - (a : ℝ)/r)
  have he : |e| = |(l : ℝ)| * v * |β - (a : ℝ)/r| := by
    dsimp [e]
    rw [abs_mul, abs_mul, abs_of_pos hV, mul_comm (v : ℝ)]
  have hx : (r : ℝ) * x - (r : ℝ) * e =
      (r : ℝ) * v * k * α + (↑((v : ℤ) * l * a) : ℝ) := by
    push_cast
    dsimp [x, e]
    field_simp [hR.ne']
    ring
  have hsimple :
      torusNorm ((r : ℝ)*v*k*α) ≤ (r : ℝ) * torusNorm x + (r : ℝ) * |e| := by
    calc
      torusNorm ((r : ℝ)*v*k*α) = torusNorm ((r : ℝ)*x - (r : ℝ)*e) := by
        rw [hx, torusNorm_add_int]
      _ ≤ torusNorm ((r : ℝ)*x) + torusNorm ((r : ℝ)*e) := torusNorm_sub_le _ _
      _ ≤ (r : ℝ) * torusNorm x + (r : ℝ)*|e| := by
        apply add_le_add (torusNorm_mul_nat_le r x)
        simpa [abs_mul, abs_of_pos hR] using torusNorm_le_abs ((r : ℝ)*e)
  have hm : (r : ℤ) * v * k ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by omega) (by omega)) hk
  have hraw := badlyApproximable_bound_int hα ((r : ℤ) * v * k) hm
  push_cast at hraw
  rw [abs_mul, abs_mul, abs_of_pos hR, abs_of_pos hV] at hraw
  have hdivide : c / ((r : ℝ) * v * |(k : ℝ)|) ≤ torusNorm ((r : ℝ)*v*k*α) :=
    (div_le_iff₀ (by positivity)).mpr (by simpa only [mul_comm] using hraw)
  have hdivide' := (div_le_iff₀ hR).mpr (by
    linarith [hdivide.trans hsimple] : c / ((r : ℝ)*v*|(k : ℝ)|) ≤
      (torusNorm x + |e|) * (r : ℝ))
  have hrewrite : ((r : ℝ)*v*|(k : ℝ)|) * r = |(k : ℝ)| * v * (r : ℝ)^2 := by ring
  rw [div_div, hrewrite, he] at hdivide'
  linarith

/-- A rational with nonintegral numerator-to-denominator ratio lies at
least `1/r` from the nearest integer. -/
theorem torusNorm_fraction_ge_inv (p r : ℤ) (hr : 0 < r) (hnd : ¬r ∣ p) :
    1 / (r : ℝ) ≤ torusNorm ((p : ℝ)/r) := by
  have hr' : 0 < (r : ℝ) := by exact_mod_cast hr
  let m : ℤ := round ((p : ℝ)/r)
  have hnon : p-r*m ≠ 0 := by
    intro he
    exact hnd ⟨m, by omega⟩
  have h : (1 : ℝ) ≤ |((p-r*m : ℤ) : ℝ)| := by exact_mod_cast Int.one_le_abs hnon
  push_cast at h
  have he : (p : ℝ)/r - m = ((p : ℝ) - (r : ℝ)*m)/r := by
    field_simp [hr'.ne']
  rw [torusNorm_eq, ← show m = round ((p : ℝ)/r) from rfl, he, abs_div, abs_of_pos hr']
  exact div_le_div_of_nonneg_right h hr'.le

/-- The finite arithmetic estimate for the `k = 0` case of Lemma 6.1. -/
theorem horizontal_zero_alpha_bound (β : ℝ) (r v a l : ℤ) (hr : 0 < r) (hv : 0 ≤ v)
    (hnd : ¬r ∣ v*l*a) :
    1 / (r : ℝ) - |(l : ℝ)| * v * |β - (a : ℝ)/r| ≤ torusNorm ((v : ℝ)*l*β) := by
  have hr' : 0 < (r : ℝ) := by exact_mod_cast hr
  have hv' : 0 ≤ (v : ℝ) := by exact_mod_cast hv
  let x : ℝ := (v : ℝ)*l*β
  let e : ℝ := (v : ℝ)*l*(β - (a : ℝ)/r)
  have he : |e| = |(l : ℝ)| * v * |β - (a : ℝ)/r| := by
    dsimp [e]
    rw [abs_mul, abs_mul, abs_of_nonneg hv', mul_comm (v : ℝ)]
  have hx : ((↑(v*l*a) : ℝ)/r) = x-e := by
    push_cast
    dsimp [x, e]
    ring
  have hrat := torusNorm_fraction_ge_inv (v*l*a) r hr hnd
  rw [hx] at hrat
  have h := hrat.trans ((torusNorm_sub_le x e).trans (add_le_add_left (torusNorm_le_abs e) _))
  rw [he] at h
  linarith

/-- The torus estimate at the end of the finite-cell argument for the bracket
recurrence. The three small torus norms are exactly those obtained in the cell. -/
theorem bracketPhase_near_neg_heisenbergPhase (α β ε : ℝ) (n : ℤ)
    (hεβ : ε < β) (hεβ' : ε < 1 - β)
    (hα : torusNorm (α*n) < ε) (hβ : torusNorm (β*n) < ε)
    (hθ : torusNorm (α*β/2*((n : ℝ)^2+n)) < 2*ε) :
    torusNorm (bracketPhase α β n + heisenbergPhase α β n) < (3+|α|)*ε := by
  have hε : 0 < ε := (norm_nonneg ((α * (n : ℝ) : ℝ) : UnitAddCircle)).trans_lt hα
  have hβ₀ : 0 ≤ β := by linarith
  have hβ₁ : β ≤ 1 := by linarith
  let m : ℤ := round (β*n)
  have hnear : |β * (n : ℝ) - m| < ε := by
    simpa only [torusNorm_eq] using hβ
  have hfloor := floor_next_of_near_int β n m ε hnear hεβ hεβ'
  have hincr := floor_add_eq_floor_add_horizontalCarry β (β * n) hβ₀ hβ₁
  have hrewrite : β * (n : ℝ) + β = β * ((n : ℝ)+1) := by ring
  rw [hrewrite, hfloor] at hincr
  have hcases : m - ⌊β * (n : ℝ)⌋ = 0 ∨ m - ⌊β * (n : ℝ)⌋ = 1 := by
    unfold horizontalCarry at hincr
    split_ifs at hincr <;> omega
  have hmiddle : torusNorm (α * n * ((m : ℝ) - ⌊β * (n : ℝ)⌋)) < ε := by
    rcases hcases with heq | heq
    · have heq' : (m : ℝ) - ⌊β * (n : ℝ)⌋ = 0 := by exact_mod_cast heq
      simpa [heq', torusNorm] using hε
    · have heq' : (m : ℝ) - ⌊β * (n : ℝ)⌋ = 1 := by exact_mod_cast heq
      simpa only [heq', mul_one] using hα
  have herror : torusNorm (α * (β * (n : ℝ) - m)) ≤ |α| * ε :=
    (torusNorm_le_abs _).trans <| by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hnear.le (abs_nonneg α)
  rw [bracketPhase_add_heisenbergPhase_near_int α β n m ε hnear hεβ hεβ']
  have htriangle := torusNorm_add_le (α*β/2*((n : ℝ)^2+n))
    (α * n * ((m : ℝ) - ⌊β * (n : ℝ)⌋))
  exact (torusNorm_sub_le _ _).trans_lt (by nlinarith)

end

end NilBohr
