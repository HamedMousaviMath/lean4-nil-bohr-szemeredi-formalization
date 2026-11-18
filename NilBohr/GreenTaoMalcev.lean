import NilBohr.GreenTaoLeibman
import NilBohr.GreenTaoLieAlgebra
import NilBohr.GreenTaoNilpotence
import Mathlib.Data.Matrix.Notation

/-! The adapted rational Mal'cev bases for the two applications of the
quantitative Leibman theorem. -/

open Set Topology
open scoped Manifold ContDiff

namespace NilBohr

noncomputable section

private theorem centralAxis_closed : IsClosed (HeisenbergGroup.centralAxis : Set HeisenbergGroup) :=
  (isClosed_eq HeisenbergGroup.continuous_x continuous_const).inter
    (isClosed_eq HeisenbergGroup.continuous_y continuous_const)

private theorem centralAxis_connected :
    IsConnected (HeisenbergGroup.centralAxis : Set HeisenbergGroup) := by
  have heq : (HeisenbergGroup.centralAxis : Set HeisenbergGroup) =
      range (fun t : ℝ => HeisenbergGroup.coordinates.symm (0, 0, t)) := by
    ext g
    constructor
    · rintro ⟨hx, hy⟩
      refine ⟨g.z, ?_⟩
      apply HeisenbergGroup.ext <;> simp [HeisenbergGroup.coordinates, hx, hy]
    · rintro ⟨t, rfl⟩
      exact ⟨rfl, rfl⟩
  rw [heq]
  exact isConnected_range (HeisenbergGroup.continuous_coordinates_symm.comp (by fun_prop))

theorem heisenbergLeibmanFiltration :
    IsLeibmanFiltration HeisenbergGroup.lowerCentral 2 := by
  refine ⟨rfl, rfl, HeisenbergGroup.lowerCentral_antitone,
    HeisenbergGroup.commutator_mem_lowerCentral, ?_, ?_, rfl, ?_⟩
  · rintro (_ | _ | _ | i)
    · exact isClosed_univ
    · exact isClosed_univ
    · exact centralAxis_closed
    · simp [HeisenbergGroup.lowerCentral, Subgroup.coe_bot]
  · rintro (_ | _ | _ | i)
    · exact isConnected_univ
    · exact isConnected_univ
    · exact centralAxis_connected
    · simpa [HeisenbergGroup.lowerCentral, Subgroup.coe_bot] using
        (isConnected_singleton (α := HeisenbergGroup) (x := 1))
  · intro h
    let g : HeisenbergGroup := ⟨0, 0, 1⟩
    have hg : g ∈ HeisenbergGroup.lowerCentral 2 := ⟨rfl, rfl⟩
    rw [h] at hg
    have hz := congrArg HeisenbergGroup.z (Subgroup.mem_bot.mp hg)
    norm_num [g] at hz

theorem heisenbergProductLeibmanFiltration (d : ℕ) (hd : 0 < d) :
    IsLeibmanFiltration (heisenbergProductFiltration d) (max 2 d) := by
  refine ⟨by simp [heisenbergProductFiltration, HeisenbergGroup.lowerCentral,
    realDegreeFiltration], by simp [heisenbergProductFiltration, HeisenbergGroup.lowerCentral,
    realDegreeFiltration, Nat.succ_le_iff.mpr hd], heisenbergProductFiltration_antitone d,
    commutator_mem_heisenbergProductFiltration, ?_, ?_,
    heisenbergProductFiltration_eq_bot (Nat.lt_succ_self _), ?_⟩
  · intro i
    apply (heisenbergLeibmanFiltration.closed i).prod
    by_cases hi : i ≤ d
    · simp [realDegreeFiltration, hi]
    · simp [realDegreeFiltration, hi, Subgroup.coe_bot]
  · intro i
    apply (heisenbergLeibmanFiltration.connected i).prod
    by_cases hi : i ≤ d
    · simpa [realDegreeFiltration, hi] using
        (isConnected_univ : IsConnected (univ : Set (Multiplicative ℝ)))
    · simpa [realDegreeFiltration, hi, Subgroup.coe_bot] using
        (isConnected_singleton (α := Multiplicative ℝ) (x := 1))
  · intro h
    by_cases h₂ : d ≤ 2
    · let g : HeisenbergProductGroup := (⟨0, 0, 1⟩, 1)
      have hg : g ∈ heisenbergProductFiltration d (max 2 d) := by
        rw [max_eq_left h₂]
        exact ⟨⟨rfl, rfl⟩, Subgroup.one_mem _⟩
      rw [h] at hg
      have hz := congrArg (fun x : HeisenbergProductGroup => x.1.z) (Subgroup.mem_bot.mp hg)
      norm_num [g] at hz
    · have h₂' : 2 ≤ d := by omega
      let g : HeisenbergProductGroup := (1, Multiplicative.ofAdd 1)
      have hg : g ∈ heisenbergProductFiltration d (max 2 d) := by
        rw [max_eq_right h₂']
        refine ⟨Subgroup.one_mem _, ?_⟩
        simp [realDegreeFiltration]
      rw [h] at hg
      have hu := congrArg (fun x : HeisenbergProductGroup => (Multiplicative.toAdd x.2 : ℝ))
        (Subgroup.mem_bot.mp hg)
      norm_num [g] at hu

private def scalarTangentCoordinates : HeisenbergPoint ≃ₗ[ℝ] (Fin 3 → ℝ) where
  toFun p := ![p.1, p.2.1, p.2.2]
  invFun v := (v 0, v 1, v 2)
  left_inv p := by rcases p with ⟨_, _, _⟩; rfl
  right_inv v := by funext i; fin_cases i <;> rfl
  map_add' p q := by funext i; fin_cases i <;> rfl
  map_smul' a p := by funext i; fin_cases i <;> rfl

private def scalarBasis : Basis (Fin 3) ℝ
    (GroupLieAlgebra 𝓘(ℝ, HeisenbergPoint) HeisenbergGroup) :=
  Basis.ofEquivFun scalarTangentCoordinates

private theorem scalarBasis_repr (v : HeisenbergPoint) (i : Fin 3) :
    scalarBasis.repr v i = ![v.1, v.2.1, v.2.2] i := rfl

private theorem scalarBasis_apply (i : Fin 3) :
    (scalarBasis i : HeisenbergPoint) = ![(1, 0, 0), (0, 1, 0), (0, 0, 1)] i := by
  simp only [scalarBasis, Basis.coe_ofEquivFun]
  fin_cases i <;> norm_num [scalarTangentCoordinates, Pi.single_apply, Fin.ext_iff]

/-- The one-parameter Heisenberg subgroup with initial velocity `v`. -/
def heisenbergOneParameter (v : HeisenbergPoint) : Multiplicative ℝ →* HeisenbergGroup where
  toFun t := ⟨Multiplicative.toAdd t * v.1, Multiplicative.toAdd t * v.2.1,
    Multiplicative.toAdd t * v.2.2 + (Multiplicative.toAdd t)^2 * (v.1 * v.2.1 / 2)⟩
  map_one' := by ext <;> simp
  map_mul' s t := by
    have h : Multiplicative.toAdd (s * t) = Multiplicative.toAdd s + Multiplicative.toAdd t := rfl
    ext <;> simp only [h, HeisenbergGroup.mul_x, HeisenbergGroup.mul_y,
      HeisenbergGroup.mul_z] <;> ring

theorem heisenbergOneParameter_smooth (v : HeisenbergPoint) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, HeisenbergPoint) ∞
      (fun t : ℝ => heisenbergOneParameter v (Multiplicative.ofAdd t)) := by
  apply ContMDiff.of_comp_isOpenEmbedding HeisenbergGroup.coordinatesHomeomorph.isOpenEmbedding
  exact (show ContDiff ℝ ∞ (fun t : ℝ =>
    (t * v.1, t * v.2.1, t * v.2.2 + t^2 * (v.1 * v.2.1 / 2))) from by fun_prop).contMDiff

theorem heisenbergOneParameter_velocity (v : HeisenbergPoint) :
    HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, HeisenbergPoint)
      (fun t : ℝ => heisenbergOneParameter v (Multiplicative.ofAdd t)) 0
      ((ContinuousLinearMap.id ℝ ℝ).smulRight v) := by
  apply hasMFDerivAt_of_global_coordinates HeisenbergGroup.coordinatesHomeomorph
  · exact (heisenbergOneParameter_smooth v).continuous
  · apply HasDerivAt.hasFDerivAt
    have hid := hasDerivAt_id' (0 : ℝ)
    have hx := hid.mul_const v.1
    have hy := hid.mul_const v.2.1
    have hz := (hid.mul_const v.2.2).add ((hid.pow 2).mul_const (v.1 * v.2.1 / 2))
    convert hx.prodMk (hy.prodMk hz) using 1
    simp

private def scalarSecondKindCoordinates : HeisenbergGroup ≃ (Fin 3 → ℝ) :=
  HeisenbergGroup.malcevCoordinates.trans scalarTangentCoordinates.toEquiv

private theorem scalarSecondKindCoordinates_apply (g : HeisenbergGroup) (i : Fin 3) :
    scalarSecondKindCoordinates g i = ![g.x, g.y, g.z - g.x * g.y] i := rfl

private theorem scalarTail_ideal (j : ℕ)
    (x y : GroupLieAlgebra 𝓘(ℝ, HeisenbergPoint) HeisenbergGroup)
    (hy : ∀ k : Fin 3, k.val < j → scalarBasis.repr y k = 0)
    (k : Fin 3) (hk : k.val < j) :
    scalarBasis.repr
      (⁅x, y⁆ : GroupLieAlgebra 𝓘(ℝ, HeisenbergPoint) HeisenbergGroup) k = 0 := by
  rw [heisenberg_groupLie_bracket, scalarBasis_repr]
  fin_cases k
  · rfl
  · rfl
  · change 2 < j at hk
    have h0 := hy 0 (by omega)
    have h1 := hy 1 (by omega)
    simp [scalarBasis_repr] at h0 h1
    simp [h0, h1]

private theorem scalarSecondKindCoordinates_lattice (g : HeisenbergGroup) :
    g ∈ HeisenbergGroup.lattice ↔ ∀ j : Fin 3, ∃ z : ℤ, scalarSecondKindCoordinates g j = z := by
  rw [HeisenbergGroup.mem_lattice_iff_integer_malcevCoordinates]
  constructor
  · rintro ⟨u, v, w, h⟩ i
    change ∃ z : ℤ, scalarTangentCoordinates (HeisenbergGroup.malcevCoordinates g) i = z
    rw [h]
    fin_cases i
    · exact ⟨u, rfl⟩
    · exact ⟨v, rfl⟩
    · exact ⟨w, rfl⟩
  · intro h
    obtain ⟨u, hu⟩ := h 0
    obtain ⟨v, hv⟩ := h 1
    obtain ⟨w, hw⟩ := h 2
    exact ⟨u, v, w, Prod.ext hu (Prod.ext hv hw)⟩

private theorem scalarFiltration_tail (i : ℕ) :
    ∃ j ≤ 3, ∀ g, g ∈ HeisenbergGroup.lowerCentral i ↔
    ∀ k : Fin 3, k.val < j → scalarSecondKindCoordinates g k = 0 := by
  rcases i with _ | _ | _ | i
  · exact ⟨0, by omega, fun g => ⟨fun _ _ h => (Nat.not_lt_zero _ h).elim,
      fun _ => Subgroup.mem_top g⟩⟩
  · exact ⟨0, by omega, fun g => ⟨fun _ _ h => (Nat.not_lt_zero _ h).elim,
      fun _ => Subgroup.mem_top g⟩⟩
  · refine ⟨2, by omega, ?_⟩
    intro g
    change (g.x = 0 ∧ g.y = 0) ↔ _
    constructor
    · rintro ⟨hx, hy⟩ k hk
      fin_cases k <;> simp [scalarSecondKindCoordinates_apply, hx, hy] at hk ⊢
    · intro h
      exact ⟨h 0 (by decide), h 1 (by decide)⟩
  · refine ⟨3, le_rfl, ?_⟩
    intro g
    change g ∈ (⊥ : Subgroup HeisenbergGroup) ↔ _
    rw [Subgroup.mem_bot]
    constructor
    · rintro rfl k _
      fin_cases k <;> simp [scalarSecondKindCoordinates_apply]
    · intro h
      apply scalarSecondKindCoordinates.injective
      funext k
      rw [h k k.isLt]
      fin_cases k <;> simp [scalarSecondKindCoordinates_apply]

/-- The rational Mal'cev basis in the order `(X,Y,Z)`. -/
def heisenbergLeibmanBasis : LeibmanMalcevBasis HeisenbergPoint HeisenbergGroup
    HeisenbergGroup.lattice HeisenbergGroup.lowerCentral 3 where
  basis := scalarBasis
  axis := fun j => heisenbergOneParameter (scalarBasis j)
  axis_smooth := fun j => heisenbergOneParameter_smooth (scalarBasis j)
  axis_velocity := fun j => heisenbergOneParameter_velocity (scalarBasis j)
  coordinates := scalarSecondKindCoordinates
  coordinates_factor g := by
    simpa [List.ofFn_succ, scalarBasis_apply, scalarSecondKindCoordinates_apply,
      heisenbergOneParameter, mul_assoc] using HeisenbergGroup.malcevCoordinates_factor g
  coordinates_lattice := scalarSecondKindCoordinates_lattice
  tail_ideal := scalarTail_ideal
  filtration_tail := scalarFiltration_tail

private theorem rationalHeightOne {a : ℝ} (h : a = 0 ∨ a = 1 ∨ a = -1) :
    ∃ c : ℚ, a = (c : ℝ) ∧ (c.num.natAbs : ℝ) ≤ 1 ∧ (c.den : ℝ) ≤ 1 := by
  rcases h with rfl | rfl | rfl
  · exact ⟨0, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨1, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨-1, by norm_num, by norm_num, by norm_num⟩

theorem heisenbergLeibmanBasis_rational : heisenbergLeibmanBasis.IsRational 1 := by
  intro i j k
  apply rationalHeightOne
  change scalarBasis.repr ⁅scalarBasis i, scalarBasis j⁆ k = 0 ∨ _
  simp only [heisenbergLeibmanBasis, heisenberg_groupLie_bracket,
    scalarBasis_repr, scalarBasis_apply]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num

@[simp] theorem heisenbergLeibmanBasis_coordinates (g : HeisenbergGroup) :
    heisenbergLeibmanBasis.coordinates g = ![g.x, g.y, g.z - g.x * g.y] := rfl

private def productTangentCoordinates (d : ℕ) :
    (HeisenbergPoint × ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ) :=
  if d = 1 then
    { toFun := fun p => ![p.1.1, p.1.2.1, p.2, p.1.2.2]
      invFun := fun v => ((v 0, v 1, v 3), v 2)
      left_inv := fun ⟨⟨_, _, _⟩, _⟩ => rfl
      right_inv := by intro v; funext i; fin_cases i <;> rfl
      map_add' := by intro p q; funext i; fin_cases i <;> rfl
      map_smul' := by intro a p; funext i; fin_cases i <;> rfl }
  else
    { toFun := fun p => ![p.1.1, p.1.2.1, p.1.2.2, p.2]
      invFun := fun v => ((v 0, v 1, v 2), v 3)
      left_inv := fun ⟨⟨_, _, _⟩, _⟩ => rfl
      right_inv := by intro v; funext i; fin_cases i <;> rfl
      map_add' := by intro p q; funext i; fin_cases i <;> rfl
      map_smul' := by intro a p; funext i; fin_cases i <;> rfl }

private def productBasis (d : ℕ) : Basis (Fin 4) ℝ
    (GroupLieAlgebra 𝓘(ℝ, HeisenbergPoint × ℝ) HeisenbergProductGroup) :=
  Basis.ofEquivFun (productTangentCoordinates d)

private theorem productBasis_repr (d : ℕ) (v : HeisenbergPoint × ℝ) (i : Fin 4) :
    (productBasis d).repr v i =
      (if d = 1 then ![v.1.1, v.1.2.1, v.2, v.1.2.2]
        else ![v.1.1, v.1.2.1, v.1.2.2, v.2]) i := by
  rw [productBasis, Basis.ofEquivFun_repr_apply]
  by_cases h : d = 1 <;>
    fin_cases i <;>
    simp [productTangentCoordinates, h]

private theorem productBasis_apply (d : ℕ) (i : Fin 4) :
    (productBasis d i : HeisenbergPoint × ℝ) =
      (if d = 1 then ![((1, 0, 0), 0), ((0, 1, 0), 0), ((0, 0, 0), 1), ((0, 0, 1), 0)]
        else ![((1, 0, 0), 0), ((0, 1, 0), 0), ((0, 0, 1), 0), ((0, 0, 0), 1)]) i := by
  simp only [productBasis, Basis.coe_ofEquivFun]
  by_cases h : d = 1 <;>
    simp only [productTangentCoordinates, h, if_true, if_false] <;>
    fin_cases i <;> rfl

/-- The one-parameter subgroup for a tangent vector of the product. -/
def heisenbergProductOneParameter (v : HeisenbergPoint × ℝ) :
    Multiplicative ℝ →* HeisenbergProductGroup where
  toFun t := (heisenbergOneParameter v.1 t, Multiplicative.ofAdd (Multiplicative.toAdd t * v.2))
  map_one' := by
    apply Prod.ext
    · exact map_one _
    · change (0 : ℝ) * v.2 = 0
      simp
  map_mul' s t := by
    apply Prod.ext
    · exact map_mul _ _ _
    · change (Multiplicative.toAdd s + Multiplicative.toAdd t) * v.2 =
        Multiplicative.toAdd s * v.2 + Multiplicative.toAdd t * v.2
      ring

theorem heisenbergProductOneParameter_smooth (v : HeisenbergPoint × ℝ) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, HeisenbergPoint × ℝ) ∞
      (fun t : ℝ => heisenbergProductOneParameter v (Multiplicative.ofAdd t)) := by
  apply ContMDiff.of_comp_isOpenEmbedding heisenbergProductCoordinatesHomeomorph.isOpenEmbedding
  exact (show ContDiff ℝ ∞ (fun t : ℝ =>
    ((t * v.1.1, t * v.1.2.1, t * v.1.2.2 + t^2 * (v.1.1 * v.1.2.1 / 2)), t * v.2))
    from by fun_prop).contMDiff

theorem heisenbergProductOneParameter_velocity (v : HeisenbergPoint × ℝ) :
    HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, HeisenbergPoint × ℝ)
      (fun t : ℝ => heisenbergProductOneParameter v (Multiplicative.ofAdd t)) 0
      ((ContinuousLinearMap.id ℝ ℝ).smulRight v) := by
  apply hasMFDerivAt_of_global_coordinates heisenbergProductCoordinatesHomeomorph
  · exact (heisenbergProductOneParameter_smooth v).continuous
  · apply HasDerivAt.hasFDerivAt
    have hid := hasDerivAt_id' (0 : ℝ)
    have hx := hid.mul_const v.1.1
    have hy := hid.mul_const v.1.2.1
    have hz := (hid.mul_const v.1.2.2).add ((hid.pow 2).mul_const (v.1.1 * v.1.2.1 / 2))
    have hu := hid.mul_const v.2
    convert (hx.prodMk (hy.prodMk hz)).prodMk hu using 1
    simp

private def productSecondKindCoordinates (d : ℕ) : HeisenbergProductGroup ≃ (Fin 4 → ℝ) :=
  (HeisenbergGroup.malcevCoordinates.prodCongr Multiplicative.toAdd).trans
    (productTangentCoordinates d).toEquiv

private theorem productSecondKindCoordinates_apply (d : ℕ) (g : HeisenbergProductGroup)
    (i : Fin 4) :
    productSecondKindCoordinates d g i =
      (if d = 1 then ![g.1.x, g.1.y, Multiplicative.toAdd g.2, g.1.z - g.1.x * g.1.y]
        else ![g.1.x, g.1.y, g.1.z - g.1.x * g.1.y, Multiplicative.toAdd g.2]) i := by
  exact productBasis_repr d (HeisenbergGroup.malcevCoordinates g.1, Multiplicative.toAdd g.2) i

private theorem productTail_ideal (d j : ℕ)
    (x y : GroupLieAlgebra 𝓘(ℝ, HeisenbergPoint × ℝ) HeisenbergProductGroup)
    (hy : ∀ k : Fin 4, k.val < j → (productBasis d).repr y k = 0)
    (k : Fin 4) (hk : k.val < j) :
    (productBasis d).repr (⁅x, y⁆ :
      GroupLieAlgebra 𝓘(ℝ, HeisenbergPoint × ℝ) HeisenbergProductGroup) k = 0 := by
  rw [heisenbergProduct_groupLie_bracket, productBasis_repr]
  fin_cases k <;> by_cases hd : d = 1 <;> simp [hd]
  all_goals
    first | change 2 < j at hk | change 3 < j at hk
    have h0 := hy 0 (by omega)
    have h1 := hy 1 (by omega)
    simp [productBasis_repr, hd] at h0 h1
    simp [h0, h1]

private theorem productSecondKindCoordinates_lattice (d : ℕ) (g : HeisenbergProductGroup) :
    g ∈ heisenbergProductLattice ↔ ∀ j : Fin 4, ∃ z : ℤ, productSecondKindCoordinates d g j = z := by
  rw [heisenbergProductLattice_mem_iff, scalarSecondKindCoordinates_lattice]
  by_cases hd : d = 1
  · simp only [productSecondKindCoordinates_apply, if_pos hd, scalarSecondKindCoordinates_apply]
    constructor
    · rintro ⟨hg, b, hb⟩ i
      fin_cases i
      · exact hg 0
      · exact hg 1
      · exact ⟨b, hb⟩
      · exact hg 2
    · intro hg
      refine ⟨?_, hg 2⟩
      intro i
      fin_cases i
      · exact hg 0
      · exact hg 1
      · exact hg 3
  · simp only [productSecondKindCoordinates_apply, if_neg hd, scalarSecondKindCoordinates_apply]
    constructor
    · rintro ⟨hg, b, hb⟩ i
      fin_cases i
      · exact hg 0
      · exact hg 1
      · exact hg 2
      · exact ⟨b, hb⟩
    · intro hg
      refine ⟨?_, hg 3⟩
      intro i
      fin_cases i
      · exact hg 0
      · exact hg 1
      · exact hg 2

private theorem productSecondKindCoordinates_factor (d : ℕ) (g : HeisenbergProductGroup) :
    (List.ofFn (fun j : Fin 4 => heisenbergProductOneParameter (productBasis d j)
      (Multiplicative.ofAdd (productSecondKindCoordinates d g j)))).prod = g := by
  by_cases hd : d = 1 <;>
    apply Prod.ext
  all_goals
    simp [List.ofFn_succ, hd, productBasis_apply, productSecondKindCoordinates_apply,
      heisenbergProductOneParameter, heisenbergOneParameter, mul_assoc]
  all_goals first
    | exact HeisenbergGroup.malcevCoordinates_factor g.1
    | rw [← HeisenbergGroup.malcevCoordinates_factor g.1]
      simp [mul_assoc]; rfl

private theorem productFiltration_tail (d : ℕ) (hd : 0 < d) (i : ℕ) :
    ∃ j ≤ 4, ∀ g, g ∈ heisenbergProductFiltration d i ↔
      ∀ k : Fin 4, k.val < j → productSecondKindCoordinates d g k = 0 := by
  rcases i with _ | _ | _ | i
  · refine ⟨0, by omega, fun g => ?_⟩
    simp [heisenbergProductFiltration, HeisenbergGroup.lowerCentral, realDegreeFiltration]
  · refine ⟨0, by omega, fun g => ?_⟩
    simp [heisenbergProductFiltration, HeisenbergGroup.lowerCentral, realDegreeFiltration,
      Nat.succ_le_iff.mpr hd]
  · by_cases h : d = 1
    · subst d
      refine ⟨3, by omega, ?_⟩
      intro g
      change (g.1.x = 0 ∧ g.1.y = 0) ∧
        g.2 ∈ realDegreeFiltration 1 2 ↔ _
      rw [realDegreeFiltration, if_neg (by decide : ¬ 2 ≤ 1), Subgroup.mem_bot]
      constructor
      · rintro ⟨⟨hx, hy⟩, hu⟩ k hk
        fin_cases k <;> simp [productSecondKindCoordinates_apply, hx, hy, hu] at hk ⊢
      · intro hg
        exact ⟨⟨hg 0 (by decide), hg 1 (by decide)⟩, hg 2 (by decide)⟩
    · have h₂ : 2 ≤ d := by omega
      refine ⟨2, by omega, ?_⟩
      intro g
      change (g.1.x = 0 ∧ g.1.y = 0) ∧ g.2 ∈ realDegreeFiltration d 2 ↔ _
      rw [realDegreeFiltration, if_pos h₂]
      constructor
      · rintro ⟨⟨hx, hy⟩, _⟩ k hk
        fin_cases k <;> simp [productSecondKindCoordinates_apply, h, hx, hy] at hk ⊢
      · intro hg
        exact ⟨⟨(by simpa [productSecondKindCoordinates_apply, h] using hg 0 (by decide)),
          (by simpa [productSecondKindCoordinates_apply, h] using hg 1 (by decide))⟩,
          Subgroup.mem_top _⟩
  · by_cases hid : i + 3 ≤ d
    · have h : d ≠ 1 := by omega
      refine ⟨3, by omega, ?_⟩
      intro g
      change g.1 ∈ (⊥ : Subgroup HeisenbergGroup) ∧
        g.2 ∈ realDegreeFiltration d (i + 3) ↔ _
      rw [realDegreeFiltration, if_pos hid, Subgroup.mem_bot]
      constructor
      · rintro ⟨hg, _⟩ k hk
        fin_cases k <;> simp [productSecondKindCoordinates_apply, h, hg] at hk ⊢
      · intro hg
        refine ⟨scalarSecondKindCoordinates.injective ?_, Subgroup.mem_top _⟩
        funext k
        fin_cases k
        · simpa [scalarSecondKindCoordinates_apply, productSecondKindCoordinates_apply, h]
            using hg 0 (by decide)
        · simpa [scalarSecondKindCoordinates_apply, productSecondKindCoordinates_apply, h]
            using hg 1 (by decide)
        · simpa [scalarSecondKindCoordinates_apply, productSecondKindCoordinates_apply, h]
            using hg 2 (by decide)
    · refine ⟨4, le_rfl, ?_⟩
      intro g
      rw [heisenbergProductFiltration_eq_bot (by omega), Subgroup.mem_bot]
      constructor
      · rintro rfl k _
        fin_cases k <;> by_cases h : d = 1 <;> simp [productSecondKindCoordinates_apply, h]
      · intro hg
        apply (productSecondKindCoordinates d).injective
        funext k
        rw [hg k k.isLt]
        fin_cases k <;> by_cases h : d = 1 <;> simp [productSecondKindCoordinates_apply, h]

/-- The product rational Mal'cev basis in degree one or in larger degree. -/
def heisenbergProductLeibmanBasis (d : ℕ) (hd : 0 < d) :
    LeibmanMalcevBasis (HeisenbergPoint × ℝ) HeisenbergProductGroup
      heisenbergProductLattice (heisenbergProductFiltration d) 4 where
  basis := productBasis d
  axis := fun j => heisenbergProductOneParameter (productBasis d j)
  axis_smooth := fun j => heisenbergProductOneParameter_smooth (productBasis d j)
  axis_velocity := fun j => heisenbergProductOneParameter_velocity (productBasis d j)
  coordinates := productSecondKindCoordinates d
  coordinates_factor := productSecondKindCoordinates_factor d
  coordinates_lattice := productSecondKindCoordinates_lattice d
  tail_ideal := productTail_ideal d
  filtration_tail := productFiltration_tail d hd

private theorem productHorizontalBasisComponents (d : ℕ) (i : Fin 4) :
    ((productBasis d i).1.1 = 0 ∨ (productBasis d i).1.1 = 1) ∧
      ((productBasis d i).1.2.1 = 0 ∨ (productBasis d i).1.2.1 = 1) := by
  rw [productBasis_apply]
  by_cases h : d = 1 <;> fin_cases i <;> norm_num [h]

theorem heisenbergProductLeibmanBasis_rational (d : ℕ) (hd : 0 < d) :
    (heisenbergProductLeibmanBasis d hd).IsRational 1 := by
  intro i j k
  apply rationalHeightOne
  let a : HeisenbergPoint × ℝ := productBasis d i
  let b : HeisenbergPoint × ℝ := productBasis d j
  let c := a.1.1 * b.1.2.1 - b.1.1 * a.1.2.1
  have hc : c = 0 ∨ c = 1 ∨ c = -1 := by
    obtain ⟨ha, ha'⟩ := productHorizontalBasisComponents d i
    obtain ⟨hb, hb'⟩ := productHorizontalBasisComponents d j
    change (a.1.1 = 0 ∨ a.1.1 = 1) at ha
    change (a.1.2.1 = 0 ∨ a.1.2.1 = 1) at ha'
    change (b.1.1 = 0 ∨ b.1.1 = 1) at hb
    change (b.1.2.1 = 0 ∨ b.1.2.1 = 1) at hb'
    rcases ha with ha | ha <;> rcases ha' with ha' | ha' <;>
      rcases hb with hb | hb <;> rcases hb' with hb' | hb' <;>
      norm_num [c, ha, ha', hb, hb']
  have heq : (heisenbergProductLeibmanBasis d hd).basis.repr
      ⁅(heisenbergProductLeibmanBasis d hd).basis i,
        (heisenbergProductLeibmanBasis d hd).basis j⁆ k =
      (if d = 1 then ![0, 0, 0, c] else ![0, 0, c, 0]) k := by
    change (productBasis d).repr ⁅productBasis d i, productBasis d j⁆ k = _
    rw [heisenbergProduct_groupLie_bracket, productBasis_repr]
  rw [heq]
  by_cases h : d = 1 <;> fin_cases k <;> simp [h, hc]

theorem heisenbergProductLeibmanBasis_coordinates (d : ℕ) (hd : 0 < d)
    (g : HeisenbergProductGroup) :
    let p := heisenbergProductMalcevCoordinates d g
    (heisenbergProductLeibmanBasis d hd).coordinates g = ![p.1, p.2.1, p.2.2.1, p.2.2.2] := by
  dsimp
  change productSecondKindCoordinates d g = _
  funext i
  rw [productSecondKindCoordinates_apply]
  by_cases h : d = 1 <;>
    simp [heisenbergProductMalcevCoordinates, ne_of_gt hd, h]

end

end NilBohr
