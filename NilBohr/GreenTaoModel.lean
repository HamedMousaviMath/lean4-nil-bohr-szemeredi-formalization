import NilBohr.OrbitEquidistribution
import NilBohr.PolynomialGowers
import Mathlib.Algebra.Group.MinimalAxioms

/-! Concrete algebra for the Heisenberg and product instances of the one-parameter
quantitative Leibman theorem. Its metric and Haar input are separate from
the group filtration and polynomial membership established here. -/

open Polynomial MeasureTheory

namespace NilBohr

noncomputable section

/-- The multiplication on real upper-triangular unipotent matrices, written
in the same order (x,y,z) as the existing orbit model. -/
@[ext] structure HeisenbergGroup where
  x : ℝ
  y : ℝ
  z : ℝ

namespace HeisenbergGroup

instance : One HeisenbergGroup := ⟨⟨0, 0, 0⟩⟩

instance : Mul HeisenbergGroup :=
  ⟨fun g h => ⟨g.x + h.x, g.y + h.y, g.z + h.z + g.x * h.y⟩⟩

instance : Inv HeisenbergGroup :=
  ⟨fun g => ⟨-g.x, -g.y, -g.z + g.x * g.y⟩⟩

@[simp] theorem one_x : (1 : HeisenbergGroup).x = 0 := rfl
@[simp] theorem one_y : (1 : HeisenbergGroup).y = 0 := rfl
@[simp] theorem one_z : (1 : HeisenbergGroup).z = 0 := rfl
@[simp] theorem mul_x (g h : HeisenbergGroup) : (g * h).x = g.x + h.x := rfl
@[simp] theorem mul_y (g h : HeisenbergGroup) : (g * h).y = g.y + h.y := rfl
@[simp] theorem mul_z (g h : HeisenbergGroup) : (g * h).z = g.z + h.z + g.x * h.y := rfl
@[simp] theorem inv_x (g : HeisenbergGroup) : g⁻¹.x = -g.x := rfl
@[simp] theorem inv_y (g : HeisenbergGroup) : g⁻¹.y = -g.y := rfl
@[simp] theorem inv_z (g : HeisenbergGroup) : g⁻¹.z = -g.z + g.x * g.y := rfl

instance : Group HeisenbergGroup :=
  Group.ofLeftAxioms
    (fun g h k => by ext <;> simp <;> ring)
    (fun g => by ext <;> simp)
    (fun g => by ext <;> simp)

/-- Identification with the coordinate points used in the manuscript. -/
def coordinates : HeisenbergGroup ≃ HeisenbergPoint where
  toFun g := (g.x, g.y, g.z)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv g := by cases g; rfl
  right_inv p := by rcases p with ⟨x, y, z⟩; rfl

@[simp] theorem coordinates_mul (g h : HeisenbergGroup) :
    coordinates (g * h) = heisenbergMul (coordinates g) (coordinates h) := rfl

@[simp] theorem coordinates_inv (g : HeisenbergGroup) :
    coordinates g⁻¹ = heisenbergInv (coordinates g) := rfl

/-- The lattice consists of integer matrix coordinates. -/
def lattice : Subgroup HeisenbergGroup where
  carrier := {g | ∃ u v w : ℤ, g = ⟨u, v, w⟩}
  one_mem' := ⟨0, 0, 0, by ext <;> simp⟩
  mul_mem' := by
    rintro _ _ ⟨u, v, w, rfl⟩ ⟨u', v', w', rfl⟩
    exact ⟨u + u', v + v', w + w' + u * v', by ext <;> push_cast <;> rfl⟩
  inv_mem' := by
    rintro _ ⟨u, v, w, rfl⟩
    exact ⟨-u, -v, -w + u * v, by ext <;> push_cast <;> rfl⟩

/-- The central `z` axis. -/
def centralAxis : Subgroup HeisenbergGroup where
  carrier := {g | g.x = 0 ∧ g.y = 0}
  one_mem' := by simp
  mul_mem' := by
    rintro a b ⟨ax, ay⟩ ⟨bx, by'⟩
    exact ⟨by simp [ax, bx], by simp [ay, by']⟩
  inv_mem' := by
    rintro a ⟨ax, ay⟩
    exact ⟨by simp [ax], by simp [ay]⟩

theorem commutator_coordinates (g h : HeisenbergGroup) :
    g * h * g⁻¹ * h⁻¹ = ⟨0, 0, g.x * h.y - h.x * g.y⟩ := by
  ext <;> simp
  ring

theorem commutator_mem_centralAxis (g h : HeisenbergGroup) :
    g * h * g⁻¹ * h⁻¹ ∈ centralAxis := by
  rw [commutator_coordinates]
  exact ⟨rfl, rfl⟩

theorem commute_centralAxis (g : HeisenbergGroup) {h : HeisenbergGroup} (hh : h ∈ centralAxis) :
    Commute g h := by
  rcases hh with ⟨hx, hy⟩
  change g * h = h * g
  ext <;> simp [hx, hy, add_comm]

/-- Lower central filtration with both `G₀` and `G₁` equal to the full group. -/
def lowerCentral : ℕ → Subgroup HeisenbergGroup
  | 0 => ⊤
  | 1 => ⊤
  | 2 => centralAxis
  | _ + 3 => ⊥

theorem lowerCentral_antitone : Antitone lowerCentral := by
  intro i j hij
  rcases i with _ | _ | _ | i <;> rcases j with _ | _ | _ | j <;> simp_all [lowerCentral]

theorem commutator_mem_lowerCentral {i j : ℕ} {g h : HeisenbergGroup}
    (hg : g ∈ lowerCentral i) (hh : h ∈ lowerCentral j) :
    g * h * g⁻¹ * h⁻¹ ∈ lowerCentral (i + j) := by
  rcases i with _ | _ | _ | i <;> rcases j with _ | _ | _ | j
  all_goals first
    | exact Subgroup.mem_top _
    | exact commutator_mem_centralAxis _ _
    | have h1 : h = 1 := Subgroup.mem_bot.mp hh
      simp [h1]
    | have g1 : g = 1 := Subgroup.mem_bot.mp hg
      simp [g1]
    | rw [(commute_centralAxis g hh).eq]
      simp
    | rw [← (commute_centralAxis h hg).eq]
      simp
  all_goals exact Subgroup.one_mem _

/-- Coordinates of the second kind. In the product of the three axes,
the first two axes contribute an extra (xy) to the third coordinate. -/
def malcevCoordinates : HeisenbergGroup ≃ HeisenbergPoint where
  toFun g := (g.x, g.y, g.z - g.x * g.y)
  invFun p := ⟨p.1, p.2.1, p.2.2 + p.1 * p.2.1⟩
  left_inv g := by ext <;> simp
  right_inv p := by rcases p with ⟨x, y, z⟩; simp

theorem malcevCoordinates_factor (g : HeisenbergGroup) :
    (⟨g.x, 0, 0⟩ : HeisenbergGroup) * ⟨0, g.y, 0⟩ * ⟨0, 0, g.z - g.x * g.y⟩ = g := by
  ext <;> simp

theorem mem_lattice_iff_integer_malcevCoordinates (g : HeisenbergGroup) :
    g ∈ lattice ↔ ∃ u v w : ℤ, malcevCoordinates g = ((u : ℝ), (v : ℝ), (w : ℝ)) := by
  constructor
  · rintro ⟨u, v, w, rfl⟩
    exact ⟨u, v, w - u * v, by simp [malcevCoordinates]⟩
  · rintro ⟨u, v, w, h⟩
    refine ⟨u, v, w + u * v, ?_⟩
    apply malcevCoordinates.injective
    rw [h]
    simp [malcevCoordinates]

theorem malcevCoordinates_norm (g : HeisenbergGroup) :
    max |(malcevCoordinates g).1|
      (max |(malcevCoordinates g).2.1| |(malcevCoordinates g).2.2|) =
      heisenbergMalcevNorm (coordinates g) := rfl

/-- A representative in the unit cube in matrix coordinates, obtained by
right multiplication by a lattice element. -/
def unitChart (g : HeisenbergGroup) : HeisenbergGroup :=
  ⟨Int.fract g.x, Int.fract g.y, Int.fract (g.z - g.x * ⌊g.y⌋)⟩

theorem unitChart_coordinates (g : HeisenbergGroup) :
    unitChart g = g * ⟨(-⌊g.x⌋ : ℤ), (-⌊g.y⌋ : ℤ), (-⌊g.z - g.x * ⌊g.y⌋⌋ : ℤ)⟩ := by
  ext <;> simp only [unitChart, Int.fract, mul_x, mul_y, mul_z, Int.cast_neg] <;> ring

theorem unitChart_mem_cube (g : HeisenbergGroup) :
    (unitChart g).x ∈ Set.Ico 0 1 ∧ (unitChart g).y ∈ Set.Ico 0 1 ∧
      (unitChart g).z ∈ Set.Ico 0 1 :=
  ⟨⟨Int.fract_nonneg _, Int.fract_lt_one _⟩, ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩,
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩⟩

theorem unitChart_of_mem_cube {g : HeisenbergGroup}
    (hx : g.x ∈ Set.Ico 0 1) (hy : g.y ∈ Set.Ico 0 1) (hz : g.z ∈ Set.Ico 0 1) :
    unitChart g = g := by
  have hyf : ⌊g.y⌋ = 0 := Int.floor_eq_zero_iff.mpr hy
  ext <;> simp [unitChart, hyf, Int.fract_eq_self.mpr hx,
    Int.fract_eq_self.mpr hy, Int.fract_eq_self.mpr hz]

theorem unitChart_mul_lattice (g : HeisenbergGroup) {h : HeisenbergGroup} (hh : h ∈ lattice) :
    unitChart (g * h) = unitChart g := by
  rcases hh with ⟨u, v, w, rfl⟩
  have hh := heisenberg_chart_right_lattice (coordinates g) u v w
  exact HeisenbergGroup.ext (Int.fract_add_intCast g.x u) hh.1 hh.2

/-- Each right coset has exactly one representative in the half-open cube. -/
theorem existsUnique_cube_representative (g : HeisenbergGroup) :
    ∃! h : HeisenbergGroup, (∃ γ ∈ lattice, h = g * γ) ∧
      h.x ∈ Set.Ico 0 1 ∧ h.y ∈ Set.Ico 0 1 ∧ h.z ∈ Set.Ico 0 1 := by
  refine ⟨unitChart g, ⟨?_, unitChart_mem_cube g⟩, ?_⟩
  · exact ⟨_, ⟨_, _, _, rfl⟩, unitChart_coordinates g⟩
  · rintro h ⟨⟨γ, hγ, heq⟩, hx, hy, hz⟩
    rw [← unitChart_of_mem_cube hx hy hz, heq, unitChart_mul_lattice g hγ]

/-- A coordinate linear form descends to the circle and annihilates the integer lattice. -/
noncomputable def horizontalCharacter (k l : ℤ) : HeisenbergGroup →* Multiplicative Circle where
  toFun g := Multiplicative.ofAdd ((k * g.x + l * g.y : ℝ) : Circle)
  map_one' := by
    change (((k : ℝ) * (1 : HeisenbergGroup).x + l * (1 : HeisenbergGroup).y : ℝ) : Circle) = 0
    simp
  map_mul' g h := by
    change Multiplicative.ofAdd ((k * (g * h).x + l * (g * h).y : ℝ) : Circle) =
      Multiplicative.ofAdd (((k * g.x + l * g.y : ℝ) : Circle) + ((k * h.x + l * h.y : ℝ) : Circle))
    rw [mul_x, mul_y, ← AddCircle.coe_add]
    congr 2
    ring

theorem horizontalCharacter_of_lattice (k l : ℤ) {g : HeisenbergGroup} (hg : g ∈ lattice) :
    horizontalCharacter k l g = 1 := by
  rcases hg with ⟨u, v, w, rfl⟩
  change Multiplicative.ofAdd ((k * (u : ℝ) + l * (v : ℝ) : ℝ) : Circle) = Multiplicative.ofAdd 0
  congr 1
  apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).2
  exact ⟨k * u + l * v, by simp⟩

/-- Every circle-valued character is trivial on the central axis, since
every element of that axis is a single commutator. -/
theorem character_eq_one_centralAxis (η : HeisenbergGroup →* Multiplicative Circle) (t : ℝ) :
    η ⟨0, 0, t⟩ = 1 := by
  let g : HeisenbergGroup := ⟨t, 0, 0⟩
  let h : HeisenbergGroup := ⟨0, 1, 0⟩
  have heq : g * h * g⁻¹ * h⁻¹ = (⟨0, 0, t⟩ : HeisenbergGroup) := by
    rw [commutator_coordinates]
    simp [g, h]
  rw [← heq]
  simp only [map_mul, map_inv]
  rw [mul_right_comm (η g) (η h) (η g)⁻¹, mul_inv_cancel, one_mul, mul_inv_cancel]

/-- The central coefficient of a character in Mal'cev coordinates is zero.
The linear-coordinate premise is precisely the representation of a
horizontal character in Green–Tao Definition 2.6. -/
theorem character_central_coefficient_eq_zero (η : HeisenbergGroup →* Multiplicative Circle)
    (kx ky kz : ℤ) (hη : ∀ g, η g = Multiplicative.ofAdd
      (((kx : ℝ) * g.x + (ky : ℝ) * g.y + (kz : ℝ) * (g.z - g.x * g.y) : ℝ) : Circle)) :
    kz = 0 := by
  by_contra hne
  have hne' : (kz : ℝ) ≠ 0 := by exact_mod_cast hne
  have ht := character_eq_one_centralAxis η (1 / (2 * (kz : ℝ)))
  rw [hη] at ht
  change ((((kx : ℝ) * 0 + (ky : ℝ) * 0 + (kz : ℝ) *
    ((1 / (2 * (kz : ℝ))) - 0 * 0) : ℝ) : Circle) = 0) at ht
  have hhalf : (kz : ℝ) * (1 / (2 * (kz : ℝ))) = 1 / 2 := by
    field_simp
    ring
  have hz : ((1 / 2 : ℝ) : Circle) = 0 := by
    simpa only [mul_zero, zero_add, sub_zero, hhalf] using ht
  obtain ⟨j, hj⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).1 hz
  simp at hj
  have hj₀ : 0 < j := by exact_mod_cast (show (0 : ℝ) < (j : ℝ) by linarith)
  have hj₁ : j < 1 := by exact_mod_cast (show (j : ℝ) < 1 by linarith)
  omega

end HeisenbergGroup


/-- Iterated left forward differences in Green–Tao Definition 6.1.
The first entry of the list is the first shift applied. -/
def nilpotentDifferences {G : Type*} [Group G] : List ℤ → (ℤ → G) → (ℤ → G)
  | [], f => f
  | h :: shifts, f => nilpotentDifferences shifts (fun n => f (n + h) * (f n)⁻¹)

/-- The subgroup-valued condition of Green–Tao Definition 6.1, for
one integer parameter. -/
def IsFilteredPolynomial {G : Type*} [Group G] (F : ℕ → Subgroup G) (g : ℤ → G) : Prop :=
  ∀ (shifts : List ℤ) (n : ℤ), nilpotentDifferences shifts g n ∈ F shifts.length

private theorem nilpotentDifferences_const_of_nonempty {G : Type*} [Group G]
    {shifts : List ℤ} (hs : shifts ≠ []) (a : G) (n : ℤ) :
    nilpotentDifferences shifts (fun _ => a) n = 1 := by
  induction shifts generalizing a with
  | nil => contradiction
  | cons h shifts ih =>
    simp only [nilpotentDifferences, mul_inv_cancel]
    by_cases hshifts : shifts = []
    · simp [hshifts, nilpotentDifferences]
    · exact ih hshifts 1

namespace HeisenbergGroup

/-- The coordinate dilation preserves the Heisenberg group law for every
nonzero real scaling parameter. -/
theorem dilatedOrbit_add (α β : ℝ) (s : ℕ) (hs : s ≠ 0) (m n : ℤ) :
    coordinates.symm (dilatedHeisenbergOrbit α β s (m + n)) =
      coordinates.symm (dilatedHeisenbergOrbit α β s m) *
        coordinates.symm (dilatedHeisenbergOrbit α β s n) := by
  have hs' : (s : ℝ) ≠ 0 := by exact_mod_cast hs
  rw [dilatedHeisenbergOrbit, heisenbergOrbit_add]
  ext <;> simp [dilatedHeisenbergOrbit, coordinates, heisenbergMul]
  all_goals field_simp
  all_goals ring

theorem dilatedProgression_isFilteredPolynomial (α β : ℝ) (s : ℕ) (hs : s ≠ 0)
    (a v : ℤ) :
    IsFilteredPolynomial lowerCentral
      (fun n => coordinates.symm (dilatedHeisenbergOrbit α β s (a + v * n))) := by
  intro shifts n
  rcases shifts with _ | ⟨h, shifts⟩
  · exact Subgroup.mem_top _
  have hDiff : (fun n => coordinates.symm (dilatedHeisenbergOrbit α β s (a + v * (n + h))) *
      (coordinates.symm (dilatedHeisenbergOrbit α β s (a + v * n)))⁻¹) =
        fun _ => coordinates.symm (dilatedHeisenbergOrbit α β s (v * h)) := by
    funext n
    rw [show a + v * (n + h) = v * h + (a + v * n) by ring,
      dilatedOrbit_add α β s hs]
    simp
  simp only [nilpotentDifferences, hDiff]
  by_cases hshifts : shifts = []
  · subst shifts
    exact Subgroup.mem_top _
  · rw [nilpotentDifferences_const_of_nonempty hshifts]
    exact Subgroup.one_mem _

end HeisenbergGroup

/-- The filtration on the real line before dividing by the integer lattice.
The full real line occurs at every index through the degree. -/
def realDegreeFiltration (d i : ℕ) : Subgroup (Multiplicative ℝ) :=
  if i ≤ d then ⊤ else ⊥

/-- The adapted product filtration has degree `max 2 d`. -/
def heisenbergProductFiltration (d i : ℕ) :
    Subgroup (HeisenbergGroup × Multiplicative ℝ) :=
  (HeisenbergGroup.lowerCentral i).prod (realDegreeFiltration d i)

theorem heisenbergProductFiltration_antitone (d : ℕ) :
    Antitone (heisenbergProductFiltration d) := by
  intro i j hij g hg
  refine ⟨HeisenbergGroup.lowerCentral_antitone hij hg.1, ?_⟩
  by_cases hj : j ≤ d
  · simp [realDegreeFiltration, hij.trans hj]
  · have h : g.2 = 1 := by
      have hg₂ := hg.2
      simpa [realDegreeFiltration, hj] using hg₂
    rw [h]
    exact Subgroup.one_mem _

theorem commutator_mem_heisenbergProductFiltration {d i j : ℕ}
    {g h : HeisenbergGroup × Multiplicative ℝ}
    (hg : g ∈ heisenbergProductFiltration d i) (hh : h ∈ heisenbergProductFiltration d j) :
    g * h * g⁻¹ * h⁻¹ ∈ heisenbergProductFiltration d (i + j) := by
  refine ⟨HeisenbergGroup.commutator_mem_lowerCentral hg.1 hh.1, ?_⟩
  change g.2 * h.2 * g.2⁻¹ * h.2⁻¹ ∈ realDegreeFiltration d (i + j)
  rw [mul_right_comm g.2 h.2 g.2⁻¹, mul_inv_cancel, one_mul, mul_inv_cancel]
  exact Subgroup.one_mem _

theorem heisenbergProductFiltration_eq_bot {d i : ℕ} (hi : max 2 d < i) :
    heisenbergProductFiltration d i = ⊥ := by
  have hid : ¬i ≤ d := by omega
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 3 := ⟨i - 3, by omega⟩
  simp [heisenbergProductFiltration, HeisenbergGroup.lowerCentral, realDegreeFiltration, hid]

private theorem nilpotentDifferences_prod {G H : Type*} [Group G] [Group H]
    (shifts : List ℤ) (f : ℤ → G) (g : ℤ → H) (n : ℤ) :
    nilpotentDifferences shifts (fun t => (f t, g t)) n =
      (nilpotentDifferences shifts f n, nilpotentDifferences shifts g n) := by
  induction shifts generalizing f g with
  | nil => rfl
  | cons h shifts ih =>
    simp only [nilpotentDifferences]
    exact ih (fun t => f (t + h) * (f t)⁻¹) (fun t => g (t + h) * (g t)⁻¹)

private theorem nilpotentDifferences_polynomial_eq_one (p : Polynomial ℝ) (shifts : List ℤ)
    (hp : p.degree < (shifts.length : WithBot ℕ)) (n : ℤ) :
    nilpotentDifferences shifts (fun t => Multiplicative.ofAdd (p.eval (t : ℝ))) n = 1 := by
  induction shifts generalizing p with
  | nil =>
    by_cases hz : p = 0
    · simp [hz, nilpotentDifferences]
    · rw [degree_eq_natDegree hz] at hp
      change (p.natDegree : WithBot ℕ) < ((0 : ℕ) : WithBot ℕ) at hp
      exact (Nat.not_lt_zero _ (WithBot.coe_lt_coe.mp hp)).elim
  | cons h shifts ih =>
    let Δ := p.comp (X + C (h : ℝ)) - p
    have hΔ : Δ.degree < (shifts.length : WithBot ℕ) := by
      by_cases hz : p = 0
      · simp only [Δ, hz, zero_comp, sub_self, degree_zero]
        exact WithBot.bot_lt_coe _
      · have hdeg : Δ.degree < p.degree := by
          rw [show Δ = -(p - p.comp (X + C (h : ℝ))) by dsimp [Δ]; abel, degree_neg]
          exact degree_sub_translate_lt hz _
        rw [degree_eq_natDegree hz] at hp hdeg
        apply hdeg.trans_le
        change (p.natDegree : WithBot ℕ) ≤ (shifts.length : WithBot ℕ)
        norm_cast at hp ⊢
        exact Nat.lt_succ_iff.mp hp
    have hFun : (fun t : ℤ => Multiplicative.ofAdd (p.eval ((t + h : ℤ) : ℝ)) *
      (Multiplicative.ofAdd (p.eval (t : ℝ)))⁻¹) =
        (fun t : ℤ => Multiplicative.ofAdd (Δ.eval (t : ℝ))) := by
      funext t
      change Multiplicative.ofAdd (p.eval ((t + h : ℤ) : ℝ) + -p.eval (t : ℝ)) = _
      congr 1
      simp [Δ, eval_comp, sub_eq_add_neg]
    simp only [nilpotentDifferences, hFun]
    exact ih Δ hΔ

/-- Ordinary polynomial phase coordinates satisfy the filtered group
polynomial definition, including for negative integer indices and shifts. -/
theorem polynomial_isFilteredPolynomial {d : ℕ} {p : Polynomial ℝ} (hp : p.natDegree ≤ d) :
    IsFilteredPolynomial (realDegreeFiltration d)
      (fun t => Multiplicative.ofAdd (p.eval (t : ℝ))) := by
  intro shifts t
  by_cases h : shifts.length ≤ d
  · simp [realDegreeFiltration, h]
  · rw [nilpotentDifferences_polynomial_eq_one p shifts ?_]
    · exact Subgroup.one_mem _
    · exact degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr (hp.trans_lt (lt_of_not_ge h)))

/-- Filtered polynomial membership of the exact product orbit needed for
the twisted Green–Tao obstruction. -/
theorem heisenbergProductOrbit_isFilteredPolynomial (α β : ℝ) (s : ℕ) (hs : s ≠ 0)
    (a v : ℤ) {d : ℕ} {p : Polynomial ℝ} (hp : p.natDegree ≤ d) :
    IsFilteredPolynomial (heisenbergProductFiltration d)
      (fun n => (HeisenbergGroup.coordinates.symm (dilatedHeisenbergOrbit α β s (a + v * n)),
        Multiplicative.ofAdd (p.eval (n : ℝ)))) := by
  intro shifts n
  rw [nilpotentDifferences_prod]
  exact ⟨HeisenbergGroup.dilatedProgression_isFilteredPolynomial α β s hs a v shifts n,
    polynomial_isFilteredPolynomial hp shifts n⟩

/-- The four Mal'cev coordinates in the order adapted to the product
filtration. The real line comes first in degree zero and last in degree
two and above. In degree one the Heisenberg centre comes last. -/
def heisenbergProductMalcevCoordinates (d : ℕ) (g : HeisenbergGroup × Multiplicative ℝ) :
    ℝ × ℝ × ℝ × ℝ :=
  if d = 0 then (Multiplicative.toAdd g.2, g.1.x, g.1.y, g.1.z - g.1.x * g.1.y)
  else if d = 1 then (g.1.x, g.1.y, Multiplicative.toAdd g.2, g.1.z - g.1.x * g.1.y)
  else (g.1.x, g.1.y, g.1.z - g.1.x * g.1.y, Multiplicative.toAdd g.2)

theorem heisenbergProductMalcevCoordinates_norm (d : ℕ) (g : HeisenbergGroup × Multiplicative ℝ) :
    let p := heisenbergProductMalcevCoordinates d g
    max |p.1| (max |p.2.1| (max |p.2.2.1| |p.2.2.2|)) =
      max (heisenbergMalcevNorm (HeisenbergGroup.coordinates g.1)) |Multiplicative.toAdd g.2| := by
  by_cases h0 : d = 0 <;> by_cases h1 : d = 1 <;>
    simp [heisenbergProductMalcevCoordinates, h0, h1, HeisenbergGroup.coordinates,
      heisenbergMalcevNorm, max_assoc, max_comm, max_left_comm]

/-- Translating the argument of a 1-periodic function leaves its integral
over a unit interval unchanged. -/
private theorem intervalIntegral_unit_translate {f : ℝ → ℂ} (hf : Function.Periodic f 1)
    (c : ℝ) : (∫ x in (0 : ℝ)..1, f (x + c)) = ∫ x in (0 : ℝ)..1, f x := by
  rw [intervalIntegral.integral_comp_add_right]
  simpa only [zero_add, add_comm 1 c] using hf.intervalIntegral_add_eq c 0

/-- The unit-cube functional is invariant under left translations on
right-lattice-invariant tests. In particular the shear in the last
coordinate does not change the vertical integral. -/
theorem heisenbergChartMean_leftInvariant (Φ : HeisenbergPoint → ℂ)
    (hΦ : ∀ g (u v w : ℤ), Φ (heisenbergMul g ((u : ℝ), (v : ℝ), (w : ℝ))) = Φ g)
    (a : HeisenbergPoint) :
    heisenbergChartMean (fun g => Φ (heisenbergMul a g)) = heisenbergChartMean Φ := by
  let v (x y : ℝ) := ∫ z in (0 : ℝ)..1, Φ (x, y, z)
  have hz (x y : ℝ) : Function.Periodic (fun z => Φ (x, y, z)) 1 := by
    intro z
    simpa [heisenbergMul] using hΦ (x, y, z) 0 0 1
  have hy (x : ℝ) : Function.Periodic (v x) 1 := by
    intro y
    change (∫ z in (0 : ℝ)..1, Φ (x, y + 1, z)) = ∫ z in (0 : ℝ)..1, Φ (x, y, z)
    have hv (z : ℝ) : Φ (x, y + 1, z) = Φ (x, y, z + (-x)) := by
      simpa [heisenbergMul, add_assoc] using hΦ (x, y, z + (-x)) 0 1 0
    simp_rw [hv]
    exact intervalIntegral_unit_translate (hz x y) (-x)
  have hx : Function.Periodic (fun x => ∫ y in (0 : ℝ)..1, v x y) 1 := by
    intro x
    apply intervalIntegral.integral_congr
    intro y _
    apply intervalIntegral.integral_congr
    intro z _
    simpa [heisenbergMul] using hΦ (x, y, z) 1 0 0
  unfold heisenbergChartMean
  calc
    _ = (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, v (x + a.1) (y + a.2.1)) := by
      apply intervalIntegral.integral_congr
      intro x _
      apply intervalIntegral.integral_congr
      intro y _
      have h := intervalIntegral_unit_translate (hz (x + a.1) (y + a.2.1)) (a.2.2 + a.1 * y)
      simpa only [heisenbergMul, v, add_comm a.1 x, add_comm a.2.1 y,
        show ∀ z : ℝ, a.2.2 + z + a.1 * y = z + (a.2.2 + a.1 * y) by intro z; ring] using h
    _ = (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, v (x + a.1) y) := by
      apply intervalIntegral.integral_congr
      intro x _
      exact intervalIntegral_unit_translate (hy (x + a.1)) a.2.1
    _ = _ := intervalIntegral_unit_translate hx a.1

theorem heisenbergChartMean_one : heisenbergChartMean (fun _ => 1) = 1 := by
  simp [heisenbergChartMean, intervalIntegral.integral_const]

/-- Unit-chart integral for the product with the extra circle, taking the
circle coordinate as the innermost integral. -/
def heisenbergProductChartMean (Ψ : HeisenbergPoint × ℝ → ℂ) : ℂ :=
  heisenbergChartMean (fun g => ∫ u in (0 : ℝ)..1, Ψ (g, u))

/-- The test used in the twisted obstruction has zero product mean by
oscillation in the extra circle coordinate. No mean condition on `Φ` is needed. -/
theorem heisenbergProductChartMean_twist_eq_zero (Φ : HeisenbergPoint → ℂ) :
    heisenbergProductChartMean (fun p => Φ p.1 * phase (-p.2)) = 0 := by
  have hf : ∀ u : ℝ, phase (-u) = fourier (T := 1) (-1) (u : Circle) := by
    intro u
    rw [fourier_coe_apply, phase]
    congr 1
    push_cast
    ring
  have h := AddCircle.intervalIntegral_preimage (1 : ℝ) 0 (fourier (T := 1) (-1))
  rw [AddCircle.volume_eq_smul_haarAddCircle] at h
  simp only [zero_add, ENNReal.ofReal_one, one_smul] at h
  have hzero : (∫ u in (0 : ℝ)..1, phase (-u)) = 0 := by
    simp_rw [hf]
    rw [h]
    exact integral_eq_zero_of_add_right_eq_neg (μ := (AddCircle.haarAddCircle : Measure Circle))
      (fourier_add_half_inv_index (by norm_num : (-1 : ℤ) ≠ 0) (by norm_num : (0 : ℝ) < 1))
  simp [heisenbergProductChartMean, heisenbergChartMean,
    intervalIntegral.integral_const_mul, hzero]

end

end NilBohr
