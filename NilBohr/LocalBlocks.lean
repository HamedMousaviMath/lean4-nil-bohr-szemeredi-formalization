import NilBohr.Definitions

/-! Spatial displacement and boundary deletion for the local phase argument. -/

open Polynomial
open scoped BigOperators

namespace NilBohr

/-- An explicit coefficient-uniform displacement bound on the whole parameter
box. In applications both parameters lie in an interval of length `H`, so
`|y-z|` is bounded by `H`. -/
theorem abs_eval_sub_le_of_hasCoefficients {C : ℝ} {q M d : ℕ} {P : Polynomial ℤ}
    (hP : HasCoefficients C q P) (hdeg : P.natDegree ≤ d) (hM : 0 < M)
    (y z : ℤ) (hy : |(y : ℝ)| ≤ (M : ℝ)) (hz : |(z : ℝ)| ≤ (M : ℝ)) :
    |((P.eval y : ℤ) : ℝ) - ((P.eval z : ℤ) : ℝ)| ≤
      (C^2 * ((d : ℝ) + 1) * (d : ℝ)) * (q : ℝ)^(P.natDegree - 1) *
        (M : ℝ)^(P.natDegree - 1) * |(y : ℝ) - (z : ℝ)| := by
  obtain ⟨hC, _, hd, hconst, hcoeff, a, _, haC, hlead⟩ := hP
  let e := P.natDegree
  let Q := (q : ℝ)^(e - 1)
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hC₀ : 0 ≤ C := by linarith
  have hleadR : |(P.leadingCoeff : ℝ)| ≤ C * Q := by
    have heq : (P.leadingCoeff : ℝ) = (a : ℝ) * Q := by
      dsimp [Q, e]
      exact_mod_cast hlead
    rw [heq, abs_mul, abs_of_nonneg hQ]
    exact mul_le_mul_of_nonneg_right haC hQ
  have hcoef (j : ℕ) (hj : j ≤ e) : |(P.coeff j : ℝ)| ≤ C^2 * Q := by
    by_cases hzero : j = 0
    · simp only [hzero, hconst, Int.cast_zero, abs_zero]
      exact mul_nonneg (sq_nonneg _) hQ
    rcases eq_or_lt_of_le hj with rfl | hj'
    · rw [Polynomial.coeff_natDegree]
      exact hleadR.trans (mul_le_mul_of_nonneg_right (by nlinarith) hQ)
    · exact (hcoeff j (by omega) hj').trans
        (by simpa only [pow_two, mul_assoc] using mul_le_mul_of_nonneg_left hleadR hC₀)
  have hev (n : ℤ) : ((P.eval n : ℤ) : ℝ) =
      ∑ j ∈ Finset.range (e + 1), (P.coeff j : ℝ) * (n : ℝ)^j := by
    rw [Polynomial.eval_eq_sum_range]
    push_cast
    rfl
  have hM1 : 1 ≤ (M : ℝ) := by exact_mod_cast hM
  have hM0 : 0 ≤ (M : ℝ) := by positivity
  have hsum : ((P.eval y : ℤ) : ℝ) - ((P.eval z : ℤ) : ℝ) =
      ∑ j ∈ Finset.range (e + 1), (P.coeff j : ℝ) * ((y : ℝ)^j - (z : ℝ)^j) := by
    rw [hev y, hev z, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hterm (j : ℕ) (hj : j ≤ e) :
      |(y : ℝ)^j - (z : ℝ)^j| ≤ |(y : ℝ) - (z : ℝ)| * d * (M : ℝ)^(e - 1) := by
    have hmax : max |(y : ℝ)| |(z : ℝ)| ≤ (M : ℝ) := max_le hy hz
    have hmax0 : 0 ≤ max |(y : ℝ)| |(z : ℝ)| := (abs_nonneg _).trans (le_max_left _ _)
    have hjd : (j : ℝ) ≤ (d : ℝ) := by exact_mod_cast hj.trans hdeg
    apply (abs_pow_sub_pow_le (y : ℝ) (z : ℝ) j).trans
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left hjd (abs_nonneg _)
    · exact (pow_le_pow_left₀ hmax0 hmax _).trans (pow_le_pow_right₀ hM1 (by omega))
    · exact pow_nonneg hmax0 _
    · positivity
  rw [hsum]
  calc
    _ ≤ ∑ j ∈ Finset.range (e + 1), |(P.coeff j : ℝ) * ((y : ℝ)^j - (z : ℝ)^j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range (e + 1),
        (C^2 * Q) * (|(y : ℝ) - (z : ℝ)| * d * (M : ℝ)^(e - 1)) := by
      apply Finset.sum_le_sum
      intro j hj
      have hj' : j ≤ e := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      rw [abs_mul]
      exact mul_le_mul (hcoef j hj') (hterm j hj') (abs_nonneg _) (mul_nonneg (sq_nonneg _) hQ)
    _ ≤ ∑ _j ∈ Finset.range (d + 1),
        (C^2 * Q) * (|(y : ℝ) - (z : ℝ)| * d * (M : ℝ)^(e - 1)) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_succ hdeg) (by positivity)
    _ = _ := by simp [Q, e]; ring

/-- The displacement bound on an interval of at most `H` integer parameters. -/
theorem abs_eval_sub_le_on_short_interval {C : ℝ} {q M d H : ℕ} {P : Polynomial ℤ}
    (hP : HasCoefficients C q P) (hdeg : P.natDegree ≤ d) (hM : 0 < M)
    {y z : ℤ} (hy : y ∈ positiveInterval M) (hz : z ∈ positiveInterval M)
    (hshort : |y - z| ≤ (H : ℤ)) :
    |((P.eval y : ℤ) : ℝ) - ((P.eval z : ℤ) : ℝ)| ≤
      (C^2 * ((d : ℝ) + 1) * (d : ℝ)) * (q : ℝ)^(P.natDegree - 1) *
        (M : ℝ)^(P.natDegree - 1) * (H : ℝ) := by
  have hbound {t : ℤ} (ht : t ∈ positiveInterval M) : |(t : ℝ)| ≤ (M : ℝ) := by
    obtain ⟨ht₀, ht₁⟩ := Finset.mem_Icc.mp ht
    rw [abs_of_nonneg (by exact_mod_cast (show 0 ≤ t by omega))]
    exact_mod_cast ht₁
  have hD := abs_eval_sub_le_of_hasCoefficients hP hdeg hM y z (hbound hy) (hbound hz)
  refine hD.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  exact_mod_cast hshort

/-- Integer positions for which the shift at the first parameter lies within
`r` of a boundary between consecutive blocks of width `w`. -/
noncomputable def boundaryNeighborhood (X : Finset ℤ) (w r : ℕ) (s : ℤ) : Finset ℤ := by
  classical
  exact X.filter (fun x => ∃ j : ℤ, |x + s - (w : ℤ) * j| ≤ (r : ℤ))

theorem mem_boundaryNeighborhood {X : Finset ℤ} {w r : ℕ} {s x : ℤ} :
    x ∈ boundaryNeighborhood X w r s ↔ x ∈ X ∧ ∃ j : ℤ, |x + s - (w : ℤ) * j| ≤ (r : ℤ) := by
  classical
  exact Finset.mem_filter

/-- In an arbitrary translated integer window, boundary neighborhoods are
bounded by the number of relevant boundaries times `2r+1`. The form here
also covers a wide neighborhood using the total size of the window. -/
theorem card_boundaryNeighborhood_mul_le {X : Finset ℤ} {lo hi : ℤ}
    (hlo : lo ≤ hi) (hX : X ⊆ Finset.Icc lo hi) {w r : ℕ} (hw : 0 < w) (s : ℤ) :
    ((boundaryNeighborhood X w r s).card : ℤ) * (w : ℤ) ≤
      (hi - lo + 4 * (w : ℤ)) * (2 * (r : ℤ) + 1) := by
  classical
  have hwz : (0 : ℤ) < w := by exact_mod_cast hw
  have hrz : (0 : ℤ) ≤ r := by positivity
  have hrad : 0 ≤ 2 * (r : ℤ) + 1 := by omega
  by_cases hsmall : r ≤ w
  · let A : ℤ := lo + s - r
    let B : ℤ := hi + s + r
    let j₀ := A / (w : ℤ)
    let j₁ := B / (w : ℤ)
    let J := Finset.Icc j₀ j₁
    let V (j : ℤ) := Finset.Icc ((w : ℤ) * j - s - r) ((w : ℤ) * j - s + r)
    have hab : A ≤ B := by dsimp [A, B]; omega
    have hj := Int.ediv_le_ediv hwz hab
    have hsmallz : (r : ℤ) ≤ (w : ℤ) := by exact_mod_cast hsmall
    have hJ : (J.card : ℤ) * (w : ℤ) ≤ hi - lo + 4 * (w : ℤ) := by
      rw [show (J.card : ℤ) = j₁ + 1 - j₀ from Int.card_Icc_of_le j₀ j₁ (by change A / (w : ℤ) ≤ B / (w : ℤ) + 1; omega)]
      have ha := Int.emod_add_ediv A (w : ℤ)
      have hb := Int.emod_add_ediv B (w : ℤ)
      change A % (w : ℤ) + (w : ℤ) * j₀ = A at ha
      change B % (w : ℤ) + (w : ℤ) * j₁ = B at hb
      have hA := Int.emod_lt_of_pos A hwz
      have hB := Int.emod_nonneg B hwz.ne'
      have hab' : B - A = hi - lo + 2 * (r : ℤ) := by dsimp [A, B]; ring
      nlinarith only [ha, hb, hA, hB, hab', hsmallz]
    have hsub : boundaryNeighborhood X w r s ⊆ J.biUnion V := by
      intro x hx
      obtain ⟨hxX, j, hj⟩ := mem_boundaryNeighborhood.mp hx
      obtain ⟨hxlo, hxhi⟩ := Finset.mem_Icc.mp (hX hxX)
      obtain ⟨hjlo, hjhi⟩ := abs_le.mp hj
      have hj₀ : A ≤ (w : ℤ) * j := by dsimp [A]; omega
      have hj₁ : (w : ℤ) * j ≤ B := by dsimp [B]; omega
      refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_Icc.mpr ⟨?_, ?_⟩,
        Finset.mem_Icc.mpr ⟨by change (w : ℤ) * j - s - r ≤ x; omega,
          by change x ≤ (w : ℤ) * j - s + r; omega⟩⟩
      · dsimp [j₀]
        have hq := Int.ediv_le_ediv hwz hj₀
        rw [Int.mul_ediv_cancel_left _ hwz.ne'] at hq
        exact hq
      · dsimp [j₁]
        apply (Int.le_ediv_iff_mul_le hwz).mpr
        rwa [mul_comm]
    have hNat : (boundaryNeighborhood X w r s).card ≤ J.card * (2 * r + 1) := by
      apply (Finset.card_le_card hsub).trans
      apply Finset.card_biUnion_le_card_mul
      intro j _
      have hcount : ((V j).card : ℤ) = 2 * (r : ℤ) + 1 := by
        change ((Finset.Icc ((w : ℤ) * j - s - r) ((w : ℤ) * j - s + r)).card : ℤ) = _
        rw [Int.card_Icc_of_le _ _ (by omega)]
        omega
      exact_mod_cast hcount.le
    have hInt : ((boundaryNeighborhood X w r s).card : ℤ) ≤ (J.card : ℤ) * (2 * (r : ℤ) + 1) := by
      exact_mod_cast hNat
    calc
      _ ≤ ((J.card : ℤ) * (2 * (r : ℤ) + 1)) * (w : ℤ) :=
        mul_le_mul_of_nonneg_right hInt hwz.le
      _ = ((J.card : ℤ) * (w : ℤ)) * (2 * (r : ℤ) + 1) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hJ hrad
  · have ht : (boundaryNeighborhood X w r s).card ≤ (Finset.Icc lo hi).card :=
      Finset.card_le_card (fun x hx => hX (mem_boundaryNeighborhood.mp hx).1)
    have ht' : ((boundaryNeighborhood X w r s).card : ℤ) ≤ (Finset.Icc lo hi).card := by
      exact_mod_cast ht
    rw [Int.card_Icc_of_le lo hi (by omega)] at ht'
    exact mul_le_mul (ht'.trans (by omega)) (by omega) hwz.le (by omega)

/-- A displacement whose modulus is smaller than the distance to every
boundary leaves the Euclidean block index unchanged. The block indexed
by `j` consists of the integers in `(w*j,w*(j+1)]`. -/
theorem blockIndex_eq_of_away_from_boundaries {w : ℤ} (hw : 0 < w) {R : ℝ} {z₀ z : ℤ}
    (hmove : |(z : ℝ) - (z₀ : ℝ)| ≤ R)
    (haway : ∀ j : ℤ, R < |(z₀ : ℝ) - ((w * j : ℤ) : ℝ)|) :
    (z - 1) / w = (z₀ - 1) / w := by
  let j := (z₀ - 1) / w
  have hd := Int.emod_add_ediv (z₀ - 1) w
  have hn := Int.emod_nonneg (z₀ - 1) hw.ne'
  have hm := Int.emod_lt_of_pos (z₀ - 1) hw
  change (z₀ - 1) % w + w * j = z₀ - 1 at hd
  have h₁ : w * j < z₀ := by omega
  have h₂ : z₀ ≤ w * (j + 1) := by rw [mul_add, mul_one]; omega
  have h₁R : ((w * j : ℤ) : ℝ) < (z₀ : ℝ) := by exact_mod_cast h₁
  have h₂R : (z₀ : ℝ) ≤ ((w * (j + 1) : ℤ) : ℝ) := by exact_mod_cast h₂
  have hleft := haway j
  have hright := haway (j + 1)
  rw [abs_of_nonneg (sub_nonneg.mpr h₁R.le)] at hleft
  rw [abs_of_nonpos (sub_nonpos.mpr h₂R)] at hright
  obtain ⟨hlo, hhi⟩ := abs_le.mp hmove
  have h₁' : w * j < z := by exact_mod_cast (show ((w * j : ℤ) : ℝ) < (z : ℝ) by linarith)
  have h₂' : z < w * (j + 1) := by
    exact_mod_cast (show (z : ℝ) < ((w * (j + 1) : ℤ) : ℝ) by linarith)
  change (z - 1) / w = j
  apply le_antisymm
  · have h : (z - 1) / w < j + 1 := (Int.ediv_lt_iff_lt_mul hw).mpr (by rw [mul_comm]; omega)
    omega
  · exact (Int.le_ediv_iff_mul_le hw).mpr (by rw [mul_comm]; omega)

/-- On a single congruence class of an interval, both block and residue are
fixed provided the first shifted point avoids every boundary strip. -/
theorem localBlockCoordinates_eq_of_away_from_boundaries {L V : ℕ} (hL : 0 < L) (hV : 0 < V)
    (P : Polynomial ℤ) (x y₀ y z : ℤ) {R : ℝ}
    (hy : |((P.eval y : ℤ) : ℝ) - ((P.eval y₀ : ℤ) : ℝ)| ≤ R)
    (hz : |((P.eval z : ℤ) : ℝ) - ((P.eval y₀ : ℤ) : ℝ)| ≤ R)
    (haway : ∀ j : ℤ, R < |((x + P.eval y₀ : ℤ) : ℝ) - ((((L : ℤ) * V) * j : ℤ) : ℝ)|)
    (hres : y ≡ z [ZMOD (L : ℤ)]) :
    ((x + P.eval y - 1) / ((L : ℤ) * V), (x + P.eval y - 1) % (L : ℤ)) =
      ((x + P.eval z - 1) / ((L : ℤ) * V), (x + P.eval z - 1) % (L : ℤ)) := by
  let w : ℤ := (L : ℤ) * V
  have hw : 0 < w := by dsimp [w]; positivity
  have hshift {u : ℤ} (hu : |((P.eval u : ℤ) : ℝ) - ((P.eval y₀ : ℤ) : ℝ)| ≤ R) :
      (x + P.eval u - 1) / w = (x + P.eval y₀ - 1) / w := by
    apply blockIndex_eq_of_away_from_boundaries hw ?_ haway
    push_cast
    simpa only [add_sub_add_left_eq_sub] using hu
  refine Prod.ext ((hshift hy).trans (hshift hz).symm) ?_
  exact ((Int.ModEq.refl x).add (eval_modEq P (L : ℤ) y z hres)).sub (Int.ModEq.refl 1)

/-- The boundary count at the actual spatial scale. Taking the integer
ceiling of a real radius changes the constant only, for radii at least one. -/
theorem card_boundaryNeighborhood_spatial_bound {X : Finset ℤ} {C R : ℝ} {N w : ℕ}
    (hC : 0 ≤ C) (hR : 1 ≤ R) (hw : 0 < w) (hwN : w ≤ N)
    (hX : X ⊆ spatialInterval C N) (s : ℤ) :
    ((boundaryNeighborhood X w ⌈R⌉₊ s).card : ℝ) ≤
      (5 * (2 * C + 4)) * N * R / (w : ℝ) := by
  let lo : ℤ := ⌈-C * (N : ℝ)⌉
  let hi : ℤ := ⌊C * (N : ℝ)⌋
  have hCN : 0 ≤ C * (N : ℝ) := by positivity
  have hlo : lo ≤ 0 := (Int.ceil_le).2 (by push_cast; linarith)
  have hhi : 0 ≤ hi := (Int.le_floor).2 (by push_cast; linarith)
  have hsub : X ⊆ Finset.Icc lo hi := hX
  let m := (boundaryNeighborhood X w ⌈R⌉₊ s).card
  have hbound := card_boundaryNeighborhood_mul_le (hlo.trans hhi) hsub hw s (r := ⌈R⌉₊)
  have hboundR : (m : ℝ) * (w : ℝ) ≤
      ((hi : ℝ) - (lo : ℝ) + 4 * (w : ℝ)) * (2 * (⌈R⌉₊ : ℝ) + 1) := by
    exact_mod_cast hbound
  have hWidth : (w : ℝ) ≤ N := by exact_mod_cast hwN
  have hloR : -C * (N : ℝ) ≤ (lo : ℝ) := Int.le_ceil _
  have hhiR : (hi : ℝ) ≤ C * (N : ℝ) := Int.floor_le _
  have hceil : (⌈R⌉₊ : ℝ) < R + 1 := Nat.ceil_lt_add_one (by linarith)
  have h₁ : (hi : ℝ) - (lo : ℝ) + 4 * (w : ℝ) ≤ (2 * C + 4) * N := by linarith
  have h₂ : 2 * (⌈R⌉₊ : ℝ) + 1 ≤ 5 * R := by linarith
  change (m : ℝ) ≤ (5 * (2 * C + 4)) * N * R / (w : ℝ)
  apply (le_div_iff₀ (by positivity)).mpr
  refine hboundR.trans ((mul_le_mul h₁ h₂ (by positivity) (by positivity)).trans_eq ?_)
  ring

/-- Delete all boundary-neighborhood positions, with additive costs for
any finite family of polynomials and widths. -/
theorem card_union_boundaryNeighborhood_spatial_bound {ι : Type*} (S : Finset ι)
    {X : Finset ℤ} {C : ℝ} {N : ℕ} (hC : 0 ≤ C) (hX : X ⊆ spatialInterval C N)
    (w : ι → ℕ) (R : ι → ℝ) (s : ι → ℤ)
    (hw : ∀ i ∈ S, 0 < w i) (hwN : ∀ i ∈ S, w i ≤ N) (hR : ∀ i ∈ S, 1 ≤ R i) :
    ((S.biUnion (fun i => boundaryNeighborhood X (w i) ⌈R i⌉₊ (s i))).card : ℝ) ≤
      ∑ i ∈ S, (5 * (2 * C + 4)) * N * R i / (w i : ℝ) := by
  have hcard : (S.biUnion (fun i => boundaryNeighborhood X (w i) ⌈R i⌉₊ (s i))).card ≤
      ∑ i ∈ S, (boundaryNeighborhood X (w i) ⌈R i⌉₊ (s i)).card := Finset.card_biUnion_le
  calc
    _ ≤ ((∑ i ∈ S, (boundaryNeighborhood X (w i) ⌈R i⌉₊ (s i)).card : ℕ) : ℝ) := by
      exact_mod_cast hcard
    _ ≤ _ := by
      push_cast
      refine Finset.sum_le_sum (fun i hi => ?_)
      exact card_boundaryNeighborhood_spatial_bound hC (hR i hi) (hw i hi) (hwN i hi) hX (s i)

/-- A retained position is farther from every boundary than any radius
below the integer radius used in the deletion. -/
theorem boundaryAway_of_not_mem {X : Finset ℤ} {w r : ℕ} {s x : ℤ} {R : ℝ}
    (hx : x ∈ X) (hR : R ≤ (r : ℝ)) (hgood : x ∉ boundaryNeighborhood X w r s) :
    ∀ j : ℤ, R < |((x + s : ℤ) : ℝ) - (((w : ℤ) * j : ℤ) : ℝ)| := by
  intro j
  have hJ : (r : ℤ) < |x + s - (w : ℤ) * j| :=
    lt_of_not_ge (fun hj => hgood (mem_boundaryNeighborhood.mpr ⟨hx, j, hj⟩))
  refine hR.trans_lt ?_
  exact_mod_cast hJ

end NilBohr
