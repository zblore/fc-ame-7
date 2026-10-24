/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import AME7.Instances
import AME7.LinearPhase
import AME7.Binary

/-!
# AME(7, 2q) for every odd `q ≥ 3`

The coupled state of Shi, Zhang, Zhao and Li (2026, Eq. (31)):
`(|0_L⟩ |G^(0)⟩ + |1_L⟩ |G^(1)⟩) / √2`, with `|0_L⟩`, `|1_L⟩` the Steane logical states
(`AME7.Binary`) and `|G^(a)⟩` the graph state of `Γ` over `ZMod q` with the linear phase
`a · c · x`, `c = (1, -1, 1, 0, 0, 0, 0)` (their Eq. (14)).

For every permutation, the reduction to the first three parties is `½ ∑_{s,t} R_st ⊗ T_st`
(`reduced_coupledState`, their Eq. (33)), and:

* `R₀₀ + R₁₁ = ¼ · 1` (`codeRed_diag`) and `T₀₀ = T₁₁ = q⁻³ · 1` (`graphStateL_firstHalf`), so
  the diagonal terms give the maximally mixed state (their Eq. (34));
* off the Fano lines `R₀₁ = R₁₀ = 0` (`codeRed_cross`); on a Fano line `T₀₁ = T₁₀ = 0`, by the
  kernel vectors `h_t` of their Table II (`fanoCerts`, `crossRed_eq_zero_of_cutAvoid`). So the
  cross terms vanish for every cut (their Eqs. (36)–(37)).
-/

namespace AME7

open OpenQuantumProblem35
open scoped Matrix

/-- The integer vector `c = (1, -1, 1, 0, 0, 0, 0)`. -/
def cvecZ (j : ℕ) : ℤ := [1, -1, 1, 0, 0, 0, 0].getD j 0

/-- The kernel vectors `h_t` of their Table II, one per Fano line, by mask: `h_t` vanishes on the
line, is killed by the rows of `Γ` from the line, and `h_t · c ∈ {±1, ±2}`. -/
def fanoCerts : List (ℕ × List ℤ) :=
  [(11, [0, 0, 1, 0, 0, -1, 1]), (22, [1, 0, 0, 1, 0, 0, -1]), (44, [-1, 1, 0, 0, 1, 0, 0]),
   (49, [0, 0, -1, 1, 0, 0, 1]), (69, [0, 1, 0, 0, -1, 1, 0]), (88, [0, -1, 1, 0, 0, 1, 0]),
   (98, [1, 0, 0, -1, 1, 0, 0])]

/-- What the kernel checks for a Fano certificate. -/
def fanoCertOK (c : ℕ × List ℤ) : Bool :=
  (List.range 7).all (fun i ↦ !c.1.testBit i ||
    (c.2.getD i 0 == 0 && ((List.range 7).map fun j ↦ gammaT i j * c.2.getD j 0).sum == 0)) &&
  (let v := ((List.range 7).map fun j ↦ cvecZ j * c.2.getD j 0).sum
   v == 1 || v == -1 || v == 2 || v == -2)

theorem fanoCerts_ok : fanoCerts.all fanoCertOK = true := by decide +kernel

theorem fanoCerts_masks : fanoCerts.map Prod.fst = fanoMasks := by decide +kernel

variable {q : ℕ} [NeZero q]

/-- The linear phase `a · c`. -/
def phase (a : Fin 2) : Coord 7 1 → ZMod q := fun p ↦ ((a : ℕ) : ZMod q) * (cvecZ (idx p) : ZMod q)

/-- The twisted graph states `|G^(a)⟩`. -/
noncomputable def twisted (a : Fin 2) : StateVector 7 (q ^ 1) :=
  graphStateL (graphU 1 gammaT) (phase a)

/-- The coupled AME(7, 2q) state. -/
noncomputable def coupled72q : StateVector 7 (2 * q ^ 1) :=
  coupledState codeState (twisted (q := q))

omit [NeZero q] in
lemma idx_one (p : Coord 7 1) : idx p = p.1.1 := by
  rw [idx_eq]
  have := p.2.2
  omega

omit [NeZero q] in
/-- A sum over the coordinates of seven one-digit parties, as a sum over `List.range 7`. -/
lemma sum_coord_one {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ p : Coord 7 1, f (idx p) = ((List.range 7).map f).sum :=
  (sum_range_coord (k := 1) f).symm

omit [NeZero q] in
/-- **On a Fano line, no vector on the line reaches the phase difference** (their
Eqs. (26)–(29)). -/
theorem cutAvoid_fano [Nontrivial (ZMod q)] (hq : Odd q) (S : Finset (Fin 7))
    (hS : maskOf S ∈ fanoMasks) :
    CutAvoid (graphU (q := q) 1 gammaT + (graphU 1 gammaT)ᵀ) S (phase 0 - phase 1) := by
  rw [← fanoCerts_masks] at hS
  obtain ⟨c, hc, hcm⟩ := List.mem_map.mp hS
  have hok := List.all_eq_true.mp fanoCerts_ok c hc
  simp only [fanoCertOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true', beq_iff_eq] at hok
  obtain ⟨hrow, hval⟩ := hok
  have hmem : ∀ p : Coord 7 1, p.1 ∈ S ↔ c.1.testBit (idx p) = true := by
    intro p
    rw [idx_one, hcm, testBit_maskOf]
  refine cutAvoid_of_cert _ S _ (fun p ↦ (c.2.getD (idx p) 0 : ZMod q)) (fun p hp ↦ ?_)
    (fun p hp ↦ ?_) ?_
  · have := (hrow (idx p) (idx_lt p)).resolve_left (by simp [(hmem p).mp hp])
    rw [this.1, Int.cast_zero]
  · have hrp := (hrow (idx p) (idx_lt p)).resolve_left (by simp [(hmem p).mp hp])
    have hsum : ∑ c' : Coord 7 1,
        (graphU (q := q) 1 gammaT + (graphU (q := q) 1 gammaT)ᵀ :
          Matrix (Coord 7 1) (Coord 7 1) (ZMod q)) p c' * (c.2.getD (idx c') 0 : ZMod q) =
        (((List.range 7).map fun j ↦ gammaT (idx p) j * c.2.getD j 0).sum : ℤ) := by
      rw [← sum_coord_one, Int.cast_sum]
      refine Finset.sum_congr rfl fun c' _ ↦ ?_
      by_cases hc' : c'.1 ∈ S
      · have := (hrow (idx c') (idx_lt c')).resolve_left (by simp [(hmem c').mp hc'])
        rw [this.1]
        simp
      · rw [graphU_add gammaT gammaT_symm p c' fun h ↦ hc' (h ▸ hp)]
        push_cast
        rfl
    rw [hsum, hrp.2, Int.cast_zero]
  · have hsum : ∑ c' : Coord 7 1, (phase (q := q) 0 - phase (q := q) 1 : Coord 7 1 → ZMod q) c' *
        (c.2.getD (idx c') 0 : ZMod q) =
        ((-((List.range 7).map fun j ↦ cvecZ j * c.2.getD j 0).sum : ℤ) : ZMod q) := by
      rw [Int.cast_neg, ← sum_coord_one, Int.cast_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun c' _ ↦ ?_
      rw [Pi.sub_apply, show phase (q := q) 0 c' = 0 by simp [phase],
        show phase (q := q) 1 c' = (cvecZ (idx c') : ZMod q) by simp [phase]]
      push_cast
      ring
    rw [hsum]
    set v := ((List.range 7).map fun j ↦ cvecZ j * c.2.getD j 0).sum
    have h2 : IsUnit (2 : ZMod q) := by
      simpa using (ZMod.isUnit_iff_coprime 2 q).mpr (Nat.coprime_two_left.mpr hq)
    rcases hval with ((h | h) | h) | h <;> rw [h] <;> simp [h2, h2.neg]

/-- The twisted states are AME on every first half: `T_ss = q⁻³ · 1`. -/
theorem twisted_diag (hq : Odd q) (π : Equiv.Perm (Fin 7)) (s : Fin 2) :
    crossRed (7 / 2) (Nat.div_le_self 7 2) (permuteState π (twisted (q := q) s))
      (permuteState π (twisted s)) = maximallyMixed (7 / 2) (q ^ 1) := by
  rw [crossRed_self, twisted, permuteState_graphStateL]
  apply graphStateL_firstHalf
  have e : (graphU (q := q) 1 gammaT).submatrix (coordPerm π).symm (coordPerm π).symm +
      ((graphU (q := q) 1 gammaT).submatrix (coordPerm π).symm (coordPerm π).symm)ᵀ =
      (graphU (q := q) 1 gammaT + (graphU 1 gammaT)ᵀ).submatrix
        (coordPerm π).symm (coordPerm π).symm := by
    ext i j
    simp
  rw [e]
  exact CutInj.submatrix π (odd_cutInj hq _ (by
    rw [Finset.card_map, card_firstHalf (by norm_num)]))

/-- On a Fano line the twisted cross terms vanish: `T₀₁ = T₁₀ = 0`. -/
theorem twisted_cross [Nontrivial (ZMod q)] (hq : Odd q) (π : Equiv.Perm (Fin 7))
    (hS : maskOf (keptSet π 3) ∈ fanoMasks) (s t : Fin 2) (hst : s ≠ t) :
    crossRed (7 / 2) (Nat.div_le_self 7 2) (permuteState π (twisted (q := q) s))
      (permuteState π (twisted t)) = 0 := by
  simp only [twisted, permuteState_graphStateL]
  apply crossRed_eq_zero_of_cutAvoid
  have e : (graphU (q := q) 1 gammaT).submatrix (coordPerm π).symm (coordPerm π).symm +
      ((graphU (q := q) 1 gammaT).submatrix (coordPerm π).symm (coordPerm π).symm)ᵀ =
      (graphU (q := q) 1 gammaT + (graphU 1 gammaT)ᵀ).submatrix
        (coordPerm π).symm (coordPerm π).symm := by
    ext i j
    simp
  rw [e]
  have h01 := cutAvoid_fano hq _ hS
  fin_cases s <;> fin_cases t
  · exact absurd rfl hst
  · exact CutAvoid.submatrix π h01
  · have h10 : CutAvoid (graphU (q := q) 1 gammaT + (graphU 1 gammaT)ᵀ) (keptSet π 3)
        (phase 1 - phase 0) := by
      intro w hw
      obtain ⟨c, hc, hne⟩ := h01 (-w) (fun p hp ↦ by simp [hw p hp])
      refine ⟨c, hc, fun h ↦ hne ?_⟩
      simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, Pi.sub_apply] at h ⊢
      linear_combination -h
    exact CutAvoid.submatrix π h10
  · exact absurd rfl hst

/-- **The coupled state is AME(7, 2q)** for every odd `q ≥ 3`. -/
theorem coupled72q_isAME (hq : Odd q) (hq3 : 3 ≤ q) : IsAME (coupled72q (q := q)) := by
  have : Fact (1 < q) := ⟨by omega⟩
  have : NeZero (2 * q ^ 1) := ⟨by positivity⟩
  have hmm : ∀ π : Equiv.Perm (Fin 7), HasMaximallyMixedFirstReduction (7 / 2)
      (Nat.div_le_self 7 2) (permuteState π (coupled72q (q := q))) := by
    intro π
    rw [coupled72q, permuteState_coupledState]
    ext a b
    rw [reduced_coupledState]
    have hR : ∀ s t : Fin 2, crossRed (7 / 2) (Nat.div_le_self 7 2)
        (permuteState π (codeState s)) (permuteState π (codeState t)) = codeRed π s t :=
      fun _ _ ↦ rfl
    simp only [hR, Fin.sum_univ_two, twisted_diag hq]
    -- The cross terms vanish.
    have hcross : codeRed π 0 1 (splitL a) (splitL b) *
          crossRed (7 / 2) (Nat.div_le_self 7 2) (permuteState π (twisted (q := q) 0))
            (permuteState π (twisted 1)) (splitR a) (splitR b) +
        codeRed π 1 0 (splitL a) (splitL b) *
          crossRed (7 / 2) (Nat.div_le_self 7 2) (permuteState π (twisted (q := q) 1))
            (permuteState π (twisted 0)) (splitR a) (splitR b) = 0 := by
      by_cases hF : maskOf (keptSet π 3) ∈ fanoMasks
      · rw [twisted_cross hq π hF 0 1 (by decide), twisted_cross hq π hF 1 0 (by decide)]
        simp
      · rw [codeRed_cross π hF 0 1 (by decide), codeRed_cross π hF 1 0 (by decide)]
        simp
    have hdiag := congrFun (congrFun (codeRed_diag π) (splitL a)) (splitL b)
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at hdiag
    have hab : a = b ↔ splitL a = splitL b ∧ splitR a = splitR b := by
      rw [← Prod.mk.injEq, ← splitEquiv_apply, ← splitEquiv_apply]
      exact (splitEquiv (7 / 2)).injective.eq_iff.symm
    -- Group the diagonal and the cross terms, drop the cross terms, use `R₀₀ + R₁₁ = ¼ · 1`.
    have hsplit : ∀ x y z w X : ℂ,
        (2 : ℂ)⁻¹ * (x * X + z + (w + y * X)) = (2 : ℂ)⁻¹ * ((x + y) * X + (z + w)) := by
      intros
      ring
    rw [hsplit, hcross, add_zero, hdiag]
    simp only [maximallyMixed_apply, card_config]
    by_cases h₁ : splitL a = splitL b <;> by_cases h₂ : splitR a = splitR b <;>
      simp [h₁, h₂, hab]
    norm_num
    ring
  have h1 := hmm (Equiv.refl _)
  rw [permuteState_refl] at h1
  exact ⟨isNormalized_of_maxMixed _ h1, hmm⟩

end AME7
