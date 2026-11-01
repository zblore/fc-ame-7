/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import AME7.Coupled
public import AME7.GraphState

/-!
# Graph states with a linear phase

`graphStateL U ℓ` has amplitude `q^(-nk/2) · χ(xᵀ U x + ℓ · x)`: the graph state of `U` with each
level `x_p` given the extra phase `χ(ℓ_p x_p)`, a local unitary. The twisted states `|G_q^(a)⟩` of
Shi, Zhang, Zhao and Li (2026, Eq. (14)) are of this form.

* `crossRed_graphStateL`: the cross reduction of two such states with phases `ℓ`, `ℓ'` is a
  character sum, nonzero only where the traced coefficients cancel `ℓ - ℓ'` on the traced
  coordinates;
* `graphStateL_firstHalf`: with equal phases the reduction is maximally mixed under the cut
  condition, as for `graphState`;
* `crossRed_eq_zero_of_cutAvoid`: with different phases the cross reduction vanishes when no
  vector on the kept coordinates reaches `-(ℓ - ℓ')` through the cut block (`CutAvoid`), which a
  single vector in the kernel of the block certifies (`cutAvoid_of_cert`; their Eqs. (26)–(29)).
-/

@[expose] public section

namespace AME7

open OpenQuantumProblem35
open scoped Matrix

variable {q : ℕ} [NeZero q] {k : ℕ}

/-- The linear form `ℓ · x`. -/
def lin {ι : Type*} [Fintype ι] (ℓ x : ι → ZMod q) : ZMod q := ∑ i, ℓ i * x i

/-- The graph state of `U` with linear phase `ℓ`: amplitude `q^(-nk/2) · χ(xᵀ U x + ℓ · x)`. -/
noncomputable def graphStateL {n : ℕ} (U : Matrix (Coord n k) (Coord n k) (ZMod q))
    (ℓ : Coord n k → ZMod q) : StateVector n (q ^ k) :=
  mkStateVector fun x ↦ normConst q n k * χ (quad U (toVec x) + lin ℓ (toVec x))

/-- The traced coefficient vector of a cross term: from the quadratic form and from the phases. -/
def coeffL {n m : ℕ} (hm : m ≤ n) (S : Matrix (Coord n k) (Coord n k) (ZMod q))
    (δ : Coord n k → ZMod q) (d : Coord m k → ZMod q) : Coord (n - m) k → ZMod q :=
  fun c ↦ coeff hm S d c + δ (rightIndex hm c.1, c.2)

omit [NeZero q] in
lemma lin_add_left {ι : Type*} [Fintype ι] (ℓ ℓ' y w : ι → ZMod q) :
    lin ℓ (y + w) - lin ℓ' y = lin (ℓ - ℓ') y + lin ℓ w := by
  simp only [lin, Pi.add_apply, Pi.sub_apply, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun _ _ ↦ by ring

/-- **The cross reduction of two graph states with linear phases.** -/
theorem crossRed_graphStateL {n m : ℕ} (hm : m ≤ n) (U : Matrix (Coord n k) (Coord n k) (ZMod q))
    (ℓ ℓ' : Coord n k → ZMod q) (a b : Config m (q ^ k)) :
    ∃ K : ZMod q, (toVec a = toVec b → ℓ = ℓ' → K = 0) ∧
      crossRed m hm (graphStateL U ℓ) (graphStateL U ℓ') a b =
        ((q : ℂ) ^ (n * k))⁻¹ * χ K *
          (if coeffL hm (U + Uᵀ) (ℓ - ℓ') (toVec a - toVec b) = 0 then
            (q : ℂ) ^ ((n - m) * k) else 0) := by
  set d := toVec a - toVec b
  set K₀ : ZMod q := quad U (lift d) +
    ∑ p : Coord m k, (∑ l, lift d l * (U + Uᵀ) l (leftIndex hm p.1, p.2)) * toVec b p +
    lin ℓ (lift d) + ∑ p : Coord m k, (ℓ - ℓ') (leftIndex hm p.1, p.2) * toVec b p
  refine ⟨K₀, fun hab hℓ ↦ ?_, ?_⟩
  · have hd : d = 0 := sub_eq_zero.mpr hab
    have hl : lift (n := n) d = 0 := by
      funext p
      simp [lift, hd]
    simp [K₀, hl, hℓ, quad, lin]
  have hdiff : ∀ z : Config (n - m) (q ^ k),
      (quad U (toVec (combineFirst m hm a z)) + lin ℓ (toVec (combineFirst m hm a z))) -
        (quad U (toVec (combineFirst m hm b z)) + lin ℓ' (toVec (combineFirst m hm b z))) =
        K₀ + ∑ c, toVec z c * coeffL hm (U + Uᵀ) (ℓ - ℓ') d c := by
    intro z
    have hsplit : ∀ x y : ZMod q, ∀ s t : ZMod q, (x + s) - (y + t) = (x - y) + (s - t) := by
      intros; ring
    rw [hsplit, toVec_combineFirst_eq hm a b z, quad_add, lin_add_left, lin, sum_coord_split hm,
      sum_coord_split hm]
    simp only [toVec_combineFirst_left, toVec_combineFirst_right, coeffL, coeff, K₀, mul_add,
      Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl fun c _ ↦ mul_comm
      (∑ l, lift d l * (U + Uᵀ) l (rightIndex hm c.1, c.2)) (toVec z c),
      Finset.sum_congr rfl fun c _ ↦ mul_comm ((ℓ - ℓ') (rightIndex hm c.1, c.2)) (toVec z c)]
    ring
  have hterm : ∀ z : Config (n - m) (q ^ k),
      graphStateL U ℓ (combineFirst m hm a z) * star (graphStateL U ℓ' (combineFirst m hm b z)) =
        ((q : ℂ) ^ (n * k))⁻¹ * χ (K₀ + ∑ c, toVec z c * coeffL hm (U + Uᵀ) (ℓ - ℓ') d c) := by
    intro z
    rw [← hdiff z, sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_neg_eq_conj,
      ← normConst_mul_star]
    simp only [graphStateL, mkStateVector_apply, star_mul', starRingEnd_apply]
    ring
  have hsum : ∑ z : Config (n - m) (q ^ k), χ (∑ c, toVec z c * coeffL hm (U + Uᵀ) (ℓ - ℓ') d c) =
      ∑ v : Coord (n - m) k → ZMod q, χ (∑ c, v c * coeffL hm (U + Uᵀ) (ℓ - ℓ') d c) :=
    Fintype.sum_equiv (vecEquiv (n - m)) _ _ fun _ ↦ rfl
  rw [crossRed]
  simp_rw [hterm, AddChar.map_add_eq_mul, ← Finset.mul_sum]
  rw [hsum, sum_χ_dot]
  simp only [Fintype.card_prod, Fintype.card_fin]
  ring

/-- With equal phases the first-half reduction is maximally mixed under the cut condition. -/
theorem graphStateL_firstHalf {n : ℕ} (U : Matrix (Coord n k) (Coord n k) (ZMod q))
    (ℓ : Coord n k → ZMod q) (h : CutInj (U + Uᵀ) (firstHalf n (n / 2))) :
    HasMaximallyMixedFirstReduction (n / 2) (Nat.div_le_self n 2) (graphStateL U ℓ) := by
  have hm := Nat.div_le_self n 2
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  ext a b
  obtain ⟨K, hK0, hK⟩ := crossRed_graphStateL hm U ℓ ℓ a b
  rw [← crossRed_self, hK, maximallyMixed_apply, card_config]
  have hexp : n * k = (n - n / 2) * k + n / 2 * k := by
    rw [← add_mul, Nat.sub_add_cancel hm]
  have hc : ∀ d, coeffL hm (U + Uᵀ) (ℓ - ℓ) d = coeff hm (U + Uᵀ) d := by
    intro d
    funext c
    simp [coeffL]
  rw [hc]
  by_cases hab : a = b
  · subst hab
    have h0 : coeff hm (U + Uᵀ) (toVec a - toVec a) = 0 := by
      funext c
      simp [coeff, lift]
    rw [hK0 rfl rfl, ite_eq_left h0, ite_eq_left rfl, hexp, pow_add]
    push_cast
    rw [← pow_mul, mul_comm k (n / 2)]
    field_simp
    simp
  · have hne : coeff hm (U + Uᵀ) (toVec a - toVec b) ≠ 0 := by
      intro hc0
      apply hab
      have hw := h (lift (toVec a - toVec b)) (fun p hp ↦ by
          simp only [firstHalf, Finset.mem_filter, Finset.mem_univ, true_and] at hp
          simp [lift, hp]) (fun c hc' ↦ by
          simp only [firstHalf, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hc'
          have hjk : rightIndex hm ⟨c.1.1 - n / 2, by omega⟩ = c.1 := by
            ext
            simp [rightIndex]
            omega
          have := congrFun hc0 (⟨c.1.1 - n / 2, by omega⟩, c.2)
          simpa [coeff, hjk] using this)
      apply toVec_injective
      funext p
      have hp := congrFun hw (leftIndex hm p.1, p.2)
      rw [lift_left] at hp
      exact sub_eq_zero.mp hp
    rw [ite_eq_right hne, ite_eq_right hab]
    ring

/-- No vector supported on the coordinates of `A` reaches `-δ` on the coordinates outside `A`
through the block of `S`. -/
def CutAvoid {n : ℕ} (S : Matrix (Coord n k) (Coord n k) (ZMod q)) (A : Finset (Fin n))
    (δ : Coord n k → ZMod q) : Prop :=
  ∀ w : Coord n k → ZMod q, (∀ p : Coord n k, p.1 ∉ A → w p = 0) →
    ∃ c : Coord n k, c.1 ∉ A ∧ ∑ p, w p * S p c + δ c ≠ 0

/-- **With different phases the cross reduction vanishes** when the first half avoids. -/
theorem crossRed_eq_zero_of_cutAvoid {n : ℕ} (U : Matrix (Coord n k) (Coord n k) (ZMod q))
    (ℓ ℓ' : Coord n k → ZMod q) (h : CutAvoid (U + Uᵀ) (firstHalf n (n / 2)) (ℓ - ℓ')) :
    crossRed (n / 2) (Nat.div_le_self n 2) (graphStateL U ℓ) (graphStateL U ℓ') = 0 := by
  have hm := Nat.div_le_self n 2
  ext a b
  obtain ⟨K, -, hK⟩ := crossRed_graphStateL hm U ℓ ℓ' a b
  rw [hK, Matrix.zero_apply]
  have hne : coeffL hm (U + Uᵀ) (ℓ - ℓ') (toVec a - toVec b) ≠ 0 := by
    intro hc0
    obtain ⟨c, hc, hcne⟩ := h (lift (toVec a - toVec b)) (fun p hp ↦ by
      simp only [firstHalf, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      simp [lift, hp])
    simp only [firstHalf, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hc
    have hjk : rightIndex hm ⟨c.1.1 - n / 2, by omega⟩ = c.1 := by
      ext
      simp [rightIndex]
      omega
    have := congrFun hc0 (⟨c.1.1 - n / 2, by omega⟩, c.2)
    simp only [coeffL, coeff, hjk, Pi.zero_apply] at this
    exact hcne this
  rw [ite_eq_right hne, mul_zero]

/-- Permuting the parties of a graph state with a linear phase permutes the matrix and the phase. -/
theorem permuteState_graphStateL {n : ℕ} (π : Equiv.Perm (Fin n))
    (U : Matrix (Coord n k) (Coord n k) (ZMod q)) (ℓ : Coord n k → ZMod q) :
    permuteState π (graphStateL U ℓ) =
      graphStateL (U.submatrix (coordPerm π).symm (coordPerm π).symm)
        (fun p ↦ ℓ ((coordPerm π).symm p)) := by
  ext x
  rw [permuteState_apply]
  simp only [graphStateL, mkStateVector_apply]
  rw [show toVec (permuteConfig π x) = fun p ↦ toVec x (coordPerm (k := k) π p) from rfl,
    quad_perm]
  congr 3
  unfold lin
  rw [← Equiv.sum_comp (coordPerm π) (fun p ↦ ℓ ((coordPerm π).symm p) * toVec x p)]
  simp

omit [NeZero q] in
/-- Permuting the matrix and the phase moves the cut, as for `CutInj`. -/
lemma CutAvoid.submatrix {n : ℕ} {S : Matrix (Coord n k) (Coord n k) (ZMod q)}
    {δ : Coord n k → ZMod q} (π : Equiv.Perm (Fin n)) {A : Finset (Fin n)}
    (h : CutAvoid S (A.map π.symm.toEmbedding) δ) :
    CutAvoid (S.submatrix (coordPerm π).symm (coordPerm π).symm)
      A (fun p ↦ δ ((coordPerm π).symm p)) := by
  intro w hw
  have hmem : ∀ i : Fin n, π i ∈ A → i ∈ A.map π.symm.toEmbedding := fun i hi ↦ by
    simpa using Finset.mem_map_of_mem π.symm.toEmbedding hi
  obtain ⟨c, hc, hne⟩ := h (fun p ↦ w (coordPerm π p))
    (fun p hp ↦ hw (coordPerm π p) fun h' ↦ hp (hmem p.1 h'))
  refine ⟨coordPerm π c, fun h' ↦ hc ?_, ?_⟩
  · simpa [coordPerm] using
      Finset.mem_map_of_mem π.symm.toEmbedding (show π c.1 ∈ A from h')
  · simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]
    rw [← Equiv.sum_comp (coordPerm π) (fun p ↦ w p * S ((coordPerm π).symm p) c)] at *
    simpa using hne

omit [NeZero q] in
/-- **A kernel vector certifies avoidance.** If `h` vanishes on the coordinates of `A`, is killed
by the rows of `S` from `A`, and pairs with `δ` to a unit, then `A` avoids `δ`. -/
theorem cutAvoid_of_cert [Nontrivial (ZMod q)] {n : ℕ}
    (S : Matrix (Coord n k) (Coord n k) (ZMod q)) (A : Finset (Fin n)) (δ : Coord n k → ZMod q)
    (h : Coord n k → ZMod q) (hsupp : ∀ c : Coord n k, c.1 ∈ A → h c = 0)
    (hker : ∀ p : Coord n k, p.1 ∈ A → ∑ c, S p c * h c = 0)
    (hunit : IsUnit (∑ c, δ c * h c)) : CutAvoid S A δ := by
  intro w hw
  by_contra hall
  push Not at hall
  have hzero : ∑ c, (∑ p, w p * S p c + δ c) * h c = 0 := by
    refine Finset.sum_eq_zero fun c _ ↦ ?_
    by_cases hc : c.1 ∈ A
    · rw [hsupp c hc, mul_zero]
    · rw [hall c hc, zero_mul]
  have hfirst : ∑ c, (∑ p, w p * S p c) * h c = 0 := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun p _ ↦ ?_
    by_cases hp : p.1 ∈ A
    · simp_rw [mul_assoc, ← Finset.mul_sum]
      rw [hker p hp, mul_zero]
    · simp [hw p hp]
  simp only [add_mul, Finset.sum_add_distrib, hfirst, zero_add] at hzero
  exact hunit.ne_zero hzero

end AME7
