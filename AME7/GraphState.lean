/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import FormalConjectures.OpenQuantumProblems.«35»

/-!
# Qudit graph states over `ZMod q`, with several coordinates per party

Fix `q ≥ 1` and `k`. Each of `n` parties has `q^k` levels, read as `k` digits base `q`, so a
configuration is a vector over `ZMod q` indexed by *coordinates* `(i, j)`: party `i`, digit `j`
(`toVec`). A matrix `U` over `ZMod q` on the coordinates defines the state whose amplitude at `x` is
`q^(-nk/2) · χ(xᵀ U x)`, with `χ(t) = exp(2πit/q)` (`graphState`).

Write `S = U + Uᵀ`. For parties split into a kept set `A` and the rest, the reduction to `A` is a
character sum over the levels of the other parties. It is maximally mixed when no non-zero vector
supported on the coordinates of `A` is killed by the block of `S` between the coordinates of `A`
and the rest (`CutInj`). So the state is AME when that holds for every set of `n/2` parties
(`graphState_isAME`), for any number of parties, even or odd.

With `k = 1` this is the usual qudit graph state over `ZMod q`. With `q = 2` and `k > 1` it covers
graph states over `GF(2^k)`, written in a basis of `GF(2^k)` over `GF(2)`.
-/

namespace AME7

open OpenQuantumProblem35
open scoped Matrix

variable {q : ℕ} [NeZero q] {k : ℕ}

/-- The additive character `t ↦ exp(2πit/q)` of `ZMod q`. -/
noncomputable abbrev χ : AddChar (ZMod q) ℂ := ZMod.stdAddChar

/-- The coordinates of `n` parties with `k` digits each: party `i`, digit `j`. -/
abbrev Coord (n k : ℕ) := Fin n × Fin k

/-- The quadratic form `xᵀ U x`, for any finite index type. -/
def quad {ι : Type*} [Fintype ι] (U : Matrix ι ι (ZMod q)) (x : ι → ZMod q) : ZMod q :=
  ∑ i, ∑ j, U i j * x i * x j

/-- One party's level `a < q^k`, as its `k` digits base `q`, read in `ZMod q`. -/
def digits (a : Fin (q ^ k)) : Fin k → ZMod q :=
  fun j ↦ ZMod.finEquiv q (finFunctionFinEquiv.symm a j)

/-- A configuration as a vector over `ZMod q`, indexed by coordinates. -/
def toVec {n : ℕ} (x : Config n (q ^ k)) : Coord n k → ZMod q := fun p ↦ digits (x p.1) p.2

/-- Configurations and coordinate vectors correspond. -/
def vecEquiv (n : ℕ) : Config n (q ^ k) ≃ (Coord n k → ZMod q) :=
  (Equiv.arrowCongr (Equiv.refl (Fin n))
      (finFunctionFinEquiv.symm.trans
        (Equiv.arrowCongr (Equiv.refl (Fin k)) (ZMod.finEquiv q).toEquiv))).trans
    (Equiv.curry (Fin n) (Fin k) (ZMod q)).symm

lemma vecEquiv_apply {n : ℕ} (x : Config n (q ^ k)) : vecEquiv n x = toVec x := rfl

lemma toVec_injective {n : ℕ} : Function.Injective (toVec (q := q) (k := k) (n := n)) :=
  (vecEquiv n).injective

/-- The normalising constant `q^(-nk/2)`. -/
noncomputable def normConst (q n k : ℕ) : ℂ := ((Real.sqrt ((q : ℝ) ^ (n * k)) : ℝ) : ℂ)⁻¹

lemma normConst_mul_star (q n k : ℕ) :
    normConst q n k * star (normConst q n k) = ((q : ℂ) ^ (n * k))⁻¹ := by
  have h : 0 ≤ (q : ℝ) ^ (n * k) := by positivity
  simp only [normConst, star_inv₀, Complex.star_def, Complex.conj_ofReal]
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt h]
  push_cast
  rfl

/-- The graph state of `U`: amplitude `q^(-nk/2) · χ(xᵀ U x)` at every configuration `x`. -/
noncomputable def graphState {n : ℕ} (U : Matrix (Coord n k) (Coord n k) (ZMod q)) :
    StateVector n (q ^ k) :=
  mkStateVector fun x ↦ normConst q n k * χ (quad U (toVec x))

/-- The cut condition for a set `A` of parties and a matrix `S` on the coordinates: a vector
supported on the coordinates of `A` whose products with the columns of `S` outside `A` all vanish
is zero. For `S = U + Uᵀ` this says the block of `S` from the coordinates of `A` to the rest has
full row rank. -/
def CutInj {n : ℕ} (S : Matrix (Coord n k) (Coord n k) (ZMod q)) (A : Finset (Fin n)) : Prop :=
  ∀ w : Coord n k → ZMod q, (∀ p : Coord n k, p.1 ∉ A → w p = 0) →
    (∀ c : Coord n k, c.1 ∉ A → ∑ p, w p * S p c = 0) → w = 0

/-- A character of a sum is the product of the characters. -/
lemma χ_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod q) :
    χ (∑ i ∈ s, f i) = ∏ i ∈ s, χ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

/-- The character sum over one level: `∑ t, χ(t · e)` is `q` if `e = 0` and `0` otherwise. -/
lemma sum_χ_mul (e : ZMod q) : ∑ t : ZMod q, χ (t * e) = if e = 0 then (q : ℂ) else 0 := by
  rw [AddChar.sum_mulShift e (ZMod.isPrimitive_stdAddChar q)]
  split_ifs <;> simp

/-- The character sum over many levels: `∑ z, χ(∑ j, z j · e j)` is `q^|ι|` if `e = 0` and `0`
otherwise. -/
lemma sum_χ_dot {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι → ZMod q) :
    ∑ z : ι → ZMod q, χ (∑ j, z j * e j) = if e = 0 then (q : ℂ) ^ Fintype.card ι else 0 := by
  simp_rw [χ_sum]
  rw [← Fintype.prod_sum (fun j t ↦ χ (t * e j))]
  simp_rw [sum_χ_mul]
  split_ifs with he
  · simp [he]
  · obtain ⟨j, hj⟩ := Function.ne_iff.mp he
    exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)

omit [NeZero q] in
/-- `xᵀ U x` at `y + w`, expanded: the cross terms are `∑ j, (∑ i, w i · S i j) · y j` with
`S = U + Uᵀ`. -/
lemma quad_add {ι : Type*} [Fintype ι] (U : Matrix ι ι (ZMod q)) (y w : ι → ZMod q) :
    quad U (y + w) = quad U y + quad U w + ∑ j, (∑ i, w i * (U + Uᵀ) i j) * y j := by
  simp only [quad, Pi.add_apply, Matrix.add_apply, Matrix.transpose_apply]
  have h1 : ∑ j, (∑ i, w i * (U i j + U j i)) * y j =
      ∑ i, ∑ j, U i j * w i * y j + ∑ i, ∑ j, U i j * y i * w j := by
    simp_rw [Finset.sum_mul, mul_add, add_mul, Finset.sum_add_distrib]
    rw [Finset.sum_comm]
    congr 1
    · exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
    · exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
  rw [h1]
  simp_rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring

/-- A sum over `Fin n` splits into the first `m` indices and the last `n - m`. -/
lemma sum_split {n m : ℕ} (hm : m ≤ n) {M : Type*} [AddCommMonoid M] (f : Fin n → M) :
    ∑ i, f i = ∑ i : Fin m, f (leftIndex hm i) + ∑ j : Fin (n - m), f (rightIndex hm j) := by
  have e : m + (n - m) = n := by omega
  rw [← Fin.sum_congr' f e, Fin.sum_univ_add]
  rfl

/-- A sum over coordinates splits into the coordinates of the first `m` parties and the rest. -/
lemma sum_coord_split {n m : ℕ} (hm : m ≤ n) {M : Type*} [AddCommMonoid M] (f : Coord n k → M) :
    ∑ p, f p = ∑ p : Coord m k, f (leftIndex hm p.1, p.2) +
      ∑ p : Coord (n - m) k, f (rightIndex hm p.1, p.2) := by
  simp only [Fintype.sum_prod_type]
  exact sum_split hm (fun i ↦ ∑ j, f (i, j))

/-- The graph state is normalised, for any number of parties. -/
theorem graphState_isNormalized {n : ℕ} (U : Matrix (Coord n k) (Coord n k) (ZMod q)) :
    IsNormalized (graphState U) := by
  rw [isNormalized_iff_norm_sq_eq_one, EuclideanSpace.norm_sq_eq]
  have h : ∀ x : Config n (q ^ k), ‖(graphState U).ofLp x‖ ^ 2 = ((q : ℝ) ^ (n * k))⁻¹ := by
    intro x
    have hpos : 0 ≤ (q : ℝ) ^ (n * k) := by positivity
    simp only [graphState, normConst, mkStateVector_apply, norm_mul, norm_inv,
      Complex.norm_real, AddChar.norm_apply, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt hpos]
  simp_rw [h]
  rw [Finset.sum_const, Finset.card_univ, card_config, nsmul_eq_mul]
  have hq : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  push_cast
  rw [← pow_mul, mul_comm k n]
  exact mul_inv_cancel₀ (pow_ne_zero _ hq)

/-- Permuting the parties, as a permutation of coordinates. -/
def coordPerm (π : Equiv.Perm (Fin n)) : Equiv.Perm (Coord n k) :=
  Equiv.prodCongr π (Equiv.refl (Fin k))

omit [NeZero q] in
/-- The quadratic form of a permuted vector is the form of the permuted matrix. -/
lemma quad_perm {ι : Type*} [Fintype ι] (U : Matrix ι ι (ZMod q)) (σ : Equiv.Perm ι)
    (x : ι → ZMod q) : quad U (fun i ↦ x (σ i)) = quad (U.submatrix σ.symm σ.symm) x := by
  symm
  unfold quad
  rw [← Equiv.sum_comp σ]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Equiv.sum_comp σ]
  simp

/-- Permuting the parties of a graph state gives the graph state of the permuted matrix. -/
theorem permuteState_graphState {n : ℕ} (π : Equiv.Perm (Fin n))
    (U : Matrix (Coord n k) (Coord n k) (ZMod q)) :
    permuteState π (graphState U) =
      graphState (U.submatrix (coordPerm π).symm (coordPerm π).symm) := by
  ext x
  rw [permuteState_apply]
  simp only [graphState, mkStateVector_apply]
  rw [show toVec (permuteConfig π x) = fun p ↦ toVec x (coordPerm (k := k) π p) from rfl,
    quad_perm]

omit [NeZero q] in
/-- Permuting the matrix moves the cut: the cut condition for `A` and the permuted matrix
follows from the cut condition for the image of `A`. -/
lemma CutInj.submatrix {n : ℕ} {S : Matrix (Coord n k) (Coord n k) (ZMod q)}
    (π : Equiv.Perm (Fin n)) {A : Finset (Fin n)} (h : CutInj S (A.map π.symm.toEmbedding)) :
    CutInj (S.submatrix (coordPerm π).symm (coordPerm π).symm) A := by
  intro w hw hcol
  have hmem : ∀ i : Fin n, π i ∈ A → i ∈ A.map π.symm.toEmbedding := fun i hi ↦ by
    simpa using Finset.mem_map_of_mem π.symm.toEmbedding hi
  have hz := h (fun p ↦ w (coordPerm π p))
    (fun p hp ↦ hw (coordPerm π p) fun h' ↦ hp (hmem p.1 h'))
    (fun c hc ↦ by
      have hc' : (coordPerm π c).1 ∉ A := fun h' ↦ hc (hmem c.1 h')
      have := hcol (coordPerm π c) hc'
      simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply] at this
      rw [← this, ← Equiv.sum_comp (coordPerm π) (fun p ↦ w p * S ((coordPerm π).symm p) c)]
      simp)
  funext p
  simpa using congrFun hz ((coordPerm π).symm p)

/-- The first `m` parties. -/
def firstHalf (n m : ℕ) : Finset (Fin n) := Finset.univ.filter fun i ↦ i.1 < m

lemma card_firstHalf {n m : ℕ} (hm : m ≤ n) : (firstHalf n m).card = m := by
  simp [firstHalf, Fin.card_filter_val_lt, hm]

/-- A vector on the coordinates of the first `m` parties, extended by zero. -/
def lift {n m : ℕ} (v : Coord m k → ZMod q) : Coord n k → ZMod q :=
  fun p ↦ if hi : p.1.1 < m then v (⟨p.1.1, hi⟩, p.2) else 0

omit [NeZero q] in
lemma lift_left {n m : ℕ} (hm : m ≤ n) (v : Coord m k → ZMod q) (p : Coord m k) :
    lift (n := n) v (leftIndex hm p.1, p.2) = v p := by
  simp [lift, leftIndex, p.1.2]

omit [NeZero q] in
lemma lift_right {n m : ℕ} (hm : m ≤ n) (v : Coord m k → ZMod q) (p : Coord (n - m) k) :
    lift (n := n) v (rightIndex hm p.1, p.2) = 0 := by
  simp [lift, rightIndex]

lemma toVec_combineFirst_left {n m : ℕ} (hm : m ≤ n) (a : Config m (q ^ k))
    (z : Config (n - m) (q ^ k)) (p : Coord m k) :
    toVec (combineFirst m hm a z) (leftIndex hm p.1, p.2) = toVec a p := by
  simp [toVec, combineFirst_leftIndex]

lemma toVec_combineFirst_right {n m : ℕ} (hm : m ≤ n) (a : Config m (q ^ k))
    (z : Config (n - m) (q ^ k)) (p : Coord (n - m) k) :
    toVec (combineFirst m hm a z) (rightIndex hm p.1, p.2) = toVec z p := by
  simp [toVec, combineFirst_rightIndex]

/-- Changing the kept levels from `b` to `a` adds the difference, extended by zero. -/
lemma toVec_combineFirst_eq {n m : ℕ} (hm : m ≤ n) (a b : Config m (q ^ k))
    (z : Config (n - m) (q ^ k)) :
    toVec (combineFirst m hm a z) = toVec (combineFirst m hm b z) + lift (toVec a - toVec b) := by
  funext p
  simp only [Pi.add_apply, toVec, lift, combineFirst]
  split_ifs <;> simp [toVec]

/-- The coefficient vector of the traced levels in `xᵀ U x - yᵀ U y`. -/
def coeff {n m : ℕ} (hm : m ≤ n) (S : Matrix (Coord n k) (Coord n k) (ZMod q))
    (d : Coord m k → ZMod q) : Coord (n - m) k → ZMod q :=
  fun c ↦ ∑ p, lift d p * S p (rightIndex hm c.1, c.2)

/-- The entries of the first-`m` reduction of a graph state, as a character sum evaluated:
`q^(-nk)` times a phase depending only on `a, b`, times `q^((n-m)k)` if the traced coefficients
vanish and `0` otherwise. -/
theorem reduced_graphState {n m : ℕ} (hm : m ≤ n) (U : Matrix (Coord n k) (Coord n k) (ZMod q))
    (a b : Config m (q ^ k)) :
    ∃ K : ZMod q, (toVec a = toVec b → K = 0) ∧ reducedDensityFirst m hm (graphState U) a b =
      ((q : ℂ) ^ (n * k))⁻¹ * χ K *
        (if coeff hm (U + Uᵀ) (toVec a - toVec b) = 0 then (q : ℂ) ^ ((n - m) * k) else 0) := by
  set d := toVec a - toVec b
  set K₀ : ZMod q := quad U (lift d) +
    ∑ p : Coord m k, (∑ l, lift d l * (U + Uᵀ) l (leftIndex hm p.1, p.2)) * toVec b p
  refine ⟨K₀, fun hab ↦ ?_, ?_⟩
  · have hd : d = 0 := sub_eq_zero.mpr hab
    have hl : lift (n := n) d = 0 := by
      funext p
      simp [lift, hd]
    simp [K₀, hl, quad]
  have hdiff : ∀ z : Config (n - m) (q ^ k),
      quad U (toVec (combineFirst m hm a z)) - quad U (toVec (combineFirst m hm b z)) =
        K₀ + ∑ c, toVec z c * coeff hm (U + Uᵀ) d c := by
    intro z
    rw [toVec_combineFirst_eq hm a b z, quad_add, sum_coord_split hm]
    simp only [toVec_combineFirst_left, toVec_combineFirst_right, coeff, K₀]
    rw [Finset.sum_congr rfl fun c _ ↦ mul_comm
      (∑ l, lift d l * (U + Uᵀ) l (rightIndex hm c.1, c.2)) (toVec z c)]
    ring
  have hterm : ∀ z : Config (n - m) (q ^ k),
      graphState U (combineFirst m hm a z) * star (graphState U (combineFirst m hm b z)) =
        ((q : ℂ) ^ (n * k))⁻¹ * χ (K₀ + ∑ c, toVec z c * coeff hm (U + Uᵀ) d c) := by
    intro z
    rw [← hdiff z, sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_neg_eq_conj,
      ← normConst_mul_star]
    simp only [graphState, mkStateVector_apply, star_mul', starRingEnd_apply]
    ring
  have hsum : ∑ z : Config (n - m) (q ^ k), χ (∑ c, toVec z c * coeff hm (U + Uᵀ) d c) =
      ∑ v : Coord (n - m) k → ZMod q, χ (∑ c, v c * coeff hm (U + Uᵀ) d c) :=
    Fintype.sum_equiv (vecEquiv (n - m)) _ _ fun _ ↦ rfl
  rw [reducedDensityFirst]
  simp_rw [hterm, AddChar.map_add_eq_mul, ← Finset.mul_sum]
  rw [hsum, sum_χ_dot]
  simp only [Fintype.card_prod, Fintype.card_fin]
  ring

/-- The first-half reduction of a graph state is maximally mixed when the cut condition holds
for the first half. -/
theorem graphState_firstHalf {n : ℕ} (U : Matrix (Coord n k) (Coord n k) (ZMod q))
    (h : CutInj (U + Uᵀ) (firstHalf n (n / 2))) :
    HasMaximallyMixedFirstReduction (n / 2) (Nat.div_le_self n 2) (graphState U) := by
  have hm := Nat.div_le_self n 2
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  ext a b
  obtain ⟨K, hK0, hK⟩ := reduced_graphState hm U a b
  rw [hK, maximallyMixed_apply, card_config]
  have hexp : n * k = (n - n / 2) * k + n / 2 * k := by
    rw [← add_mul, Nat.sub_add_cancel hm]
  by_cases hab : a = b
  · subst hab
    have h0 : coeff hm (U + Uᵀ) (toVec a - toVec a) = 0 := by
      funext c
      simp [coeff, lift]
    rw [hK0 rfl, if_pos h0, if_pos rfl, hexp, pow_add]
    push_cast
    rw [← pow_mul, mul_comm k (n / 2)]
    field_simp
    simp
  · have hne : coeff hm (U + Uᵀ) (toVec a - toVec b) ≠ 0 := by
      intro hc
      apply hab
      have hw := h (lift (toVec a - toVec b)) (fun p hp ↦ by
          simp only [firstHalf, Finset.mem_filter, Finset.mem_univ, true_and] at hp
          simp [lift, hp]) (fun c hc' ↦ by
          simp only [firstHalf, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hc'
          have hjk : rightIndex hm ⟨c.1.1 - n / 2, by omega⟩ = c.1 := by
            ext
            simp [rightIndex]
            omega
          have := congrFun hc (⟨c.1.1 - n / 2, by omega⟩, c.2)
          simpa [coeff, hjk] using this)
      apply toVec_injective
      funext p
      have hp := congrFun hw (leftIndex hm p.1, p.2)
      rw [lift_left] at hp
      exact sub_eq_zero.mp hp
    rw [if_neg hne, if_neg hab]
    ring

/-- **A graph state over `ZMod q` is AME** when, for every set `A` of `n / 2` parties, the block
of `U + Uᵀ` from the coordinates of `A` to the rest is injective. Any number of parties. -/
theorem graphState_isAME {n : ℕ} (U : Matrix (Coord n k) (Coord n k) (ZMod q))
    (h : ∀ A : Finset (Fin n), A.card = n / 2 → CutInj (U + Uᵀ) A) :
    IsAME (graphState U) := by
  refine ⟨graphState_isNormalized U, fun π ↦ ?_⟩
  rw [permuteState_graphState]
  apply graphState_firstHalf
  have e : U.submatrix (coordPerm π).symm (coordPerm π).symm +
      (U.submatrix (coordPerm π).symm (coordPerm π).symm)ᵀ =
      (U + Uᵀ).submatrix (coordPerm π).symm (coordPerm π).symm := by
    ext i j
    simp
  rw [e]
  exact CutInj.submatrix π (h _ (by rw [Finset.card_map, card_firstHalf (Nat.div_le_self n 2)]))

end AME7
