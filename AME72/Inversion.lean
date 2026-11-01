/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import AME72.Relations

/-!
# The state inversion on a set of qubits

For a set `A` of qubits, `inv A X = σ_y^{⊗A} Xᵀ σ_y^{⊗A}`, where the `σ_y` factors act on the qubits
in `A` and `ᵀ` is the transpose on all `n` qubits. On `ρ_A ⊗ 1` this agrees with the partial
transpose on `A`, since the identity on the other qubits is symmetric. On all qubits this is
Wootters' spin flip (S. Hill and W. K. Wootters, PRL 78, 5022 (1997); Wootters, PRL 80, 2245
(1998)), which Wyderka, Huber and Gühne call the state inversion (*Constraints on correlations in
multiqubit systems*, PRA 97, 060101 (2018), eq. (5)). Written out, `inv A X` at `(x, y)` is `X` at
`(ȳ, x̄)`, where `x̄` flips the qubits of `x` in `A`, times a sign `-1` for each qubit of `A` on
which `x` and `y` differ.

Two facts are proved, both one qubit at a time:

* `inv_mul`: it reverses products, `inv A (X * Y) = inv A Y * inv A X`;
* `inv_red`: on a reduced state it is an alternating sum of the smaller reductions,
  `inv A (ρ_A ⊗ 1) = ∑_{U ⊆ A} (-1)^|U| ρ_U ⊗ 1` (Wyderka, Huber and Gühne, eq. (10), citing
  W. Hall, PRA 72, 022311 (2005)). On one qubit this is `σ_y Mᵀ σ_y = tr(M) · 1 - M`.
-/

@[expose] public section

namespace AME72

open OpenQuantumProblem35 Finset

variable {n : ℕ}

/-- Flip one qubit if `b`. -/
def fl (b : Bool) (x : Fin 2) : Fin 2 := if b then x + 1 else x

/-- The sign on one qubit: `-1` if `b` and the two values differ. -/
def sg (b : Bool) (x y : Fin 2) : ℤ := if b ∧ x ≠ y then -1 else 1

/-- Flip the qubits in `A`. -/
def flipOn (A : Finset (Fin n)) (x : Config n 2) : Config n 2 := fun i ↦ fl (decide (i ∈ A)) (x i)

/-- The sign `(-1)^(number of qubits of A on which x and y differ)`. -/
def sgnOn (A : Finset (Fin n)) (x y : Config n 2) : ℂ := ∏ i, (sg (decide (i ∈ A)) (x i) (y i) : ℂ)

/-- **The state inversion on the qubits in `A`**: `σ_y^{⊗A} Xᵀ σ_y^{⊗A}`. -/
noncomputable def inv (A : Finset (Fin n)) (X : Matrix (Config n 2) (Config n 2) ℂ) :
    Matrix (Config n 2) (Config n 2) ℂ :=
  fun x y ↦ sgnOn A x y * X (flipOn A y) (flipOn A x)

lemma fl_fl : ∀ (b : Bool) (x : Fin 2), fl b (fl b x) = x := by decide

lemma flipOn_flipOn (A : Finset (Fin n)) (x : Config n 2) : flipOn A (flipOn A x) = x :=
  funext fun _ ↦ fl_fl _ _

/-- Flipping the qubits in `A`, as a permutation of configurations. -/
def flipEquiv (A : Finset (Fin n)) : Config n 2 ≃ Config n 2 where
  toFun := flipOn A
  invFun := flipOn A
  left_inv := flipOn_flipOn A
  right_inv := flipOn_flipOn A

/-- One qubit: the signs multiply through any middle value. -/
lemma sg_mul : ∀ (b : Bool) (x y c : Fin 2), sg b x c * sg b c y = sg b x y := by
  decide

lemma sgnOn_mul (A : Finset (Fin n)) (x y c : Config n 2) :
    sgnOn A x c * sgnOn A c y = sgnOn A x y := by
  simp only [sgnOn, ← prod_mul_distrib]
  refine prod_congr rfl fun _ _ ↦ ?_
  exact_mod_cast sg_mul _ _ _ _

/-- **The inversion reverses products.** -/
theorem inv_mul (A : Finset (Fin n)) (X Y : Matrix (Config n 2) (Config n 2) ℂ) :
    inv A (X * Y) = inv A Y * inv A X := by
  ext x y
  simp only [inv, Matrix.mul_apply, mul_sum]
  rw [← (flipEquiv A).sum_comp]
  refine sum_congr rfl fun c _ ↦ ?_
  simp only [flipEquiv, Equiv.coe_fn_mk]
  rw [← sgnOn_mul A x y c]
  ring

/-- The inversion is linear. -/
lemma inv_smul (A : Finset (Fin n)) (c : ℂ) (X : Matrix (Config n 2) (Config n 2) ℂ) :
    inv A (c • X) = c • inv A X := by
  ext x y
  simp only [inv, Matrix.smul_apply, smul_eq_mul]
  ring

/-- One qubit, `σ_y Mᵀ σ_y = tr(M) · 1 - M`, on the kernel: inside `A` the inverted kept factor is
the traced factor minus the kept one; outside `A` nothing changes. -/
lemma sg_kern : ∀ (b : Bool) (x x' p q : Fin 2),
    sg b x x' * kern b (fl b x') (fl b x) p q =
      if b then -(kern true x x' p q : ℤ) + kern false x x' p q else kern false x x' p q := by
  decide

/-- The kernel identity behind `inv_red`. -/
lemma kern_inv (A : Finset (Fin n)) (x x' p q : Config n 2) :
    sgnOn A x x' * kernProd A (flipOn A x') (flipOn A x) p q =
      ∑ U ∈ A.powerset, (-1 : ℂ) ^ U.card * kernProd U x x' p q := by
  let keep : Fin n → ℂ := fun i ↦ (kern true (x i) (x' i) (p i) (q i) : ℂ)
  let trace : Fin n → ℂ := fun i ↦ (kern false (x i) (x' i) (p i) (q i) : ℂ)
  have hL : sgnOn A x x' * kernProd A (flipOn A x') (flipOn A x) p q =
      (∏ i ∈ A, (-keep i + trace i)) * ∏ i ∈ Aᶜ, trace i := by
    simp only [sgnOn, kernProd, flipOn, ← prod_mul_distrib]
    rw [← prod_mul_prod_compl A]
    congr 1
    · refine prod_congr rfl fun i hi ↦ ?_
      have h := congrArg (fun z : ℤ ↦ (z : ℂ)) (sg_kern true (x i) (x' i) (p i) (q i))
      simp only [hi, decide_true, ite_true] at h ⊢
      push_cast at h ⊢
      simpa [keep, trace] using h
    · refine prod_congr rfl fun i hi ↦ ?_
      have h := congrArg (fun z : ℤ ↦ (z : ℂ)) (sg_kern false (x i) (x' i) (p i) (q i))
      rw [mem_compl] at hi
      simp only [hi, decide_false, Bool.false_eq_true, ite_false] at h ⊢
      push_cast at h ⊢
      simpa [trace] using h
  have hR : ∀ U ∈ A.powerset, (-1 : ℂ) ^ U.card * kernProd U x x' p q =
      (∏ i ∈ U, -keep i) * (∏ i ∈ A \ U, trace i) * ∏ i ∈ Aᶜ, trace i := by
    intro U hU
    rw [mem_powerset] at hU
    rw [kernProd, ← prod_mul_prod_compl A, ← prod_sdiff hU]
    have h₁ : ∏ i ∈ A \ U, (kern (decide (i ∈ U)) (x i) (x' i) (p i) (q i) : ℂ) =
        ∏ i ∈ A \ U, trace i :=
      prod_congr rfl fun i hi ↦ by simp [trace, (mem_sdiff.mp hi).2]
    have h₂ : ∏ i ∈ U, (kern (decide (i ∈ U)) (x i) (x' i) (p i) (q i) : ℂ) = ∏ i ∈ U, keep i :=
      prod_congr rfl fun i hi ↦ by simp [keep, hi]
    have h₃ : ∏ i ∈ Aᶜ, (kern (decide (i ∈ U)) (x i) (x' i) (p i) (q i) : ℂ) =
        ∏ i ∈ Aᶜ, trace i :=
      prod_congr rfl fun i hi ↦ by
        have : i ∉ U := fun h ↦ (mem_compl.mp hi) (hU h)
        simp [trace, this]
    have h₄ : ∏ i ∈ U, -keep i = (-1 : ℂ) ^ U.card * ∏ i ∈ U, keep i := by
      rw [← prod_const, ← prod_mul_distrib]
      exact prod_congr rfl fun i _ ↦ by ring
    rw [h₁, h₂, h₃, h₄]
    ring
  rw [hL, sum_congr rfl hR, ← sum_mul, prod_add]

/-- **The inversion of a reduced state.** `inv A (ρ_A ⊗ 1) = ∑_{U ⊆ A} (-1)^|U| ρ_U ⊗ 1`. -/
theorem inv_red (A : Finset (Fin n)) (X : Matrix (Config n 2) (Config n 2) ℂ) :
    inv A (red A X) = ∑ U ∈ A.powerset, ((-1 : ℂ) ^ U.card) • red U X := by
  ext x x'
  -- The kernel identity, one qubit at a time.
  have key : ∀ p q : Config n 2, sgnOn A x x' * kernProd A (flipOn A x') (flipOn A x) p q =
      ∑ U ∈ A.powerset, (-1 : ℂ) ^ U.card * kernProd U x x' p q := by
    intro p q
    exact kern_inv A x x' p q
  simp only [Matrix.sum_apply, inv, red, Matrix.smul_apply, smul_eq_mul, mul_sum]
  calc ∑ p, ∑ q, sgnOn A x x' * (kernProd A (flipOn A x') (flipOn A x) p q * X p q)
      = ∑ p, ∑ q, ∑ U ∈ A.powerset, (-1 : ℂ) ^ U.card * (kernProd U x x' p q * X p q) :=
        sum_congr rfl fun p _ ↦ sum_congr rfl fun q _ ↦ by
          rw [← mul_assoc, key, sum_mul]
          exact sum_congr rfl fun U _ ↦ by ring
    _ = _ := (sum_comm.trans (sum_congr rfl fun _ _ ↦ sum_comm)).symm

end AME72
