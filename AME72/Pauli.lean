/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import AME72.Kernel

/-!
# Pauli strings and the parity rule

We use the real form of the Pauli basis on one qubit, `1, X, Z, XZ` (with `XZ = -i Y`), indexed by
`Fin 4` as `0, 1, 2, 3`: index `a` stands for `X^(a mod 2) Z^(a / 2)`. All entries are `0` or `± 1`,
so every one-qubit fact is checked by `decide` over the integers. A *Pauli string* on `n` qubits is
`α : Fin n → Fin 4`, and `tau α` is the tensor product of the one-qubit matrices. Its *weight* is
the number of qubits where it is not the identity.

Up to the phases `± i` on each `Y`, these are the Pauli strings of Huber, Gühne and Siewert
(PRL 118, 200502 (2017)), with the same weights, so the even and odd parts of an operator are the
same in either basis.

* `tau_mul`: `τ_α τ_β = ± τ_{α + β}`, where `+` is addition in `(ZMod 2)²` on each qubit;
* `parity_rule` (**the parity rule**, their Lemma 1): if `{τ_α, τ_β} ≠ 0`, then
  `wt(α + β) ≡ wt α + wt β (mod 2)`.
-/

@[expose] public section

namespace AME72

open OpenQuantumProblem35 Finset

variable {n : ℕ}

/-- The one-qubit basis `1, X, Z, XZ`, as integer matrices. -/
def tau1 : Fin 4 → Fin 2 → Fin 2 → ℤ :=
  ![![![1, 0], ![0, 1]], ![![0, 1], ![1, 0]], ![![1, 0], ![0, -1]], ![![0, -1], ![1, 0]]]

/-- Multiplication of indices: addition in `(ZMod 2)²`, i.e. bitwise exclusive or. -/
def mul1 : Fin 4 → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3], ![1, 0, 3, 2], ![2, 3, 0, 1], ![3, 2, 1, 0]]

/-- The sign in `τ_a τ_b = sgn1 a b · τ_{a + b}`: `-1` exactly when `a` has a `Z` and `b` an `X`. -/
def sgn1 : Fin 4 → Fin 4 → ℤ :=
  ![![1, 1, 1, 1], ![1, 1, 1, 1], ![1, -1, 1, -1], ![1, -1, 1, -1]]

/-- Whether a one-qubit index is not the identity, as `0` or `1`. -/
def wt1 (a : Fin 4) : ℕ := if a = 0 then 0 else 1

/-- The Pauli string `τ_α = ⊗ τ_{α i}`. -/
def tau (α : Fin n → Fin 4) : Matrix (Config n 2) (Config n 2) ℂ :=
  fun x y ↦ ∏ i, (tau1 (α i) (x i) (y i) : ℂ)

/-- The product of two Pauli strings, as indices. -/
def mulStr (α β : Fin n → Fin 4) : Fin n → Fin 4 := fun i ↦ mul1 (α i) (β i)

/-- The sign of the product of two Pauli strings. -/
def sgnStr (α β : Fin n → Fin 4) : ℂ := ∏ i, (sgn1 (α i) (β i) : ℂ)

/-- The weight of a Pauli string: the number of qubits where it is not the identity. -/
def weight (α : Fin n → Fin 4) : ℕ := ∑ i, wt1 (α i)

/-- A sum over configurations of a product of one-qubit factors, for any finite set of values. -/
lemma sum_prod_eq' {β : Type*} [Fintype β] (f : Fin n → β → ℂ) :
    ∑ p : Fin n → β, ∏ i, f i (p i) = ∏ i, ∑ s, f i s :=
  (Fintype.prod_sum f).symm

/-- One qubit: `τ_a τ_b = sgn1 a b · τ_{a + b}`. -/
lemma tau1_mul : ∀ (a b : Fin 4) (s u : Fin 2),
    ∑ t : Fin 2, tau1 a s t * tau1 b t u = sgn1 a b * tau1 (mul1 a b) s u := by
  decide

/-- **Products of Pauli strings.** `τ_α τ_β = sgnStr α β · τ_{α + β}`. -/
theorem tau_mul (α β : Fin n → Fin 4) : tau α * tau β = sgnStr α β • tau (mulStr α β) := by
  ext x y
  simp only [Matrix.mul_apply, tau, ← prod_mul_distrib, Matrix.smul_apply, smul_eq_mul, sgnStr,
    mulStr]
  rw [sum_prod_eq (fun i t ↦ (tau1 (α i) (x i) t : ℂ) * (tau1 (β i) t (y i) : ℂ))]
  refine prod_congr rfl fun i _ ↦ ?_
  exact_mod_cast tau1_mul (α i) (β i) (x i) (y i)

/-- The two orders of one qubit's product have the same index. -/
lemma mul1_comm : ∀ a b : Fin 4, mul1 b a = mul1 a b := by decide

/-- Whether `τ_a` and `τ_b` anticommute on one qubit. -/
def anti1 (a b : Fin 4) : Prop := sgn1 b a = -sgn1 a b

instance (a b : Fin 4) : Decidable (anti1 a b) := inferInstanceAs (Decidable (_ = _))

/-- One qubit: the two orders differ by the sign `-1` exactly on anticommuting pairs. -/
lemma sgn1_comm : ∀ a b : Fin 4, sgn1 b a = (if anti1 a b then -1 else 1) * sgn1 a b := by
  decide

/-- One qubit: the weight changes parity exactly on anticommuting pairs. -/
lemma wt1_parity : ∀ a b : Fin 4,
    ((wt1 (mul1 a b) : ZMod 2) + wt1 a + wt1 b) = if anti1 a b then 1 else 0 := by
  decide

/-- The number of qubits where `τ_α` and `τ_β` anticommute. -/
def anti (α β : Fin n → Fin 4) : ℕ := (univ.filter fun i ↦ anti1 (α i) (β i)).card

/-- The signs of the two orders differ by `(-1)^(anticommuting qubits)`. -/
lemma sgnStr_comm (α β : Fin n → Fin 4) :
    sgnStr β α = (-1) ^ anti α β * sgnStr α β := by
  have h : ∀ i, (sgn1 (β i) (α i) : ℂ) =
      (if anti1 (α i) (β i) then -1 else 1) * (sgn1 (α i) (β i) : ℂ) := by
    intro i
    have := sgn1_comm (α i) (β i)
    split_ifs at this ⊢ <;> push_cast [this] <;> ring
  simp only [sgnStr, h, prod_mul_distrib, prod_ite, prod_const, one_pow, mul_one, anti]

/-- The weights of `α`, `β` and `α + β` add up to the number of anticommuting qubits, mod 2. -/
lemma weight_parity (α β : Fin n → Fin 4) :
    ((weight (mulStr α β) + weight α + weight β : ℕ) : ZMod 2) = (anti α β : ZMod 2) := by
  simp only [weight, mulStr, anti, Nat.cast_add, Nat.cast_sum, ← sum_add_distrib, wt1_parity,
    natCast_card_filter]

/-- **The parity rule** (Huber, Gühne and Siewert 2017, Lemma 1). If two Pauli strings do not
anticommute, i.e. `{τ_α, τ_β} ≠ 0`, then the weight of their product has the parity of the sum of
their weights. -/
theorem parity_rule (α β : Fin n → Fin 4) :
    tau α * tau β + tau β * tau α = 0 ∨ Even (weight (mulStr α β) + weight α + weight β) := by
  have hmul : mulStr β α = mulStr α β := funext fun i ↦ mul1_comm (α i) (β i)
  rcases Nat.even_or_odd (anti α β) with h | h
  · right
    rw [← ZMod.natCast_eq_zero_iff_even, weight_parity, ZMod.natCast_eq_zero_iff_even]
    exact h
  · left
    rw [tau_mul, tau_mul, hmul, sgnStr_comm α β, h.neg_one_pow, ← add_smul]
    simp

end AME72
