/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import AME7.Defs

/-!
# Reduced states on any set of qubits, one qubit at a time

For a set `U` of qubits and an operator `X` on `n` qubits, `red U X` is `tr_{Uᶜ}(X) ⊗ 1_{Uᶜ}`:
trace out the qubits outside `U`, then put the identity back on them. Its entries are a sum over
pairs of configurations of a product of single-qubit factors (`kern`), one per qubit:

* on a qubit in `U` the factor reads the entry `|p⟩⟨q|` at `(x, x')`;
* on a qubit outside `U` it is `δ(x, x') δ(p, q)`.

Because every factor depends on one qubit only, a sum over configurations of such a product is the
product over qubits of a sum over `Fin 2` (`sum_prod_eq`). So every identity between these
operators comes down to a statement about one qubit, which `decide` checks.

This file proves the two identities used later: tracing out in two steps
(`red_red`) and the reduction of the identity (`red_one`).
-/

@[expose] public section

namespace AME72

open OpenQuantumProblem35 Finset

variable {n : ℕ}

/-- The single-qubit factor of `red`: on a kept qubit, the entry of `|p⟩⟨q|` at `(x, x')`; on a
traced qubit, `δ(x, x') δ(p, q)`. -/
def kern (keep : Bool) (x x' p q : Fin 2) : ℕ :=
  if keep then (if p = x ∧ q = x' then 1 else 0) else (if x = x' ∧ p = q then 1 else 0)

/-- The product of the single-qubit factors over all qubits, as a complex number. -/
def kernProd (U : Finset (Fin n)) (x x' p q : Config n 2) : ℂ :=
  ∏ i, (kern (decide (i ∈ U)) (x i) (x' i) (p i) (q i) : ℂ)

/-- `red U X = tr_{Uᶜ}(X) ⊗ 1_{Uᶜ}`: the reduction of `X` to the qubits in `U`, as an operator on
all `n` qubits. -/
noncomputable def red (U : Finset (Fin n)) (X : Matrix (Config n 2) (Config n 2) ℂ) :
    Matrix (Config n 2) (Config n 2) ℂ :=
  fun x x' ↦ ∑ p, ∑ q, kernProd U x x' p q * X p q

/-- A sum over configurations of a product of single-qubit factors is the product over qubits of
the single-qubit sums. -/
lemma sum_prod_eq (f : Fin n → Fin 2 → ℂ) :
    ∑ p : Config n 2, ∏ i, f i (p i) = ∏ i, ∑ s, f i s :=
  (Fintype.prod_sum f).symm

/-- The same for a double sum over pairs of configurations. -/
lemma sum_sum_prod_eq (f : Fin n → Fin 2 → Fin 2 → ℂ) :
    ∑ p : Config n 2, ∑ q : Config n 2, ∏ i, f i (p i) (q i) = ∏ i, ∑ s, ∑ t, f i s t := by
  calc ∑ p : Config n 2, ∑ q : Config n 2, ∏ i, f i (p i) (q i)
      = ∑ p : Config n 2, ∏ i, ∑ t, f i (p i) t :=
        sum_congr rfl fun p _ ↦ sum_prod_eq (fun i t ↦ f i (p i) t)
    _ = _ := sum_prod_eq (fun i s ↦ ∑ t, f i s t)

/-- Bring the last two of four sums to the front. -/
lemma sum4_comm {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ a, ∑ c, ∑ d, ∑ b, f a b c d :=
        sum_congr rfl fun a _ ↦ by rw [sum_comm]; exact sum_congr rfl fun c _ ↦ sum_comm
    _ = _ := by rw [sum_comm]; exact sum_congr rfl fun c _ ↦ sum_comm

/-- `red` is linear in the operator. -/
lemma red_smul (U : Finset (Fin n)) (c : ℂ) (X : Matrix (Config n 2) (Config n 2) ℂ) :
    red U (c • X) = c • red U X := by
  ext x x'
  simp only [red, Matrix.smul_apply, smul_eq_mul, mul_sum]
  exact sum_congr rfl fun p _ ↦ sum_congr rfl fun q _ ↦ by ring

/-- One qubit, two reductions: keeping then keeping is keeping, tracing after keeping is tracing,
and tracing twice is tracing with a factor `2` (the trace of the identity on one qubit). -/
lemma kern_comp : ∀ (a b : Bool), (a = true → b = true) → ∀ x x' r s : Fin 2,
    ∑ s' : Fin 2, ∑ t' : Fin 2, kern a x x' s' t' * kern b s' t' r s =
      (if b then 1 else 2) * kern a x x' r s := by
  decide

/-- **Tracing out in two steps.** For `U ⊆ V`, reducing to `V` and then to `U` is reducing to `U`,
times `2^|Vᶜ|` from the identities that the first step put back on `Vᶜ`. -/
theorem red_red {U V : Finset (Fin n)} (hUV : U ⊆ V) (X : Matrix (Config n 2) (Config n 2) ℂ) :
    red U (red V X) = (2 : ℂ) ^ Vᶜ.card • red U X := by
  ext x x'
  simp only [red, Matrix.smul_apply, smul_eq_mul]
  -- Move the inner sum outside and collect the kernels.
  have h : ∀ r s : Config n 2,
      ∑ p : Config n 2, ∑ q : Config n 2, kernProd U x x' p q * kernProd V p q r s =
        (2 : ℂ) ^ Vᶜ.card * kernProd U x x' r s := by
    intro r s
    simp only [kernProd, ← prod_mul_distrib]
    refine (sum_sum_prod_eq (fun i a b ↦ (kern (decide (i ∈ U)) (x i) (x' i) a b : ℂ) *
      (kern (decide (i ∈ V)) a b (r i) (s i) : ℂ))).trans ?_
    have hi : ∀ i, ∑ s' : Fin 2, ∑ t' : Fin 2,
        (kern (decide (i ∈ U)) (x i) (x' i) s' t' : ℂ) * (kern (decide (i ∈ V)) s' t' (r i) (s i)) =
          (if i ∈ V then 1 else 2) * (kern (decide (i ∈ U)) (x i) (x' i) (r i) (s i) : ℂ) := by
      intro i
      have := kern_comp (decide (i ∈ U)) (decide (i ∈ V))
        (by simpa using fun h ↦ hUV h) (x i) (x' i) (r i) (s i)
      have := congrArg (fun k : ℕ ↦ (k : ℂ)) this
      push_cast at this
      by_cases hV : i ∈ V <;> simpa [hV] using this
    rw [prod_congr rfl fun i _ ↦ hi i, prod_mul_distrib, prod_ite, prod_const_one, one_mul,
      prod_const]
    congr 2
    simp [filter_not, compl_eq_univ_sdiff]
  calc ∑ p, ∑ q, kernProd U x x' p q * ∑ r, ∑ s, kernProd V p q r s * X r s
      = ∑ r, ∑ s, (∑ p, ∑ q, kernProd U x x' p q * kernProd V p q r s) * X r s := by
        simp only [mul_sum, sum_mul]
        rw [sum4_comm]
        exact sum_congr rfl fun r _ ↦ sum_congr rfl fun s _ ↦ sum_congr rfl fun p _ ↦
          sum_congr rfl fun q _ ↦ by ring
    _ = _ := by
        simp only [h, mul_sum]
        exact sum_congr rfl fun r _ ↦ sum_congr rfl fun s _ ↦ by ring

/-- One qubit, the identity reduced: `1` if kept, `2` if traced, times `δ(x, x')`. -/
lemma kern_one : ∀ (a : Bool) (x x' : Fin 2),
    ∑ s : Fin 2, ∑ t : Fin 2, kern a x x' s t * (if s = t then 1 else 0) =
      (if a then 1 else 2) * (if x = x' then 1 else 0) := by
  decide

/-- **The identity, reduced.** `red U 1 = 2^|Uᶜ| · 1`. -/
theorem red_one (U : Finset (Fin n)) :
    red U (1 : Matrix (Config n 2) (Config n 2) ℂ) = (2 : ℂ) ^ Uᶜ.card • 1 := by
  ext x x'
  have hone : ∀ p q : Config n 2, (1 : Matrix (Config n 2) (Config n 2) ℂ) p q =
      ∏ i, ((if p i = q i then 1 else 0 : ℕ) : ℂ) := by
    intro p q
    rw [Matrix.one_apply]
    by_cases h : p = q
    · simp [h]
    · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
      rw [ite_eq_right h, eq_comm]
      exact prod_eq_zero (mem_univ i) (by simp [hi])
  simp only [red, kernProd, hone, ← prod_mul_distrib, Matrix.smul_apply, smul_eq_mul]
  refine (sum_sum_prod_eq (fun i a b ↦ (kern (decide (i ∈ U)) (x i) (x' i) a b : ℂ) *
    ((if a = b then 1 else 0 : ℕ) : ℂ))).trans ?_
  have hi : ∀ i, ∑ s : Fin 2, ∑ t : Fin 2,
      (kern (decide (i ∈ U)) (x i) (x' i) s t : ℂ) * ((if s = t then 1 else 0 : ℕ) : ℂ) =
        (if i ∈ U then 1 else 2) * ((if x i = x' i then 1 else 0 : ℕ) : ℂ) := by
    intro i
    have := congrArg (fun k : ℕ ↦ (k : ℂ)) (kern_one (decide (i ∈ U)) (x i) (x' i))
    push_cast at this ⊢
    by_cases hU : i ∈ U <;> simpa [hU] using this
  rw [prod_congr rfl fun i _ ↦ hi i, prod_mul_distrib, prod_ite, prod_const_one, one_mul,
    prod_const, ← hone]
  congr 2
  simp [filter_not, compl_eq_univ_sdiff]

end AME72
