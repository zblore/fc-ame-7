/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import AME72.Kernel

/-!
# Pure states: the eigenvector and projector relations

For a pure state `ψ` of `n` qubits, write `proj ψ = |ψ⟩⟨ψ|` and `red U (proj ψ) = ρ_U ⊗ 1`.
This file proves the two facts about pure states that the non-existence proof uses (Huber, Gühne
and Siewert, PRL 118, 200502 (2017), the relations before Observation 2):

* `red_mulVec_compl`: `(ρ_U ⊗ 1) ψ = (ρ_{Uᶜ} ⊗ 1) ψ`. In matrix form, with `ψ` written as a
  `U × Uᶜ` matrix `M`, this is `(M M†) M = M (M† M)`.
* `red_mul_red`: `(ρ_A ⊗ 1)² = tr_{Aᶜ}((1 ⊗ ρ_{Aᶜ}) |ψ⟩⟨ψ|) ⊗ 1`, which in matrix form is
  `(M M†)² = M (M† M) M†`.

So if `ρ_U` is maximally mixed on `U`, `(ρ_U ⊗ 1) ψ = 2^(-|U|) ψ` (`mulVec_of_maxMixed`), and so
also `(ρ_{Uᶜ} ⊗ 1) ψ = 2^(-|U|) ψ` (with `red_mulVec_compl`); and if
`ρ_{Aᶜ}` is maximally mixed, `ρ_A² = 2^(-|Aᶜ|) ρ_A` (`red_mul_red_of_maxMixed`). Neither needs the
spectral theorem or a Schmidt decomposition: both are rearrangements of finite sums, checked one
qubit at a time. A maximally mixed reduction stays maximally mixed on every smaller set
(`IsMaxMixedOn.mono`).
-/

@[expose] public section

namespace AME72

open OpenQuantumProblem35 Finset
open scoped Matrix

variable {n : ℕ}

/-- The amplitudes of a state, as a vector to multiply matrices with. -/
def vec (ψ : StateVector n 2) : Config n 2 → ℂ := fun x ↦ ψ x

/-- The projector `|ψ⟩⟨ψ|`. -/
def proj (ψ : StateVector n 2) : Matrix (Config n 2) (Config n 2) ℂ :=
  fun p q ↦ ψ p * star (ψ q)

/-- The reduced state of `ψ` on the qubits in `U` is maximally mixed: `ρ_U ⊗ 1 = 2^(-|U|) · 1`. -/
def IsMaxMixedOn (ψ : StateVector n 2) (U : Finset (Fin n)) : Prop :=
  red U (proj ψ) = ((2 : ℂ) ^ U.card)⁻¹ • 1

/-- **Maximally mixed on fewer qubits.** If the reduction of `ψ` to `V` is maximally mixed, so is
its reduction to every `U ⊆ V`: trace out `V \ U` from `2^(-|V|) · 1`. -/
theorem IsMaxMixedOn.mono {ψ : StateVector n 2} {U V : Finset (Fin n)} (h : IsMaxMixedOn ψ V)
    (hUV : U ⊆ V) : IsMaxMixedOn ψ U := by
  have key := red_red hUV (proj ψ)
  rw [h, red_smul, red_one, smul_smul] at key
  have hU := card_add_card_compl U
  have hV := card_add_card_compl V
  simp only [Fintype.card_fin] at hU hV
  have h2 : ((2 : ℂ) ^ V.card)⁻¹ * 2 ^ Uᶜ.card = (2 : ℂ) ^ Vᶜ.card * ((2 : ℂ) ^ U.card)⁻¹ := by
    have h0 : (2 : ℂ) ^ U.card * 2 ^ Uᶜ.card = 2 ^ V.card * 2 ^ Vᶜ.card := by
      rw [← pow_add, ← pow_add, hU, hV]
    field_simp
    linear_combination h0
  rw [h2, ← smul_smul] at key
  exact (smul_right_injective _ (pow_ne_zero _ two_ne_zero)) key.symm

/-- One qubit: keeping `(x, x')` with `|p⟩⟨q|` is tracing `(x, p)` with `|x'⟩⟨q|`. -/
lemma kern_compl : ∀ (b : Bool) (x x' p q : Fin 2), kern (!b) x p x' q = kern b x x' p q := by
  decide

/-- **The eigenvector relation.** `(ρ_U ⊗ 1) ψ = (ρ_{Uᶜ} ⊗ 1) ψ`. Both sides are the same triple sum
`∑ ψ(p) ψ̄(q) ψ(x')`, with the roles of `p` and `x'` exchanged. -/
theorem red_mulVec_compl (ψ : StateVector n 2) (U : Finset (Fin n)) :
    red U (proj ψ) *ᵥ vec ψ = red Uᶜ (proj ψ) *ᵥ vec ψ := by
  ext x
  have hk : ∀ x' p q : Config n 2, kernProd Uᶜ x p x' q = kernProd U x x' p q := by
    intro x' p q
    refine prod_congr rfl fun i _ ↦ ?_
    have := kern_compl (decide (i ∈ U)) (x i) (x' i) (p i) (q i)
    simp only [mem_compl, decide_not] at this ⊢
    rw [this]
  simp only [Matrix.mulVec, dotProduct, red, proj, vec, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun p _ ↦ sum_congr rfl fun x' _ ↦ sum_congr rfl fun q _ ↦ ?_
  rw [hk]
  ring

/-- If `ψ` is maximally mixed on `U`, then `(ρ_U ⊗ 1) ψ = 2^(-|U|) ψ`. -/
lemma mulVec_of_maxMixed {ψ : StateVector n 2} {U : Finset (Fin n)} (h : IsMaxMixedOn ψ U) :
    red U (proj ψ) *ᵥ vec ψ = ((2 : ℂ) ^ U.card)⁻¹ • vec ψ := by
  rw [h, Matrix.smul_mulVec, Matrix.one_mulVec]

/-- Move the first of five sums to the end. -/
lemma sum5_comm {α β γ δ ε : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] [Fintype ε]
    (f : α → β → γ → δ → ε → ℂ) :
    ∑ w, ∑ p, ∑ q, ∑ r, ∑ s, f w p q r s = ∑ p, ∑ q, ∑ r, ∑ s, ∑ w, f w p q r s :=
  sum_comm.trans (sum_congr rfl fun _ _ ↦ sum_comm.trans (sum_congr rfl fun _ _ ↦
    sum_comm.trans (sum_congr rfl fun _ _ ↦ sum_comm)))

/-- One qubit: the kernel of `(ρ_A ⊗ 1)²` at `(p, q, r, s)` is the kernel of
`tr_{Aᶜ}((1 ⊗ ρ_{Aᶜ}) |ψ⟩⟨ψ|) ⊗ 1` with `p` and `r` exchanged. -/
lemma kern_sq : ∀ (b : Bool) (x x' p q r s : Fin 2),
    ∑ t : Fin 2, kern b x t p q * kern b t x' r s =
      ∑ t : Fin 2, kern b x x' t s * kern (!b) t p r q := by
  decide

/-- **The projector relation.** `(ρ_A ⊗ 1)² = tr_{Aᶜ}((1 ⊗ ρ_{Aᶜ}) |ψ⟩⟨ψ|) ⊗ 1`. -/
theorem red_mul_red (ψ : StateVector n 2) (A : Finset (Fin n)) :
    red A (proj ψ) * red A (proj ψ) = red A (red Aᶜ (proj ψ) * proj ψ) := by
  ext x x'
  -- The two kernels agree after exchanging `p` and `r`.
  have hk : ∀ p q r s : Config n 2,
      ∑ w, kernProd A x w p q * kernProd A w x' r s =
        ∑ u, kernProd A x x' u s * kernProd Aᶜ u p r q := by
    intro p q r s
    simp only [kernProd, ← prod_mul_distrib]
    rw [sum_prod_eq (fun i t ↦ (kern (decide (i ∈ A)) (x i) t (p i) (q i) : ℂ) *
        (kern (decide (i ∈ A)) t (x' i) (r i) (s i) : ℂ)),
      sum_prod_eq (fun i t ↦ (kern (decide (i ∈ A)) (x i) (x' i) t (s i) : ℂ) *
        (kern (decide (i ∈ Aᶜ)) t (p i) (r i) (q i) : ℂ))]
    refine prod_congr rfl fun i _ ↦ ?_
    have := congrArg (fun k : ℕ ↦ (k : ℂ))
      (kern_sq (decide (i ∈ A)) (x i) (x' i) (p i) (q i) (r i) (s i))
    simp only [Nat.cast_sum, Nat.cast_mul] at this
    simpa only [mem_compl, decide_not] using this
  -- Left side: four sums over `p q r s` of the kernel times `ψ(p) ψ̄(q) ψ(r) ψ̄(s)`.
  have hL : (red A (proj ψ) * red A (proj ψ)) x x' =
      ∑ p, ∑ q, ∑ r, ∑ s, (∑ w, kernProd A x w p q * kernProd A w x' r s) *
        (ψ p * star (ψ q) * (ψ r * star (ψ s))) := by
    simp only [Matrix.mul_apply, red, proj, sum_mul, mul_sum]
    rw [sum5_comm, sum4_comm]
    exact sum_congr rfl fun p _ ↦ sum_congr rfl fun q _ ↦ sum_congr rfl fun r _ ↦
      sum_congr rfl fun s _ ↦ sum_congr rfl fun w _ ↦ by ring
  -- Right side: the same, with `p` and `r` exchanged.
  have hR : red A (red Aᶜ (proj ψ) * proj ψ) x x' =
      ∑ p, ∑ q, ∑ r, ∑ s, (∑ u, kernProd A x x' u s * kernProd Aᶜ u p r q) *
        (ψ p * star (ψ q) * (ψ r * star (ψ s))) := by
    simp only [Matrix.mul_apply, red, proj, sum_mul, mul_sum]
    -- Now `∑ u, ∑ v, ∑ c, ∑ p', ∑ q'` with `ψ(p') ψ̄(q') ψ(c) ψ̄(v)`; rename to `p q r s`.
    rw [sum5_comm]
    -- `∑ v, ∑ c, ∑ p', ∑ q', ∑ u`: bring `c, q', p'` to the front in that order.
    rw [sum_comm]
    refine sum_congr rfl fun c _ ↦ ?_
    rw [sum_comm]
    refine (sum_congr rfl fun p' _ ↦ sum_comm).trans ?_
    rw [sum_comm]
    exact sum_congr rfl fun q' _ ↦ sum_congr rfl fun p' _ ↦ sum_congr rfl fun v _ ↦
      sum_congr rfl fun u _ ↦ by ring
  rw [hL, hR]
  exact sum_congr rfl fun p _ ↦ sum_congr rfl fun q _ ↦ sum_congr rfl fun r _ ↦
    sum_congr rfl fun s _ ↦ by rw [hk]

/-- **`ρ_A² = 2^(-|Aᶜ|) ρ_A`** when the complementary reduction is maximally mixed. -/
theorem red_mul_red_of_maxMixed {ψ : StateVector n 2} {A : Finset (Fin n)}
    (h : IsMaxMixedOn ψ Aᶜ) :
    red A (proj ψ) * red A (proj ψ) = ((2 : ℂ) ^ Aᶜ.card)⁻¹ • red A (proj ψ) := by
  rw [red_mul_red, h, Matrix.smul_mul, Matrix.one_mul, red_smul]

end AME72
