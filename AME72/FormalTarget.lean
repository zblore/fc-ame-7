/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import AME72.Inversion

/-!
# The headline: no AME(7,2) state exists

Suppose `ψ` is an AME state of seven qubits, and let `A` be the first five qubits. Write
`ρ' = inv A (ρ_A ⊗ 1)`, the state inversion of the five-qubit reduction.

* **`ρ'² = ρ' / 4`.** The two-qubit rest is maximally mixed, so `ρ_A² = ρ_A / 4`
  (`red_mul_red_ame72`), and the inversion reverses products (`inv_mul`).
* **`ρ' ψ = ψ / 8`.** The inversion is `∑_{U ⊆ A} (-1)^|U| ρ_U ⊗ 1` (`inv_red`), and each
  `ρ_U ⊗ 1` acts on `ψ` as `2^(-min(|U|, 7 - |U|))` (`mulVec_ame72`). Grouping the subsets of the
  five qubits by size, `1 - 5/2 + 10/4 - 10/8 + 5/8 - 1/4 = 1/8`.

Applying `ρ'` twice then gives `ψ / 64` one way and `ψ / 32` the other, so `ψ = 0`, which is not
normalized.

This follows the structure of Huber, Gühne and Siewert, PRL 118, 200502 (2017): the projector and
eigenvector relations of a five-qubit marginal. Where they compare Bloch components using their
parity rule (Lemma 1), this proof uses the state inversion, whose reversal of products does the
same job. The tools are those of Wyderka, Huber and Gühne, PRA 97, 060101 (2018): the state
inversion (their eq. (5)), its expansion into reductions (eq. (10)) and the relation
`(ρ_M ⊗ 1) ψ = (ρ_{M'} ⊗ 1) ψ` for complementary parties (eq. (9)). I did not find this
application of them to AME(7,2) written down.

The statement is Formal Conjectures' own `OpenQuantumProblem35.ame_7_2_not_exists`.
-/

@[expose] public section

namespace AME72

open OpenQuantumProblem35 Finset
open scoped Matrix

/-- The first five of the seven qubits. -/
def firstFive : Finset (Fin 7) := {0, 1, 2, 3, 4}

lemma card_firstFive : firstFive.card = 5 := rfl

/-- The alternating sum over the subsets of five qubits: `1 - 5/2 + 10/4 - 10/8 + 5/8 - 1/4`. -/
lemma alternating_sum_firstFive :
    ∑ U ∈ firstFive.powerset, (-1 : ℂ) ^ U.card * ((2 : ℂ) ^ min U.card (7 - U.card))⁻¹ =
      8⁻¹ := by
  rw [sum_powerset_apply_card (fun k ↦ (-1 : ℂ) ^ k * ((2 : ℂ) ^ min k (7 - k))⁻¹), card_firstFive]
  simp only [sum_range_succ, sum_range_zero, nsmul_eq_mul]
  norm_num [Nat.choose]

/-- **No AME(7,2) state exists.** -/
theorem ame_7_2_not_exists : ¬ ExistsAME 7 2 := by
  rintro ⟨ψ, hψ⟩
  set ρt := inv firstFive (red firstFive (proj ψ)) with hρt
  -- `ρ'² = ρ' / 4`.
  have hsq : ρt * ρt = (4 : ℂ)⁻¹ • ρt := by
    rw [hρt, ← inv_mul, red_mul_red_ame72 hψ card_firstFive, inv_smul]
  -- `ρ' ψ = ψ / 8`.
  have hvec : ρt *ᵥ vec ψ = (8 : ℂ)⁻¹ • vec ψ := by
    rw [hρt, inv_red, Matrix.sum_mulVec]
    simp only [Matrix.smul_mulVec, mulVec_ame72 hψ, smul_smul]
    rw [← sum_smul, alternating_sum_firstFive]
  -- Apply `ρ'` twice.
  have htwice := Matrix.mulVec_mulVec (vec ψ) ρt ρt
  rw [hsq, Matrix.smul_mulVec, hvec, Matrix.mulVec_smul, hvec, smul_smul, smul_smul] at htwice
  have hzero : vec ψ = 0 := by
    have h : ((4 : ℂ)⁻¹ * 8⁻¹ - 8⁻¹ * 8⁻¹) • vec ψ = 0 := by
      rw [sub_smul, htwice, sub_self]
    exact (smul_eq_zero.mp h).resolve_left (by norm_num)
  have hψ0 : ψ = 0 := by
    ext x
    exact congrFun hzero x
  have h1 := hψ.1
  rw [IsNormalized, hψ0, norm_zero] at h1
  exact zero_ne_one h1

end AME72
