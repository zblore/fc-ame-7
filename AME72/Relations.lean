/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import AME72.Bridge

/-!
# The relations an AME state satisfies

For an AME state of `n` qubits (Formal Conjectures' `IsAME`):

* `mulVec_of_isAME`: for every set `U` of qubits with `|U| ≤ n / 2` or `|Uᶜ| ≤ n / 2`, the operator
  `ρ_U ⊗ 1` acts on `ψ` as the number `2^(-|U|)`, respectively `2^(-|Uᶜ|)`;
* `red_mul_red_of_isAME`: if `|Aᶜ| ≤ n / 2`, then `ρ_A² = 2^(-|Aᶜ|) ρ_A`.

For seven qubits every set or its complement has at most three qubits, so every `ρ_U ⊗ 1` acts on
`ψ` as `2^(-min(|U|, 7 - |U|))` (`mulVec_ame72`), and every five-qubit reduction satisfies
`ρ_A² = ρ_A / 4` (`red_mul_red_ame72`). These are the eigenvector and projector relations from
which Huber, Gühne and Siewert derive the contradiction.
-/

@[expose] public section

namespace AME72

open OpenQuantumProblem35 Finset
open scoped Matrix

variable {n : ℕ}

/-- **The eigenvector relations.** In an AME state, `ρ_U ⊗ 1` acts on `ψ` as `2^(-|U|)` when `U` is
small, and as `2^(-|Uᶜ|)` when its complement is small. -/
theorem mulVec_of_isAME {ψ : StateVector n 2} (h : IsAME ψ) (U : Finset (Fin n)) :
    (U.card ≤ n / 2 → red U (proj ψ) *ᵥ vec ψ = ((2 : ℂ) ^ U.card)⁻¹ • vec ψ) ∧
      (Uᶜ.card ≤ n / 2 → red U (proj ψ) *ᵥ vec ψ = ((2 : ℂ) ^ Uᶜ.card)⁻¹ • vec ψ) :=
  ⟨fun hU ↦ mulVec_of_maxMixed (isMaxMixedOn_of_isAME h U hU),
    fun hU ↦ (red_mulVec_compl ψ U).trans (mulVec_of_maxMixed (isMaxMixedOn_of_isAME h Uᶜ hU))⟩

/-- **The projector relation.** In an AME state, `ρ_A² = 2^(-|Aᶜ|) ρ_A` when `Aᶜ` is small. -/
theorem red_mul_red_of_isAME {ψ : StateVector n 2} (h : IsAME ψ) {A : Finset (Fin n)}
    (hA : Aᶜ.card ≤ n / 2) :
    red A (proj ψ) * red A (proj ψ) = ((2 : ℂ) ^ Aᶜ.card)⁻¹ • red A (proj ψ) :=
  red_mul_red_of_maxMixed (isMaxMixedOn_of_isAME h Aᶜ hA)

/-- **Seven qubits: every reduction acts on `ψ` as a number.** In an AME(7,2) state,
`(ρ_U ⊗ 1) ψ = 2^(-min(|U|, 7 - |U|)) ψ` for every set `U` of qubits. -/
theorem mulVec_ame72 {ψ : StateVector 7 2} (h : IsAME ψ) (U : Finset (Fin 7)) :
    red U (proj ψ) *ᵥ vec ψ = ((2 : ℂ) ^ min U.card (7 - U.card))⁻¹ • vec ψ := by
  have hc : Uᶜ.card = 7 - U.card := by simp [card_compl]
  have hle : U.card ≤ 7 := by simpa using U.card_le_univ
  by_cases hU : U.card ≤ 3
  · rw [min_eq_left (by omega)]
    exact (mulVec_of_isAME h U).1 (by simpa using hU)
  · rw [min_eq_right (by omega), ← hc]
    exact (mulVec_of_isAME h U).2 (by rw [hc]; norm_num; omega)

/-- **Seven qubits: five-qubit reductions are projectors up to `1/4`.** In an AME(7,2) state,
`ρ_A² = ρ_A / 4` for every set `A` of five qubits. -/
theorem red_mul_red_ame72 {ψ : StateVector 7 2} (h : IsAME ψ) {A : Finset (Fin 7)}
    (hA : A.card = 5) :
    red A (proj ψ) * red A (proj ψ) = (4 : ℂ)⁻¹ • red A (proj ψ) := by
  have hc : Aᶜ.card = 2 := by simp [card_compl, hA]
  rw [red_mul_red_of_isAME h (by rw [hc]; norm_num), hc]
  norm_num

end AME72
