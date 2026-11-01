/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

import AME7

/-!
# Control: the general lemmas fire on real AME states

The non-existence proofs use general lemmas whose hypothesis is Formal Conjectures' `IsAME`. If
that hypothesis could never hold, the lemmas would be vacuous. Formal Conjectures itself proves (in
the part copied into `AME7.Defs`) that the GHZ state of three qubits and the Bell state of two
qubits are AME (`ghzState_isAME`, `bellState_isAME`); here they are fed through the lemmas of this
repository.
-/

open OpenQuantumProblem35 AME72
open scoped Matrix

/-- The three-qubit GHZ state is maximally mixed on one qubit. -/
example : IsMaxMixedOn (ghzState 2) {0} :=
  isMaxMixedOn_of_isAME (ghzState_isAME (d := 2) (by norm_num)) {0} (by decide)

/-- On the three-qubit GHZ state, a one-qubit reduction acts as `1/2`. -/
example : red ({1} : Finset (Fin 3)) (proj (ghzState 2)) *ᵥ vec (ghzState 2) =
    ((2 : ℂ) ^ ({1} : Finset (Fin 3)).card)⁻¹ • vec (ghzState 2) :=
  (mulVec_of_isAME (ghzState_isAME (d := 2) (by norm_num)) {1}).1 (by decide)

/-- On the three-qubit GHZ state, a two-qubit reduction also acts as `1/2`, through its
complement. -/
example : red ({0, 2} : Finset (Fin 3)) (proj (ghzState 2)) *ᵥ vec (ghzState 2) =
    ((2 : ℂ) ^ ({0, 2} : Finset (Fin 3))ᶜ.card)⁻¹ • vec (ghzState 2) :=
  (mulVec_of_isAME (ghzState_isAME (d := 2) (by norm_num)) {0, 2}).2 (by decide)

/-- On the three-qubit GHZ state, a two-qubit reduction is a projector up to `1/2`. -/
example : red ({0, 1} : Finset (Fin 3)) (proj (ghzState 2)) * red {0, 1} (proj (ghzState 2)) =
    ((2 : ℂ) ^ ({0, 1} : Finset (Fin 3))ᶜ.card)⁻¹ • red {0, 1} (proj (ghzState 2)) :=
  red_mul_red_of_isAME (ghzState_isAME (d := 2) (by norm_num)) (by decide)

/-- The Bell state is maximally mixed on no qubits, i.e. normalized in the sense used here. -/
example : IsMaxMixedOn (bellState 2) ∅ :=
  isMaxMixedOn_of_isAME (bellState_isAME (d := 2) (by norm_num)) ∅ (by decide)

/-!
## Controls for AME(7, d): the coupled construction fails for `q = 1`, and AME(7, 1) exists

With `q = 1` the coupled state has two levels per party, so it would be an AME(7, 2) state, which
does not exist. This shows that `IsAME` discriminates here, and why `coupled72q_isAME` needs
`q ≥ 3`. With a single level the one state is trivially AME, which is why the headline assumes
`d ≥ 2`.
-/


/-- The coupled state with `q = 1` is not AME. -/
example : ¬ IsAME (AME7.coupled72q (q := 1)) := fun h ↦ by
  have hex : ExistsAME 7 (2 * 1 ^ 1) := ⟨_, h⟩
  norm_num at hex
  exact AME72.ame_7_2_not_exists hex

/-- AME(7, 1) exists under Formal Conjectures' definitions, so `d ≥ 2` cannot be dropped. -/
example : ExistsAME 7 1 := AME7.existsAME_odd (q := 1) odd_one
