/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import AME7

/-!
# Control: the coupled construction fails for `q = 1`

With `q = 1` the coupled state has two levels per party, so it would be an AME(7, 2) state, which
does not exist. This shows that `IsAME` discriminates here, and why `coupled72q_isAME` needs
`q ≥ 3`.
-/

open OpenQuantumProblem35

/-- The coupled state with `q = 1` is not AME. -/
example : ¬ IsAME (AME7.coupled72q (q := 1)) := fun h ↦ by
  have hex : ExistsAME 7 (2 * 1 ^ 1) := ⟨_, h⟩
  norm_num at hex
  exact AME72.ame_7_2_not_exists hex
