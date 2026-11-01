/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

import AME7

/-!
# Audit

The two statements `Solution` proves under Formal Conjectures' names have exactly the types of
the repository's own headline theorems, and depend only on the standard axioms. The two open
benchmark cases that Formal Conjectures derives from the classification follow here too.
-/

/-- Formal Conjectures' name and the AME(7, 2) headline have the same type. -/
example : type_of% OpenQuantumProblem35.ame_7_2_not_exists := AME72.ame_7_2_not_exists
example : ¬ OpenQuantumProblem35.ExistsAME 7 2 := AME72.ame_7_2_not_exists

/-- The same for the second proof, by Pauli strings and the parity rule. -/
example : type_of% OpenQuantumProblem35.ame_7_2_not_exists := AME72.PauliRoute.ame_7_2_not_exists

/-- Formal Conjectures' name and the AME(7) headline have the same type. -/
example : type_of% OpenQuantumProblem35.ame_7_exists_iff := AME7.ame_7_exists_iff

/-- AME(7, 6), from the classification. -/
example : OpenQuantumProblem35.ExistsAME 7 6 :=
  (AME7.ame_7_exists_iff 6 (by norm_num)).2 (by norm_num)

/-- AME(7, 10), from the classification. -/
example : OpenQuantumProblem35.ExistsAME 7 10 :=
  (AME7.ame_7_exists_iff 10 (by norm_num)).2 (by norm_num)

/-! `combineFirst` differs from Formal Conjectures' text in one proof step (see `Challenge.lean`).
Here is Formal Conjectures' original, with `omega`, under another name; it is the same function. -/

namespace OpenQuantumProblem35

/--
Merge a configuration on the first $m$ parties and a configuration on the remaining $n-m$
parties into a configuration on all $n$ parties.
-/
def combineFirstFC {n d : ℕ} (m : ℕ) (hm : m ≤ n)
    (x : Config m d) (y : Config (n - m) d) : Config n d :=
  fun i =>
    if hi : i.1 < m then
      x ⟨i.1, hi⟩
    else
      y ⟨i.1 - m, by
        have him : m ≤ i.1 := Nat.le_of_not_gt hi
        omega⟩

example : @combineFirstFC = @combineFirst := rfl

end OpenQuantumProblem35

/--
info: 'OpenQuantumProblem35.ame_7_2_not_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OpenQuantumProblem35.ame_7_2_not_exists

/--
info: 'OpenQuantumProblem35.ame_7_exists_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OpenQuantumProblem35.ame_7_exists_iff

/-- info: 'AME72.ame_7_2_not_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AME72.ame_7_2_not_exists

/-- info: 'AME72.PauliRoute.ame_7_2_not_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AME72.PauliRoute.ame_7_2_not_exists

/-- info: 'AME72.parity_rule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AME72.parity_rule

/-- info: 'AME7.ame_7_exists_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AME7.ame_7_exists_iff
