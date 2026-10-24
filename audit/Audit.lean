/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import AME7

/-!
# Audit

The headline theorem has exactly the type of Formal Conjectures' statement, and depends only on
the standard axioms. The two open benchmark cases that Formal Conjectures derives from it follow
here too.
-/

/-- The type of Formal Conjectures' (still `sorry`) statement is the type of this proof. -/
example : type_of% OpenQuantumProblem35.ame_7_exists_iff := AME7.ame_7_exists_iff

/-- AME(7, 6), from the classification. -/
example : OpenQuantumProblem35.ExistsAME 7 6 :=
  (AME7.ame_7_exists_iff 6 (by norm_num)).2 (by norm_num)

/-- AME(7, 10), from the classification. -/
example : OpenQuantumProblem35.ExistsAME 7 10 :=
  (AME7.ame_7_exists_iff 10 (by norm_num)).2 (by norm_num)

/-- info: 'AME7.ame_7_exists_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AME7.ame_7_exists_iff
