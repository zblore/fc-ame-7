/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import AME7.TwiceOdd
public import AME72

/-!
# The headline: AME(7, d) exists exactly when d ≥ 3

The classification of Shi, Zhang, Zhao and Li (arXiv:2608.01011, 2026, Theorem 1). Write
`d = 2^α m` with `m` odd.

* `α = 0`: the graph state of `Γ` over `ZMod m` (`existsAME_odd`);
* `α = 1`: the coupled state, `m ≥ 3` (`coupled72q_isAME`);
* `α ≥ 2`: AME(7, 4) and AME(7, 8), multiplied up to `2^α` and then by `m`
  (`existsAME_four`, `existsAME_eight`, `existsAME_mul`).

For `α ≥ 2` the paper uses known AME(7, 4) states and Reed–Solomon AME(7, 2^α) states; this proof
uses the two circulant witnesses of `AME7.Instances` and the product property instead.

Necessity is the non-existence of AME(7, 2) (Huber, Gühne and Siewert 2017),
`AME72.ame_7_2_not_exists`, in this repository's `AME72` library.

The statement is Formal Conjectures' own `OpenQuantumProblem35.ame_7_exists_iff`. At the end of
the file both theorems are stated again under Formal Conjectures' names, which are the names
`Challenge.lean` and Palomar's Comparator check.
-/

@[expose] public section

namespace AME7

open OpenQuantumProblem35

/-- **AME(7, 2^α) for every `α ≥ 2`.** -/
theorem existsAME_two_pow (j : ℕ) : ExistsAME 7 (2 ^ (j + 2)) := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    match j, ih with
    | 0, _ => exact existsAME_four
    | 1, _ => exact existsAME_eight
    | j + 2, ih =>
      have h : 2 ^ (j + 2 + 2) = 4 * 2 ^ (j + 2) := by ring
      rw [h]
      exact existsAME_mul existsAME_four (ih j (by omega))

/-- **AME(7, d) exists exactly when `d ≥ 3`**, for `d ≥ 2`. -/
theorem ame_7_exists_iff (d : ℕ) (hd : 2 ≤ d) : ExistsAME 7 d ↔ 3 ≤ d := by
  constructor
  · intro h
    by_contra h3
    have : d = 2 := by omega
    subst this
    exact AME72.ame_7_2_not_exists h
  · intro h3
    obtain ⟨α, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd (n := d) (by omega)
    have : NeZero m := ⟨fun h ↦ by simp [h] at hm⟩
    match α with
    | 0 => simpa using existsAME_odd hm
    | 1 =>
      have hm3 : 3 ≤ m := by
        rcases hm with ⟨r, rfl⟩
        omega
      have h := (⟨_, coupled72q_isAME hm hm3⟩ : ExistsAME 7 (2 * m ^ 1))
      rw [pow_one] at h ⊢
      exact h
    | j + 2 => exact existsAME_mul (existsAME_two_pow j) (existsAME_odd hm)

end AME7

/-! ### Formal Conjectures' names -/

namespace OpenQuantumProblem35

/-- Formal Conjectures' `ame_7_2_not_exists`: there is no AME(7, 2) state. -/
theorem ame_7_2_not_exists : ¬ ExistsAME 7 2 :=
  AME72.ame_7_2_not_exists

/-- Formal Conjectures' `ame_7_exists_iff`: for `d ≥ 2`, AME(7, d) exists exactly when
`d ≥ 3`. -/
theorem ame_7_exists_iff (d : ℕ) (hd : 2 ≤ d) : ExistsAME 7 d ↔ 3 ≤ d :=
  AME7.ame_7_exists_iff d hd

end OpenQuantumProblem35
