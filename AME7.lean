/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import AME7.Instances
public import AME7.Product
public import AME7.Coupled
public import AME7.LinearPhase
public import AME7.Binary
public import AME7.TwiceOdd
public import AME7.FormalTarget

/-!
# AME(7, d) exists exactly when d ≥ 3

A Lean 4 proof of Formal Conjectures' `OpenQuantumProblem35.ame_7_exists_iff`, the
classification of Shi, Zhang, Zhao and Li (arXiv:2608.01011, 2026):
`AME7.ame_7_exists_iff : ExistsAME 7 d ↔ 3 ≤ d` for `d ≥ 2`.

The files:

* `AME7.Defs`: Formal Conjectures' definitions and lemmas for Open Quantum Problem 35, copied;
* `AME7.GraphState`: graph states over `ZMod q` with `k` digits per party, AME when every
  half-cut block is injective, for any number of parties;
* `AME7.Certificate`: cut certificates for seven parties, checked in natural-number arithmetic;
* `AME7.Instances`: AME(7, q) for every odd `q` (`existsAME_odd`), AME(7, 4) and AME(7, 8);
* `AME7.Product`: the product property, AME(n, d₁) and AME(n, d₂) give AME(n, d₁ d₂)
  (`existsAME_mul`);
* `AME7.Coupled`: the reduction of a coupled state `(φ₀ ⊗ χ₀ + φ₁ ⊗ χ₁) / √2`, and normalization
  from a maximally mixed reduction;
* `AME7.LinearPhase`: graph states with a linear phase, their cross reductions, and certificates
  that a cross reduction vanishes;
* `AME7.Binary`: the Steane logical states and their cross reductions, for every permutation;
* `AME7.TwiceOdd`: AME(7, 2q) for every odd `q ≥ 3` (`coupled72q_isAME`);
* `AME7.FormalTarget`: the headline theorem, with necessity from the `AME72` library (no
  AME(7, 2) state), and both theorems under Formal Conjectures' names.
-/
