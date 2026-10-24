/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import AME7.Instances
import AME7.Product
import AME7.Coupled
import AME7.LinearPhase

/-!
# AME(7, d) exists exactly when d ≥ 3 (work in progress)

Towards a Lean 4 proof of Formal Conjectures' `OpenQuantumProblem35.ame_7_exists_iff`, the
classification of Shi, Zhang, Zhao and Li (arXiv:2608.01011, 2026).

Done so far:

* `AME7.GraphState`: graph states over `ZMod q` with `k` digits per party, AME when every
  half-cut block is injective, for any number of parties;
* `AME7.Certificate`: cut certificates for seven parties, checked in natural-number arithmetic;
* `AME7.Instances`: AME(7, q) for every odd `q` (`existsAME_odd`), AME(7, 4) and AME(7, 8);
* `AME7.Product`: the product property, AME(n, d₁) and AME(n, d₂) give AME(n, d₁ d₂)
  (`existsAME_mul`);
* `AME7.Coupled`: the reduction of a coupled state `(φ₀ ⊗ χ₀ + φ₁ ⊗ χ₁) / √2`, and normalization
  from a maximally mixed reduction;
* `AME7.LinearPhase`: graph states with a linear phase, their cross reductions, and certificates
  that a cross reduction vanishes.
-/
