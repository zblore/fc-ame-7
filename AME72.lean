/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import AME72.FormalTarget
public import AME72.PauliRoute

/-!
# No AME(7,2) state, in Lean

A Lean 4 proof of Formal Conjectures' `OpenQuantumProblem35.ame_7_2_not_exists`, the theorem of
Huber, Gühne and Siewert (PRL 118, 200502 (2017)) that no pure seven-qubit state is absolutely
maximally entangled: `AME72.ame_7_2_not_exists : ¬ OpenQuantumProblem35.ExistsAME 7 2`.

The relations an AME state satisfies, for any number of qubits, from Formal Conjectures' own
`IsAME`:

* `AME72.Kernel`: reduced states on any set of qubits, `red U X = tr_{Uᶜ}(X) ⊗ 1`, computed one
  qubit at a time;
* `AME72.PureState`: the eigenvector relation `(ρ_U ⊗ 1) ψ = (ρ_{Uᶜ} ⊗ 1) ψ` and the projector
  relation for pure states;
* `AME72.Bridge`: from `IsAME` to maximally mixed reductions on every set of at most `n / 2` qubits;
* `AME72.Relations`: for seven qubits, `(ρ_U ⊗ 1) ψ = 2^(-min(|U|, 7 - |U|)) ψ` for every `U`, and
  `ρ_A² = ρ_A / 4` for every five-qubit `A`.

The contradiction, by the state inversion (as used by Wyderka, Huber and Gühne, PRA 97, 060101
(2018)) in place of the parity rule:

* `AME72.Inversion`: `inv A X = σ_y^{⊗A} Xᵀ σ_y^{⊗A}` reverses products and turns `ρ_A ⊗ 1` into
  `∑_{U ⊆ A} (-1)^|U| ρ_U ⊗ 1`;
* `AME72.FormalTarget`: the headline theorem.

A second, independent proof of the same statement follows the paper's own route, by Pauli strings
and the parity rule (their Lemma 1):

* `AME72.Pauli`: Pauli strings (in the real basis `1, X, Z, XZ`), their products, and the parity
  rule `parity_rule`;
* `AME72.Bloch`: the Bloch expansion, even and odd parts, and the parity rule for operators;
* `AME72.PauliRoute`: `AME72.PauliRoute.ame_7_2_not_exists`.
-/
