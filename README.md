# AME(7, d) in Lean

A Lean 4 proof that, for local dimension d ≥ 2, an absolutely maximally entangled state of seven parties exists exactly when d ≥ 3. It proves two statements from Open Quantum Problem 35 in Google DeepMind's [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures), against their own definitions: `ame_7_2_not_exists`, that no AME(7, 2) state exists, and `ame_7_exists_iff`, the classification. The two cases that were open until this year, AME(7, 6) and AME(7, 10), follow from it.

## The result

A pure state of seven parties, each with d levels, is absolutely maximally entangled, AME(7, d), if any three of the parties on their own look completely random. (The state must be pure: the completely mixed state passes the test trivially.)

- **d = 2.** Felix Huber, Otfried Gühne and Jens Siewert proved that no such state of seven qubits exists: "Absolutely maximally entangled states of seven qubits do not exist", Phys. Rev. Lett. 118, 200502 (2017), arXiv:1608.06228.
- **Every d.** Fei Shi, Xiande Zhang, Qi Zhao and Lvzhou Li proved that such a state exists if and only if d ≥ 3: "Complete Existence Classification of Seven-Partite Absolutely Maximally Entangled States", arXiv:2608.01011 (2026). (With a single level, d = 1, the one state there is trivially AME, so the statement assumes d ≥ 2.) Their paper is an unrefereed preprint, and they say that its new construction, for d = 2q with q odd, was developed with the assistance of GPT-5.6 and that they verified it themselves. This proof is an independent check of every case.

As far as I could find, these are the first formal proofs. I searched GitHub, the Formal Conjectures pull requests and issues, the published AlphaProof Nexus results, the Formal Conjectures benchmark and the quantum information libraries for Lean on 23 and 24 Oct 2026, and searched GitHub again on 31 Oct 2026, and found only the statements with `sorry`. The benchmark lists AME(7, 6) and AME(7, 10) as tasks with no bundled solution ("oracle_status = none").

## No AME(7, 2) state

The proof of `ame_7_2_not_exists` is done twice, by two different routes. Both share the same start. Suppose ψ is an AME(7, 2) state and A is the first five qubits. Write ρ_A for the reduced state of ψ on A.

- **Every reduction acts on ψ as a number.** For any set U of qubits, (ρ_U ⊗ 1)ψ = 2^(-min(|U|, 7-|U|)) ψ. For |U| ≤ 3 this is because ρ_U is maximally mixed. For |U| ≥ 4 it is the identity (ρ_U ⊗ 1)ψ = (ρ_Uᶜ ⊗ 1)ψ for pure states.
- **ρ_A is a projector up to a factor.** ρ_A² = ρ_A / 4, because the two qubits outside A are maximally mixed.

Neither step needs the spectral theorem. Both are rearrangements of finite sums.

**The first proof** uses Wootters' spin flip, which Wyderka, Huber and Gühne call the state inversion (Phys. Rev. A 97, 060101 (2018)). On the qubits of A it is ρ ↦ σ_y^⊗5 ρᵀ σ_y^⊗5. It reverses products, so the inverted ρ̃ also satisfies ρ̃² = ρ̃ / 4. It is also an alternating sum of the smaller reductions, ρ̃ = Σ_{U ⊆ A} (-1)^|U| ρ_U ⊗ 1 (their eq. (10), after Hall), so ρ̃ψ = (1 - 5/2 + 10/4 - 10/8 + 5/8 - 1/4) ψ = ψ / 8. Applying ρ̃ twice then gives ψ / 64 one way and ψ / 32 the other. The paper compares Pauli components with its parity rule at this point. Here the reversal of products does the same job. The tools are all in Wyderka, Huber and Gühne's paper, but I did not find this use of them for AME(7, 2) written down.

**The second proof** is the paper's own. It writes ρ_A in Pauli strings and splits it into its even and odd parts E and O, by the parity of the weight. The parity rule (their Lemma 1) says that if two Pauli strings do not anticommute, the weight of their product has the parity of the sum of their weights. With ρ_A² = ρ_A / 4 this gives 2(EO + OE) = O / 2, their Σ_j {P₅, P₄^[j] ⊗ 1} = 6P₅ (eq. (19)). The vanishing correlations and the eigenvalues above give Eψ = (3/16)ψ and Oψ = (1/16)ψ, their P₄^[j]φ = φ and P₅φ = 2φ (eq. (17)). So the left side is (3/64)ψ and the right side (1/32)ψ, their 20 ≠ 12 (eq. (21)).

## AME(7, d) exists exactly when d ≥ 3

Write d = 2^α m with m odd.

- **Odd d.** The graph state over Z_m of the complement of the 7-cycle (the paper's Eq. (2)). A graph state is AME when, for every set of three parties, the block of its matrix from those parties to the other four is injective. Here every such block has a 3 × 3 minor with determinant 1, −1 or 2, a unit modulo every odd m, so one proof covers every odd m.
- **d = 2q, q odd, q ≥ 3.** The paper's coupled state (|0_L⟩|G⁽⁰⁾⟩ + |1_L⟩|G⁽¹⁾⟩)/√2: Steane logical states on the binary side, and on the odd side the graph state above with an extra linear phase. Its three-party reductions split into four terms. The two diagonal terms give the maximally mixed state. The cross terms vanish on every cut: on the 28 cuts that are not lines of the Fano plane because of the binary code, and on the 7 Fano lines because of an integer vector in the kernel of the cut block (the paper's Table II).
- **α ≥ 2.** AME(7, 4) and AME(7, 8) from circulant graph matrices over GF(4) and GF(8), and the product property: AME(7, d₁) and AME(7, d₂) give AME(7, d₁d₂). The paper uses earlier AME(7, 4) states and Reed–Solomon states here instead. The two circulant witnesses were found for this project by computer search.
- **d = 2.** No AME(7, 2) state exists, by the proof above.

## The files

- `Challenge.lean`: the two statements, for Palomar. It imports only Mathlib, so the definitions they use are copied into it from Formal Conjectures, with Formal Conjectures' names, word for word except for one proof step (below).
- `Solution.lean`: imports the proof.
- `AME7/Defs.lean`: Formal Conjectures' file for Open Quantum Problem 35, up to its benchmark statements, copied with its `category` and `AMS` attributes removed, `Mathlib` imported in place of Formal Conjectures' own library, and the same one proof step changed.

No AME(7, 2) state:

- `AME72/Kernel.lean`: reduced states on any set of qubits, written one qubit at a time, so that every operator identity comes down to a one-qubit fact the kernel checks by `decide`.
- `AME72/PureState.lean`: the two pure-state relations above, for any number of qubits.
- `AME72/Bridge.lean`: from Formal Conjectures' `IsAME`, which speaks about the first n/2 parties after a permutation, to "maximally mixed on every set of at most n/2 qubits".
- `AME72/Relations.lean`: the seven-qubit consequences.
- `AME72/Inversion.lean` and `AME72/FormalTarget.lean`: the first proof, `AME72.ame_7_2_not_exists`.
- `AME72/Pauli.lean`: Pauli strings and the parity rule, `AME72.parity_rule`, for any number of qubits. It uses the real basis 1, X, Z, XZ, with XZ = -iY, so every one-qubit fact is an integer check. The weights are the same as for the usual Pauli strings.
- `AME72/Bloch.lean`: the Bloch expansion, even and odd parts, and the parity rule for operators.
- `AME72/PauliRoute.lean`: the second proof, `AME72.PauliRoute.ame_7_2_not_exists`.

AME(7, d):

- `AME7/GraphState.lean`: graph states over Z_q with k digits per party (local dimension q^k), AME when every half-cut block is injective, for any number of parties.
- `AME7/Certificate.lean` and `AME7/Data.lean`: a certificate for each of the 35 sets of three parties, an integer matrix R with (block) · R = d · 1, checked by the kernel in natural-number and integer arithmetic. `scripts/gen_data.py` generates the data.
- `AME7/Instances.lean`: AME(7, q) for every odd q, AME(7, 4) and AME(7, 8).
- `AME7/Product.lean`: the product property.
- `AME7/Coupled.lean`: the reduction of a coupled state, and normalization from a maximally mixed reduction.
- `AME7/LinearPhase.lean`: graph states with a linear phase, their cross reductions, and kernel-vector certificates that a cross reduction vanishes.
- `AME7/Binary.lean`: the Steane logical states, from three facts about the sixteen code words checked by the kernel for every set of three parties.
- `AME7/TwiceOdd.lean`: AME(7, 2q) for every odd q ≥ 3.
- `AME7/FormalTarget.lean`: `AME7.ame_7_exists_iff`, and both theorems again under Formal Conjectures' names, `OpenQuantumProblem35.ame_7_2_not_exists` and `OpenQuantumProblem35.ame_7_exists_iff`, which are the names `Challenge.lean` uses.

## Checks

CI runs `lake comparator`, which checks that `Solution` proves exactly the statements of `Challenge.lean`, with the same definitions, and replays the proof through Lean's kernel and nanoda. It runs it through `scripts/verify-comparator.sh`, copied unchanged from Palomar's template, which adds con-ron. Palomar's own pipeline, which `.github/workflows/palomar-preflight.yml` runs on a chosen commit, runs con-ron separately and decides acceptance.

**One proof step differs from Formal Conjectures.** Inside the definition `combineFirst`, Formal Conjectures proves `i.1 - m < n - m` by `omega`. Under Lean's module system, `omega` leaves a private helper lemma whose name contains the name of the file it was compiled in. The copy in `Challenge.lean` and the copy in `AME7/Defs.lean` are in different files, so their helpers have different names and Comparator could never match them. Both copies here prove that step by `exact Nat.sub_lt_sub_right him i.2` instead. It proves the same proposition, so `combineFirst` is the same function, and `audit/Audit.lean` checks by `rfl` that it equals Formal Conjectures' original, which it keeps under another name.

`scripts/check-fc-match.py` checks the other link: that `Challenge.lean` is Formal Conjectures' text and nothing else. It must import only `Mathlib`, and its blocks must be exactly the definitions the statements use and the one instance they need, each one of Formal Conjectures' own, in Formal Conjectures' order, with the one proof step above as the only allowed change, and the two statements must be Formal Conjectures' with only the `category` attribute left out. It also checks that `AME7/Defs.lean` differs from Formal Conjectures only by the changes listed above, and that `audit/Audit.lean` keeps Formal Conjectures' original `combineFirst`, and that nothing in Formal Conjectures' file before the statements (a `variable`, `open`, notation, option or instance) could change their meaning. With `--self-test` it checks that 28 altered files (a changed definition or statement, an extra definition, including one of Formal Conjectures' own that the statements do not use, `variable`, `instance`, `attribute` or `set_option`, a hidden nested comment, an extra import, a dropped instance, `omega` put back, context added to Formal Conjectures' file, and others) all fail.

`audit/Audit.lean` checks that the proofs have exactly the statements' types, that `combineFirst` equals Formal Conjectures' original, and derives AME(7, 6) and AME(7, 10). `audit/Control.lean` feeds Formal Conjectures' own AME(2, 2) and AME(3, 2) states through the general lemmas, so their hypotheses are not vacuous; checks that the coupled state with q = 1 is not AME, which is why that construction needs q ≥ 3; and checks that AME(7, 1) does exist, which is why the statement assumes d ≥ 2. `audit/Axioms.lean` and `audit/Audit.lean` check that the proofs use only `propext`, `Classical.choice` and `Quot.sound`, and they fail if that ever changes.

## Building

It needs Lean v4.35.0-rc3 and Mathlib at commit `5e0c4e52`.

```
lake exe cache get
lake build
lake env lean audit/Audit.lean
lake env lean audit/Axioms.lean
lake env lean audit/Control.lean
python3 scripts/check-fc-match.py --self-test
```

The whole library takes a few minutes, most of it the kernel checks of the certificates. `scripts/verify-comparator.sh` runs `lake comparator` as Palomar's template does; it needs Linux, for its sandbox. To regenerate the data, `python scripts/gen_data.py AME7/Data.lean`.

## Earlier versions

The two proofs were first published separately, depending on Formal Conjectures directly, on Lean v4.33.1: AME(7, d) in this repository at commit `cf65a3b`, and AME(7, 2) in [zblore/fc-ame-7-2](https://github.com/zblore/fc-ame-7-2) at commit `2493759`. This version has the same proofs, ported to Palomar's layout and Lean version and combined in one repository. A Palomar Challenge may import only Mathlib, so Formal Conjectures' definitions are copied in here rather than imported. The port changed module headers and imports, replaced deprecated lemma names (`if_pos`, `if_neg`, `if_true`, `if_false`), and changed the one step in Formal Conjectures' `combineFirst` described above.

## How it was made

I used Claude Code to draft the Lean. I've checked every line myself and can explain all of it.

## About

I'm Zayn Blore. My main project is [csd-lean4](https://github.com/zblore/csd-lean4), the Lean library behind my work on Constraint-Surface Dynamics.
