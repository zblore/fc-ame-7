# AME(7, d) in Lean

A Lean 4 proof that an absolutely maximally entangled state of seven parties with local dimension d exists exactly when d ≥ 3. It proves `ame_7_exists_iff` from Open Quantum Problem 35 in Google DeepMind's [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures) against their own definitions. The two cases that were open until this year, AME(7, 6) and AME(7, 10), follow from it.

## The result

A pure state of seven parties, each with d levels, is absolutely maximally entangled, AME(7, d), if any three of the parties on their own look completely random. Fei Shi, Xiande Zhang, Qi Zhao and Lvzhou Li proved that such a state exists if and only if d ≥ 3: "Complete Existence Classification of Seven-Partite Absolutely Maximally Entangled States", arXiv:2608.01011 (2026). Their paper is an unrefereed preprint, and they say that its new construction, for d = 2q with q odd, was developed with the assistance of GPT-5.6 and that they verified it themselves. This proof is an independent check of every case.

As far as I could find, this is the first formal proof. I searched GitHub, the Formal Conjectures pull requests and issues, and the Formal Conjectures benchmark on 24 Oct 2026. The benchmark lists AME(7, 6) and AME(7, 10) as tasks with no solution.

## The proof

Write d = 2^α m with m odd.

- **Odd d.** The graph state over Z_m of the complement of the 7-cycle (the paper's Eq. (2)). A graph state is AME when, for every set of three parties, the block of its matrix from those parties to the other four is injective. Here every such block has a 3 × 3 minor with determinant 1, −1 or 2, a unit modulo every odd m, so one proof covers every odd m.
- **d = 2q, q odd.** The paper's coupled state (|0_L⟩|G⁽⁰⁾⟩ + |1_L⟩|G⁽¹⁾⟩)/√2: Steane logical states on the binary side, and on the odd side the graph state above with an extra linear phase. Its three-party reductions split into four terms. The two diagonal terms give the maximally mixed state. The cross terms vanish on every cut: on the 28 cuts that are not lines of the Fano plane because of the binary code, and on the 7 Fano lines because of an integer vector in the kernel of the cut block (the paper's Table II).
- **α ≥ 2.** AME(7, 4) and AME(7, 8) from circulant graph matrices over GF(4) and GF(8), and the product property: AME(7, d₁) and AME(7, d₂) give AME(7, d₁d₂). The paper uses earlier AME(7, 4) states and Reed–Solomon states here instead. The two circulant witnesses were found for this project by computer search.
- **d = 2.** No AME(7, 2) state exists (Huber, Gühne and Siewert 2017). That proof is in [zblore/fc-ame-7-2](https://github.com/zblore/fc-ame-7-2), which this repository depends on.

The files:

- `AME7/GraphState.lean`: graph states over Z_q with k digits per party (local dimension q^k), AME when every half-cut block is injective, for any number of parties.
- `AME7/Certificate.lean` and `AME7/Data.lean`: a certificate for each of the 35 sets of three parties, an integer matrix R with (block) · R = d · 1, checked by the kernel in natural-number and integer arithmetic. `scripts/gen_data.py` generates the data.
- `AME7/Instances.lean`: AME(7, q) for every odd q, AME(7, 4) and AME(7, 8).
- `AME7/Product.lean`: the product property.
- `AME7/Coupled.lean`: the reduction of a coupled state, and normalization from a maximally mixed reduction.
- `AME7/LinearPhase.lean`: graph states with a linear phase, their cross reductions, and kernel-vector certificates that a cross reduction vanishes.
- `AME7/Binary.lean`: the Steane logical states, from three facts about the sixteen code words checked by the kernel for every set of three parties.
- `AME7/TwiceOdd.lean`: AME(7, 2q) for every odd q ≥ 3.
- `AME7/FormalTarget.lean`: `AME7.ame_7_exists_iff`.

The statement is Formal Conjectures' `OpenQuantumProblem35.ame_7_exists_iff`. `audit/Audit.lean` checks that the proof has exactly its type and derives AME(7, 6) and AME(7, 10). `audit/Control.lean` checks that the coupled state with q = 1 is not AME, which is why that construction needs q ≥ 3. The proof uses only `propext`, `Classical.choice` and `Quot.sound`, and the audit fails if that ever changes.

## Building

It needs Lean v4.33.1 and depends on Formal Conjectures at commit `9833012f` and on zblore/fc-ame-7-2 at commit `2493759`.

```
lake exe cache get
lake build
```

A fresh build first compiles Formal Conjectures' support library. The whole library takes a few minutes, most of it the kernel checks of the certificates. To rerun the audit and regenerate the data:

```
lake env lean audit/Audit.lean
lake env lean audit/Axioms.lean
lake env lean audit/Control.lean
python scripts/gen_data.py AME7/Data.lean
```

## How it was made

I used Claude Code to draft the Lean. I've checked every line myself and can explain all of it.

## About

I'm Zayn Blore. My main project is [csd-lean4](https://github.com/zblore/csd-lean4), the Lean library behind my work on Constraint-Surface Dynamics.
