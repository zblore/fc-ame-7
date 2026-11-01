/-
Copyright 2026 The Formal Conjectures Authors.
Modifications copyright 2026 Zayn Blore.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Mathlib

/-!
# Seven-party absolutely maximally entangled states

A pure state of `n` parties, each with `d` levels, is absolutely maximally entangled, AME(n, d),
if every reduction to at most half of the parties is maximally mixed. These are Formal
Conjectures' statements for seven parties (Open Quantum Problem 35):

* `ame_7_2_not_exists`: there is no AME(7, 2) state (Huber, Gühne and Siewert 2017);
* `ame_7_exists_iff`: for `d ≥ 2`, an AME(7, d) state exists exactly when `d ≥ 3` (Shi, Zhang,
  Zhao and Li 2026).

The definitions below and the text of the two statements are copied from Formal Conjectures
(`google-deepmind/formal-conjectures`, commit `b6939a3a0d89e5f999fa8c6483a6ef646c1e2923`),
`FormalConjectures/OpenQuantumProblems/35.lean`, with Formal Conjectures' names. Only the
definitions the statements use are copied, and Formal Conjectures' `category` and `AMS`
attributes are left out; they come from its own library, which a Challenge may not import.

One proof step differs. Inside `combineFirst`, Formal Conjectures proves `i.1 - m < n - m` by
`omega`; here it is `exact Nat.sub_lt_sub_right him i.2`. Under Lean's module system `omega`
leaves a private auxiliary lemma whose name contains the module's name, so the copy in
`Challenge` and the copy in the proof's own module could never compare equal in Comparator. The
two proofs are of the same proposition, so `combineFirst` is the same function;
`audit/Audit.lean` checks this against Formal Conjectures' original text by `rfl`.
-/

@[expose] public section

open scoped BigOperators

namespace OpenQuantumProblem35

/- ## Basic structures -/

/-- A computational-basis configuration of $n$ parties with local dimension $d$. -/
abbrev Config (n d : ℕ) := Fin n → Fin d

/-- A state vector in the computational basis, viewed as a finite-dimensional Hilbert space. -/
abbrev StateVector (n d : ℕ) := EuclideanSpace ℂ (Config n d)

/-- Build a state vector from its computational-basis amplitudes. -/
abbrev mkStateVector {n d : ℕ} (ψ : Config n d → ℂ) : StateVector n d :=
  WithLp.toLp 2 ψ

/-- A state vector can be evaluated on a computational-basis configuration to read its amplitude. -/
instance {n d : ℕ} : CoeFun (StateVector n d) (fun _ => Config n d → ℂ) where
  coe ψ := ψ.ofLp

/-- A state vector is normalized if it has $L^2$ norm $1$. -/
def IsNormalized {n d : ℕ} (ψ : StateVector n d) : Prop :=
  ‖ψ‖ = 1

/-- Permute the parties of a configuration. -/
def permuteConfig {n d : ℕ} (π : Equiv.Perm (Fin n)) (x : Config n d) : Config n d :=
  fun i => x (π i)

/-- Permute the parties of a state vector. -/
def permuteState {n d : ℕ} (π : Equiv.Perm (Fin n)) (ψ : StateVector n d) : StateVector n d :=
  mkStateVector fun x => ψ (permuteConfig π x)

/--
Merge a configuration on the first $m$ parties and a configuration on the remaining $n-m$
parties into a configuration on all $n$ parties.
-/
def combineFirst {n d : ℕ} (m : ℕ) (hm : m ≤ n)
    (x : Config m d) (y : Config (n - m) d) : Config n d :=
  fun i =>
    if hi : i.1 < m then
      x ⟨i.1, hi⟩
    else
      y ⟨i.1 - m, by
        have him : m ≤ i.1 := Nat.le_of_not_gt hi
        exact Nat.sub_lt_sub_right him i.2⟩

/- ## Reduced density matrices and AME -/

/--
The reduced density matrix obtained by tracing out the last $n-m$ parties.

The subsystem is always the first $m$ parties; different subsystems are handled by first
permuting the parties.
-/
noncomputable def reducedDensityFirst {n d : ℕ} (m : ℕ) (hm : m ≤ n) (ψ : StateVector n d) :
    Matrix (Config m d) (Config m d) ℂ :=
  fun x y =>
    ∑ z : Config (n - m) d,
      ψ (combineFirst (n := n) (d := d) m hm x z) *
        star (ψ (combineFirst (n := n) (d := d) m hm y z))

/-- The maximally mixed state on $m$ parties. -/
noncomputable def maximallyMixed (m d : ℕ) :
    Matrix (Config m d) (Config m d) ℂ :=
  ((Fintype.card (Config m d) : ℂ)⁻¹) •
    (1 : Matrix (Config m d) (Config m d) ℂ)

/-- A state has maximally mixed reduction on the first $m$ parties. -/
def HasMaximallyMixedFirstReduction {n d : ℕ} (m : ℕ) (hm : m ≤ n)
    (ψ : StateVector n d) : Prop :=
  reducedDensityFirst (n := n) (d := d) m hm ψ = maximallyMixed m d

/--
A state $\psi$ is absolutely maximally entangled.

Standard AME definitions quantify over all subsets $A \subseteq \mathrm{Fin}\, n$ with
$|A| \le \lfloor n/2 \rfloor$ and require that the reduction on $A$ be maximally mixed.
For pure states it is enough to check subsets of size exactly $\lfloor n/2 \rfloor$; see the
references of Helwig--Cui--Riera--Latorre--Lo (2012) and
Goyeneche--Alsina--Latorre--Riera--Życzkowski (2015). In this file, a subsystem of that size is
encoded by first permuting the chosen parties to the front and then tracing out the remaining
parties.

We also require $\psi$ to be normalized explicitly.
-/
def IsAME {n d : ℕ} (ψ : StateVector n d) : Prop :=
  IsNormalized ψ ∧
    ∀ π : Equiv.Perm (Fin n),
      HasMaximallyMixedFirstReduction (n := n) (d := d)
        (n / 2) (Nat.div_le_self n 2) (permuteState π ψ)

/-- Existence of an $\mathrm{AME}(n,d)$ state. -/
def ExistsAME (n d : ℕ) : Prop :=
  ∃ ψ : StateVector n d, IsAME (n := n) (d := d) ψ

/- ## The statements -/

/-- Source-backed benchmark statement: no $\mathrm{AME}(7,2)$ state exists; see Huber--Gühne--Siewert (2017) and the OQP page. -/
theorem ame_7_2_not_exists : ¬ ExistsAME 7 2 := by
  sorry

/-- For a physical local dimension $d \ge 2$, a seven-party AME state exists exactly when
$d \ge 3$. The hypothesis excludes the degenerate dimension $d = 1$, for which the unique
computational-basis state is AME under the definitions of this file.
Shi--Zhang--Zhao--Li (2026) construct cyclic quadratic-phase states in every odd dimension and
a coupled binary--odd-dimensional state in every dimension congruent to `2` modulo `4`; together
with power-of-two constructions and the product property, this covers every `d ≥ 3`. -/
theorem ame_7_exists_iff (d : ℕ) (hd : 2 ≤ d) : ExistsAME 7 d ↔ 3 ≤ d := by
  sorry

end OpenQuantumProblem35
