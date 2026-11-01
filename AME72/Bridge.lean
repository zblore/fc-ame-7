/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import AME72.PureState

/-!
# From Formal Conjectures' `IsAME` to maximally mixed reductions on any small set

Formal Conjectures states AME through reductions to the *first* `n / 2` parties, after permuting
the parties. This file turns that into the subset form used in this project:
`isMaxMixedOn_of_isAME` says an AME state of `n` qubits is maximally mixed on every set of at
most `n / 2` qubits.

* `exists_perm_mem_iff`: every set `U` of `m` qubits is sent to the first `m` positions by some
  permutation.
* `splitEquiv`: for such a permutation, a configuration of all `n` qubits is a configuration of the
  first block and one of the rest, read through `permuteConfig π ∘ combineFirst`.
* `red_eq_reducedDensityFirst`: `ρ_U ⊗ 1` is Formal Conjectures' `reducedDensityFirst` of the
  permuted state, tensored with the identity on the rest.
-/

@[expose] public section

namespace AME72

open OpenQuantumProblem35 Finset

variable {n m : ℕ}

/-- **A permutation for any set.** Every set `U` of `m` qubits is the set of qubits that some
permutation `π` sends to the first `m` positions. -/
lemma exists_perm_mem_iff (U : Finset (Fin n)) (hU : U.card = m) :
    ∃ π : Equiv.Perm (Fin n), ∀ i, i ∈ U ↔ (π i).1 < m := by
  have hm : m ≤ n := by simpa [hU] using U.card_le_univ
  have e₁ : {i // i ∈ U} ≃ Fin m := Fintype.equivFinOfCardEq (by simp [hU])
  have e₂ : {i // i ∉ U} ≃ Fin (n - m) := Fintype.equivFinOfCardEq (by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe, hU])
  let π : Equiv.Perm (Fin n) :=
    ((Equiv.sumCompl (· ∈ U)).symm.trans (e₁.sumCongr e₂)).trans
      (finSumFinEquiv.trans (finCongr (Nat.add_sub_cancel' hm)))
  refine ⟨π, fun i ↦ ?_⟩
  by_cases hi : i ∈ U
  · simp [π, hi, Equiv.sumCompl_symm_apply_of_pos]
  · simp [π, hi, Equiv.sumCompl_symm_apply_of_neg]

/-- Reading the first block of a configuration through `π`. -/
def firstPart (π : Equiv.Perm (Fin n)) (hm : m ≤ n) (x : Config n 2) : Config m 2 :=
  fun k ↦ x (π.symm (leftIndex hm k))

/-- Reading the rest of a configuration through `π`. -/
def restPart (π : Equiv.Perm (Fin n)) (hm : m ≤ n) (x : Config n 2) : Config (n - m) 2 :=
  fun k ↦ x (π.symm (rightIndex hm k))

/-- A configuration of all qubits is a first block and a rest, through `π`. -/
def splitEquiv (π : Equiv.Perm (Fin n)) (hm : m ≤ n) :
    Config m 2 × Config (n - m) 2 ≃ Config n 2 where
  toFun w := permuteConfig π (combineFirst m hm w.1 w.2)
  invFun x := (firstPart π hm x, restPart π hm x)
  left_inv w := by
    ext k <;> simp [firstPart, restPart, permuteConfig]
  right_inv x := by
    funext i
    by_cases h : (π i).1 < m
    · have : leftIndex hm ⟨(π i).1, h⟩ = π i := Fin.ext rfl
      simp [permuteConfig, combineFirst, firstPart, h, this]
    · have : rightIndex hm ⟨(π i).1 - m, by omega⟩ = π i := Fin.ext (by simp [rightIndex]; omega)
      simp [permuteConfig, combineFirst, restPart, h, this]

/-- The kernel product is the indicator of its qubit-by-qubit conditions. -/
lemma kernProd_eq (U : Finset (Fin n)) (x x' p q : Config n 2) :
    kernProd U x x' p q = if (∀ i, if i ∈ U then p i = x i ∧ q i = x' i
      else x i = x' i ∧ p i = q i) then 1 else 0 := by
  rw [kernProd]
  split_ifs with h
  · refine prod_eq_one fun i _ ↦ ?_
    have hi := h i
    by_cases hU : i ∈ U <;> simp_all [kern]
  · obtain ⟨i, hi⟩ := not_forall.mp h
    refine prod_eq_zero (mem_univ i) ?_
    by_cases hU : i ∈ U <;> simp_all [kern]

/-- Through `π`, the kernel conditions say: same first block as `x` and `x'`, same rest as each
other, and `x`, `x'` agree on the rest. -/
lemma kern_conditions_iff {U : Finset (Fin n)} {π : Equiv.Perm (Fin n)} (hm : m ≤ n)
    (hπ : ∀ i, i ∈ U ↔ (π i).1 < m) (b b' : Config m 2) (z z' : Config (n - m) 2)
    (x x' : Config n 2) :
    (∀ i, if i ∈ U then splitEquiv π hm (b, z) i = x i ∧ splitEquiv π hm (b', z') i = x' i
      else x i = x' i ∧ splitEquiv π hm (b, z) i = splitEquiv π hm (b', z') i) ↔
      b = firstPart π hm x ∧ b' = firstPart π hm x' ∧
        restPart π hm x = restPart π hm x' ∧ z = z' := by
  constructor
  · intro h
    refine ⟨funext fun k ↦ ?_, funext fun k ↦ ?_, funext fun k ↦ ?_, funext fun k ↦ ?_⟩
    · have hk := h (π.symm (leftIndex hm k))
      rw [ite_eq_left ((hπ _).2 (by simp [leftIndex]))] at hk
      simpa [splitEquiv, permuteConfig, firstPart] using hk.1
    · have hk := h (π.symm (leftIndex hm k))
      rw [ite_eq_left ((hπ _).2 (by simp [leftIndex]))] at hk
      simpa [splitEquiv, permuteConfig, firstPart] using hk.2
    · have hk := h (π.symm (rightIndex hm k))
      rw [ite_eq_right (by rw [hπ]; simp [rightIndex])] at hk
      simpa [restPart] using hk.1
    · have hk := h (π.symm (rightIndex hm k))
      rw [ite_eq_right (by rw [hπ]; simp [rightIndex])] at hk
      simpa [splitEquiv, permuteConfig] using hk.2
  · rintro ⟨rfl, rfl, hx, rfl⟩ i
    have hxi := (splitEquiv π hm).apply_symm_apply x
    have hxi' := (splitEquiv π hm).apply_symm_apply x'
    by_cases hi : i ∈ U
    · rw [ite_eq_left hi]
      have h := (hπ i).1 hi
      have : leftIndex hm ⟨(π i).1, h⟩ = π i := Fin.ext rfl
      simp [splitEquiv, permuteConfig, combineFirst, firstPart, h, this]
    · rw [ite_eq_right hi]
      have h : ¬ (π i).1 < m := fun h ↦ hi ((hπ i).2 h)
      refine ⟨?_, by simp [splitEquiv, permuteConfig, combineFirst, h]⟩
      have : rightIndex hm ⟨(π i).1 - m, by omega⟩ = π i := Fin.ext (by simp [rightIndex]; omega)
      have hk := congrFun hx ⟨(π i).1 - m, by omega⟩
      simpa [restPart, this] using hk

/-- **`ρ_U ⊗ 1` through Formal Conjectures' reduction.** If `π` sends `U` to the first `m`
positions, the entry of `ρ_U ⊗ 1` at `(x, x')` is `δ` of the rests times Formal Conjectures'
`reducedDensityFirst m` of the permuted state at the first blocks. -/
theorem red_eq_reducedDensityFirst {U : Finset (Fin n)} {π : Equiv.Perm (Fin n)} (hm : m ≤ n)
    (hπ : ∀ i, i ∈ U ↔ (π i).1 < m) (ψ : StateVector n 2) (x x' : Config n 2) :
    red U (proj ψ) x x' = (if restPart π hm x = restPart π hm x' then 1 else 0) *
      reducedDensityFirst m hm (permuteState π ψ) (firstPart π hm x) (firstPart π hm x') := by
  have hR : reducedDensityFirst m hm (permuteState π ψ) (firstPart π hm x) (firstPart π hm x') =
      ∑ z, ψ (splitEquiv π hm (firstPart π hm x, z)) *
        star (ψ (splitEquiv π hm (firstPart π hm x', z))) := rfl
  rw [hR]
  change (∑ p, ∑ q, kernProd U x x' p q * (ψ p * star (ψ q))) = _
  simp only [kernProd_eq]
  rw [← (splitEquiv π hm).sum_comp]
  simp_rw [← (splitEquiv π hm).sum_comp (fun q ↦ (if _ then (1 : ℂ) else 0) * (ψ _ * star (ψ q)))]
  simp only [Fintype.sum_prod_type]
  simp_rw [kern_conditions_iff hm hπ]
  by_cases hx : restPart π hm x = restPart π hm x'
  · simp [hx, ite_and]
  · simp [hx]

/-- **AME states are maximally mixed on every set of `n / 2` qubits.** -/
theorem isMaxMixedOn_of_isAME_card_eq {ψ : StateVector n 2} (h : IsAME ψ) (U : Finset (Fin n))
    (hU : U.card = n / 2) : IsMaxMixedOn ψ U := by
  obtain ⟨π, hπ⟩ := exists_perm_mem_iff U hU
  have hm : n / 2 ≤ n := Nat.div_le_self n 2
  ext x x'
  rw [red_eq_reducedDensityFirst hm hπ, h.2 π]
  simp only [maximallyMixed, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, Fintype.card_fun,
    Fintype.card_fin, hU]
  have : x = x' ↔ restPart π hm x = restPart π hm x' ∧ firstPart π hm x = firstPart π hm x' := by
    constructor
    · rintro rfl; simp
    · rintro ⟨h₁, h₂⟩
      have := congrArg (splitEquiv π hm) (Prod.ext h₂ h₁ :
        (firstPart π hm x, restPart π hm x) = (firstPart π hm x', restPart π hm x'))
      simpa [splitEquiv] using
        ((splitEquiv π hm).apply_symm_apply x).symm.trans
          (this.trans ((splitEquiv π hm).apply_symm_apply x'))
  by_cases h₁ : restPart π hm x = restPart π hm x' <;>
    by_cases h₂ : firstPart π hm x = firstPart π hm x' <;> simp [h₁, h₂, this]

/-- **AME states are maximally mixed on every set of at most `n / 2` qubits.** -/
theorem isMaxMixedOn_of_isAME {ψ : StateVector n 2} (h : IsAME ψ) (U : Finset (Fin n))
    (hU : U.card ≤ n / 2) : IsMaxMixedOn ψ U := by
  obtain ⟨V, hUV, hV⟩ := exists_superset_card_eq hU (by simpa using Nat.div_le_self n 2)
  exact (isMaxMixedOn_of_isAME_card_eq h V hV).mono hUV

end AME72
