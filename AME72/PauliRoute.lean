/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import AME72.Bloch
public import AME72.FormalTarget

/-!
# A second proof: the paper's route, by Pauli strings and the parity rule

This is the argument of Huber, Gühne and Siewert (PRL 118, 200502 (2017), Observation 2), on top of
the same pure-state relations (`AME72.Relations`).

Split `|ψ⟩⟨ψ|` by the support of the Pauli strings, `S_V` for the strings that are not the identity
exactly on `V` (`suppPart`). Then `ρ_U ⊗ 1 = 2^|Uᶜ| ∑_{V ⊆ U} S_V` (`red_eq_sum_suppPart`). For an
AME(7,2) state:

* `S_∅ = 2^(-7)`, and `S_V = 0` for `1 ≤ |V| ≤ 3` (all one-, two- and three-body correlations
  vanish);
* for `|V| = 4`, `S_V ψ = 2^(-7) ψ` (their `P_4^[j] |φ⟩ = |φ⟩`), from `(ρ_V ⊗ 1) ψ = ψ / 8`;
* so for the first five qubits `A`, the even part `E` of `ρ_A ⊗ 1` has `E ψ = (3/16) ψ`, and the
  odd part `O` has `O ψ = ψ / 16` (their `P_5 |φ⟩ = 2 |φ⟩`), since `(ρ_A ⊗ 1) ψ = ψ / 4`.

The projector relation `ρ_A² = ρ_A / 4` and the parity rule for operators (`oddPart_anticomm`) give
`2 (E O + O E) = O / 2` (their eq. (19), `∑_j {P_5, P_4^[j] ⊗ 1} = 6 P_5`). On `ψ` the left side
is `(3/64) ψ` and the right side `(1/32) ψ` (their eq. (21), `20 |φ⟩ = 12 |φ⟩`), so `ψ = 0`.
-/

@[expose] public section

namespace AME72

open OpenQuantumProblem35 Finset
open scoped Matrix

variable {n : ℕ}

/-- The qubits where a Pauli string is not the identity. -/
def supp (α : Fin n → Fin 4) : Finset (Fin n) := univ.filter fun i ↦ α i ≠ 0

lemma weight_eq_card_supp (α : Fin n → Fin 4) : weight α = (supp α).card := by
  rw [weight, supp, card_filter]
  exact sum_congr rfl fun i _ ↦ by simp [wt1]

lemma supp_subset_iff (α : Fin n → Fin 4) (U : Finset (Fin n)) :
    supp α ⊆ U ↔ ∀ i, i ∉ U → α i = 0 := by
  constructor
  · intro h i hi
    by_contra h'
    exact hi (h (by simp [supp, h']))
  · intro h i hi
    by_contra h'
    exact (by simpa [supp] using hi : α i ≠ 0) (h i h')

lemma ne_zero_of_supp_ne_empty {α : Fin n → Fin 4} (h : supp α ≠ ∅) : α ≠ 0 := by
  rintro rfl
  exact h (by simp [supp])

/-- The identity is the Pauli string of the identity. -/
lemma tau_zero : tau (0 : Fin n → Fin 4) = 1 := by
  ext x y
  rw [tau, Matrix.one_apply]
  have h : ∀ i, (tau1 ((0 : Fin n → Fin 4) i) (x i) (y i) : ℂ) =
      ((if x i = y i then 1 else 0 : ℤ) : ℂ) := by
    intro i
    have : ∀ s t : Fin 2, tau1 0 s t = if s = t then 1 else 0 := by decide
    simp [this]
  rw [prod_congr rfl fun i _ ↦ h i, prod_indicator]

/-- `red` commutes with finite sums. -/
lemma red_sum {ι : Type*} (s : Finset ι) (U : Finset (Fin n))
    (f : ι → Matrix (Config n 2) (Config n 2) ℂ) :
    red U (∑ k ∈ s, f k) = ∑ k ∈ s, red U (f k) := by
  ext x x'
  simp only [red, Matrix.sum_apply, mul_sum]
  exact ((sum_congr rfl fun _ _ ↦ sum_comm).trans sum_comm)

/-- **Coefficients of a reduction.** `c_α(ρ_U ⊗ 1) = 2^|Uᶜ| c_α(X)` if `α` lives on `U`, else
`0`. -/
lemma coef_red (α : Fin n → Fin 4) (U : Finset (Fin n)) (X : Matrix (Config n 2) (Config n 2) ℂ) :
    coef α (red U X) = if supp α ⊆ U then (2 : ℂ) ^ Uᶜ.card * coef α X else 0 := by
  conv_lhs => rw [expansion X]
  rw [red_sum, map_sum]
  simp only [red_smul, red_tau, map_smul, smul_eq_mul]
  rw [sum_eq_single α]
  · by_cases h : supp α ⊆ U
    · rw [ite_eq_left ((supp_subset_iff α U).1 h), ite_eq_left h, map_smul, coef_tau,
        ite_eq_left rfl]
      simp only [smul_eq_mul, mul_one]
      ring
    · rw [ite_eq_right (fun h' ↦ h ((supp_subset_iff α U).2 h')), ite_eq_right h, map_zero,
        mul_zero]
  · intro β _ hβ
    split_ifs <;> simp [coef_tau, Ne.symm hβ]
  · simp

/-- The part of `X` on Pauli strings with support exactly `V`. -/
noncomputable def suppPart (X : Matrix (Config n 2) (Config n 2) ℂ) (V : Finset (Fin n)) :
    Matrix (Config n 2) (Config n 2) ℂ :=
  ∑ α, (if supp α = V then coef α X else 0) • tau α

/-- **A reduction, by supports.** `ρ_U ⊗ 1 = 2^|Uᶜ| ∑_{V ⊆ U} S_V`. -/
theorem red_eq_sum_suppPart (U : Finset (Fin n)) (X : Matrix (Config n 2) (Config n 2) ℂ) :
    red U X = (2 : ℂ) ^ Uᶜ.card • ∑ V ∈ U.powerset, suppPart X V := by
  conv_lhs => rw [expansion X]
  rw [red_sum]
  simp only [suppPart, red_smul, red_tau, ← supp_subset_iff]
  rw [sum_comm, smul_sum]
  refine sum_congr rfl fun α _ ↦ ?_
  rw [← sum_smul, sum_ite_eq]
  by_cases h : supp α ⊆ U <;> simp [h, mem_powerset, smul_smul, mul_comm]

/-- A Pauli string's even part: itself if its weight is even, `0` if odd. -/
lemma evenPart_tau (γ : Fin n → Fin 4) :
    evenPart (tau γ) = if Even (weight γ) then tau γ else 0 := by
  rw [evenPart_apply]
  simp only [coef_tau]
  rw [sum_eq_single γ (fun α _ hα ↦ by simp [hα]) (by simp)]
  by_cases h : Even (weight γ) <;> simp [h]

/-- The even part of `S_V` is all of it if `|V|` is even, `0` if odd. -/
lemma evenPart_suppPart (X : Matrix (Config n 2) (Config n 2) ℂ) (V : Finset (Fin n)) :
    evenPart (suppPart X V) = if Even V.card then suppPart X V else 0 := by
  rw [suppPart, map_sum]
  simp only [map_smul, evenPart_tau]
  have h : ∀ α, (if supp α = V then coef α X else 0) • (if Even (weight α) then tau α else 0) =
      if Even V.card then (if supp α = V then coef α X else 0) • tau α else 0 := by
    intro α
    by_cases hα : supp α = V
    · rw [weight_eq_card_supp, hα]
      split_ifs <;> simp
    · simp [hα]
  simp only [h]
  split_ifs <;> simp

/-- An operator is its even part plus its odd part. -/
lemma evenPart_add_oddPart (X : Matrix (Config n 2) (Config n 2) ℂ) :
    evenPart X + oddPart X = X := by
  rw [evenPart_apply, oddPart_apply, ← sum_add_distrib]
  conv_rhs => rw [expansion X]
  exact sum_congr rfl fun α _ ↦ by split_ifs <;> simp

/-- If `ψ` is maximally mixed on `U`, the coefficients of `|ψ⟩⟨ψ|` on non-identity strings living
on `U` vanish. -/
lemma coef_eq_zero_of_maxMixed {ψ : StateVector n 2} {U : Finset (Fin n)} (h : IsMaxMixedOn ψ U)
    {α : Fin n → Fin 4} (hα : α ≠ 0) (hU : supp α ⊆ U) : coef α (proj ψ) = 0 := by
  have := coef_red α U (proj ψ)
  rw [ite_eq_left hU, h, map_smul, ← tau_zero, coef_tau, ite_eq_right hα, smul_zero] at this
  exact (mul_eq_zero.mp this.symm).resolve_left (pow_ne_zero _ two_ne_zero)

/-- If `ψ` is maximally mixed on a non-empty `V`, then `S_V = 0`. -/
lemma suppPart_eq_zero {ψ : StateVector n 2} {V : Finset (Fin n)} (h : IsMaxMixedOn ψ V)
    (hV : V ≠ ∅) : suppPart (proj ψ) V = 0 := by
  refine sum_eq_zero fun α _ ↦ ?_
  split_ifs with hα
  · rw [coef_eq_zero_of_maxMixed h (ne_zero_of_supp_ne_empty (by rw [hα]; exact hV))
      (by rw [hα]), zero_smul]
  · rw [zero_smul]

/-- `S_∅ = 2^(-n)` for a state that is maximally mixed on no qubits, i.e. normalized. -/
lemma suppPart_empty {ψ : StateVector n 2} (h : IsMaxMixedOn ψ ∅) :
    suppPart (proj ψ) ∅ = ((2 : ℂ) ^ n)⁻¹ • 1 := by
  have := red_eq_sum_suppPart ∅ (proj ψ)
  rw [h, powerset_empty, sum_singleton, compl_empty, card_univ, Fintype.card_fin, card_empty,
    pow_zero, inv_one, one_smul] at this
  rw [this, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ two_ne_zero), one_smul]

namespace PauliRoute

/-- **No AME(7,2) state exists**, by the route of Huber, Gühne and Siewert: Pauli strings and the
parity rule. -/
theorem ame_7_2_not_exists : ¬ ExistsAME 7 2 := by
  rintro ⟨ψ, hψ⟩
  have hmm : ∀ U : Finset (Fin 7), U.card ≤ 3 → IsMaxMixedOn ψ U :=
    fun U hU ↦ isMaxMixedOn_of_isAME hψ U (by simpa using hU)
  -- The parts of `|ψ⟩⟨ψ|` by support.
  have hS0 : suppPart (proj ψ) ∅ = ((2 : ℂ) ^ 7)⁻¹ • 1 := suppPart_empty (hmm ∅ (by simp))
  have hSsmall : ∀ W : Finset (Fin 7), W ≠ ∅ → W.card ≤ 3 → suppPart (proj ψ) W = 0 :=
    fun W hW hc ↦ suppPart_eq_zero (hmm W hc) hW
  have hS4 : ∀ W : Finset (Fin 7), W.card = 4 →
      suppPart (proj ψ) W *ᵥ vec ψ = (128 : ℂ)⁻¹ • vec ψ := by
    intro W hW
    have hsum : ∑ V ∈ W.powerset, suppPart (proj ψ) V =
        suppPart (proj ψ) ∅ + suppPart (proj ψ) W := by
      rw [sum_eq_add_of_mem ∅ W (empty_mem_powerset W) (mem_powerset_self W)
        (by rintro rfl; simp at hW)]
      intro V hV hne
      rw [mem_powerset] at hV
      refine hSsmall V hne.1 ?_
      have : V.card < W.card := card_lt_card (ssubset_of_subset_of_ne hV hne.2)
      omega
    have hred := red_eq_sum_suppPart W (proj ψ)
    have hc : Wᶜ.card = 3 := by simp [card_compl, hW]
    rw [hsum, hc] at hred
    have hval := mulVec_ame72 hψ W
    have hmin : min W.card (7 - W.card) = 3 := by rw [hW]; norm_num
    rw [hmin, hred, Matrix.smul_mulVec, Matrix.add_mulVec, hS0, Matrix.smul_mulVec,
      Matrix.one_mulVec] at hval
    have e2 : suppPart (proj ψ) W *ᵥ vec ψ =
        ((2 : ℂ) ^ 3)⁻¹ • (((2 : ℂ) ^ 3)⁻¹ • vec ψ) - ((2 : ℂ) ^ 7)⁻¹ • vec ψ := by
      rw [← hval, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ two_ne_zero), one_smul]
      abel
    rw [e2, smul_smul, ← sub_smul]
    norm_num
  -- The five-qubit reduction and its even and odd parts.
  have hρsum : red firstFive (proj ψ) =
      (4 : ℂ) • ∑ W ∈ firstFive.powerset, suppPart (proj ψ) W := by
    rw [red_eq_sum_suppPart]
    norm_num [card_compl, card_firstFive]
  have hE : evenPart (red firstFive (proj ψ)) *ᵥ vec ψ = (3 / 16 : ℂ) • vec ψ := by
    let g : ℕ → ℂ := fun k ↦ if k = 0 ∨ k = 4 then (128 : ℂ)⁻¹ else 0
    have hW : ∀ W ∈ firstFive.powerset,
        (if Even W.card then suppPart (proj ψ) W else 0) *ᵥ vec ψ = g W.card • vec ψ := by
      intro W hW
      have hle : W.card ≤ 5 := card_firstFive ▸ card_le_card (mem_powerset.mp hW)
      interval_cases h : W.card
      · rw [card_eq_zero.mp h, hS0]
        simp only [g, Matrix.smul_mulVec, Matrix.one_mulVec, ite_eq_left (show Even 0 by decide)]
        norm_num
      · rw [ite_eq_right (show ¬ Even 1 by decide)]
        simp [g]
      · rw [ite_eq_left (show Even 2 by decide), hSsmall W (by rintro rfl; simp at h) (by omega)]
        simp [g]
      · rw [ite_eq_right (show ¬ Even 3 by decide)]
        simp [g]
      · rw [ite_eq_left (show Even 4 by decide), hS4 W h]
        simp [g]
      · rw [ite_eq_right (show ¬ Even 5 by decide)]
        simp [g]
    rw [hρsum, map_smul, map_sum, Matrix.smul_mulVec, Matrix.sum_mulVec]
    simp only [evenPart_suppPart]
    rw [sum_congr rfl hW, ← sum_smul, sum_powerset_apply_card g, card_firstFive, smul_smul]
    simp only [sum_range_succ, sum_range_zero, nsmul_eq_mul, g]
    norm_num [Nat.choose]
  have hρv : red firstFive (proj ψ) *ᵥ vec ψ = (4 : ℂ)⁻¹ • vec ψ := by
    rw [mulVec_ame72 hψ firstFive, card_firstFive]
    norm_num
  have hO : oddPart (red firstFive (proj ψ)) *ᵥ vec ψ = (1 / 16 : ℂ) • vec ψ := by
    have h := congrArg (· *ᵥ vec ψ) (evenPart_add_oddPart (red firstFive (proj ψ)))
    simp only [Matrix.add_mulVec] at h
    rw [hE, hρv] at h
    rw [eq_sub_of_add_eq' h, ← sub_smul]
    norm_num
  -- The projector relation and the parity rule.
  have hsq := red_mul_red_ame72 hψ card_firstFive
  generalize red firstFive (proj ψ) = ρ at hsq hE hO
  have hsum2 : ρ * ρ + ρ * ρ = (2⁻¹ : ℂ) • ρ := by
    rw [hsq]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have key := oddPart_anticomm ρ ρ
  rw [hsum2, map_smul] at key
  have h2 := congrArg (· *ᵥ vec ψ) key
  simp only [Matrix.smul_mulVec, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hE, hO,
    Matrix.mulVec_smul, smul_smul, ← add_smul] at h2
  rw [← sub_eq_zero, ← sub_smul] at h2
  have hzero : vec ψ = 0 := by
    rcases smul_eq_zero.mp h2 with h | h
    · norm_num at h
    · exact h
  have hψ0 : ψ = 0 := by
    ext x
    exact congrFun hzero x
  have h1 := hψ.1
  rw [IsNormalized, hψ0, norm_zero] at h1
  exact zero_ne_one h1

end PauliRoute

end AME72
