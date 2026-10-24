/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import FormalConjectures.OpenQuantumProblems.«35»

/-!
# The product of two AME states is AME

Read each level `x < d₁ d₂` of a party as a pair of levels `(x₁, x₂)` with `x₁ < d₁`, `x₂ < d₂`
(`finProdFinEquiv`). For states `φ` with local dimension `d₁` and `χ` with `d₂` on the same parties,
`prodState φ χ` has amplitude `φ(x₁) χ(x₂)`: it is `φ ⊗ χ`, with each party's two factors merged.
Its reduction to the first `m` parties is the product of the two reductions
(`reduced_prodState`), so it is AME when both factors are (`prodState_isAME`). This is the product
property of AME states (Rains 1999; Shi, Li, Chen and Zhang, PRA 104, 032601 (2021)).
-/

namespace AME7

open OpenQuantumProblem35

variable {n d₁ d₂ : ℕ}

/-- The first level of each party. -/
def splitL (x : Config n (d₁ * d₂)) : Config n d₁ := fun i ↦ (finProdFinEquiv.symm (x i)).1

/-- The second level of each party. -/
def splitR (x : Config n (d₁ * d₂)) : Config n d₂ := fun i ↦ (finProdFinEquiv.symm (x i)).2

/-- A configuration with `d₁ d₂` levels is a pair of configurations. -/
def splitEquiv (n : ℕ) : Config n (d₁ * d₂) ≃ Config n d₁ × Config n d₂ where
  toFun x := (splitL x, splitR x)
  invFun w := fun i ↦ finProdFinEquiv (w.1 i, w.2 i)
  left_inv x := by
    funext i
    exact finProdFinEquiv.apply_symm_apply (x i)
  right_inv w := by
    ext i <;> simp [splitL, splitR]

lemma splitEquiv_apply (x : Config n (d₁ * d₂)) : splitEquiv n x = (splitL x, splitR x) := rfl

/-- The product state: amplitude `φ(x₁) χ(x₂)`. -/
noncomputable def prodState (φ : StateVector n d₁) (χ : StateVector n d₂) :
    StateVector n (d₁ * d₂) :=
  mkStateVector fun x ↦ φ (splitL x) * χ (splitR x)

/-- The product of normalized states is normalized. -/
theorem prodState_isNormalized {φ : StateVector n d₁} {χ : StateVector n d₂}
    (hφ : IsNormalized φ) (hχ : IsNormalized χ) : IsNormalized (prodState φ χ) := by
  rw [isNormalized_iff_norm_sq_eq_one, EuclideanSpace.norm_sq_eq] at hφ hχ ⊢
  calc ∑ x, ‖(prodState φ χ).ofLp x‖ ^ 2
      = ∑ w : Config n d₁ × Config n d₂, ‖φ w.1‖ ^ 2 * ‖χ w.2‖ ^ 2 := by
        refine Fintype.sum_equiv (splitEquiv n) _ _ fun x ↦ ?_
        simp [prodState, splitEquiv_apply, mul_pow]
    _ = (∑ u, ‖φ.ofLp u‖ ^ 2) * ∑ v, ‖χ.ofLp v‖ ^ 2 := by
        rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
    _ = 1 := by rw [hφ, hχ, one_mul]

/-- Permuting the parties of a product state permutes both factors. -/
lemma permuteState_prodState (π : Equiv.Perm (Fin n)) (φ : StateVector n d₁)
    (χ : StateVector n d₂) :
    permuteState π (prodState φ χ) = prodState (permuteState π φ) (permuteState π χ) := by
  ext x
  simp only [permuteState_apply, prodState, mkStateVector_apply]
  rfl

lemma splitL_combineFirst {m : ℕ} (hm : m ≤ n) (a : Config m (d₁ * d₂))
    (z : Config (n - m) (d₁ * d₂)) :
    splitL (combineFirst m hm a z) = combineFirst m hm (splitL a) (splitL z) := by
  funext i
  simp only [splitL, combineFirst]
  split_ifs <;> rfl

lemma splitR_combineFirst {m : ℕ} (hm : m ≤ n) (a : Config m (d₁ * d₂))
    (z : Config (n - m) (d₁ * d₂)) :
    splitR (combineFirst m hm a z) = combineFirst m hm (splitR a) (splitR z) := by
  funext i
  simp only [splitR, combineFirst]
  split_ifs <;> rfl

/-- **The reduction of a product is the product of the reductions.** -/
theorem reduced_prodState {m : ℕ} (hm : m ≤ n) (φ : StateVector n d₁) (χ : StateVector n d₂)
    (a b : Config m (d₁ * d₂)) :
    reducedDensityFirst m hm (prodState φ χ) a b =
      reducedDensityFirst m hm φ (splitL a) (splitL b) *
        reducedDensityFirst m hm χ (splitR a) (splitR b) := by
  simp only [reducedDensityFirst]
  rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  refine Fintype.sum_equiv (splitEquiv (n - m)) _ _ fun z ↦ ?_
  simp only [prodState, mkStateVector_apply, splitL_combineFirst, splitR_combineFirst,
    splitEquiv_apply, star_mul']
  ring

/-- **The product of two AME states is AME.** -/
theorem prodState_isAME {φ : StateVector n d₁} {χ : StateVector n d₂} (hφ : IsAME φ)
    (hχ : IsAME χ) : IsAME (prodState φ χ) := by
  refine ⟨prodState_isNormalized hφ.1 hχ.1, fun π ↦ ?_⟩
  rw [permuteState_prodState]
  ext a b
  rw [reduced_prodState, hφ.2 π, hχ.2 π]
  simp only [maximallyMixed_apply, card_config]
  have hab : a = b ↔ splitL a = splitL b ∧ splitR a = splitR b := by
    rw [← Prod.mk.injEq, ← splitEquiv_apply, ← splitEquiv_apply]
    exact (splitEquiv (n / 2)).injective.eq_iff.symm
  by_cases h₁ : splitL a = splitL b <;> by_cases h₂ : splitR a = splitR b <;>
    simp [h₁, h₂, hab, mul_pow]
  ring

/-- **The product property**: AME(n, d₁) and AME(n, d₂) give AME(n, d₁ d₂). -/
theorem existsAME_mul (h₁ : ExistsAME n d₁) (h₂ : ExistsAME n d₂) : ExistsAME n (d₁ * d₂) := by
  obtain ⟨φ, hφ⟩ := h₁
  obtain ⟨χ, hχ⟩ := h₂
  exact ⟨prodState φ χ, prodState_isAME hφ hχ⟩

end AME7
