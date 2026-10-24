/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import AME7.Product

/-!
# Coupled states `(φ₀ ⊗ χ₀ + φ₁ ⊗ χ₁) / √2`

For pairs of states `φ₀, φ₁` with local dimension `d₁` and `χ₀, χ₁` with `d₂` on the same parties,
`coupledState φ χ` has amplitude `(φ₀(x₁) χ₀(x₂) + φ₁(x₁) χ₁(x₂)) / √2`, each level of `d₁ d₂`
read as a pair (`AME7.Product`). This is the shape of the AME(7, 2q) state of Shi, Zhang, Zhao and
Li (2026, Eq. (31)).

* `reduced_coupledState`: its reduction is `½ ∑_{s,t} R_st ⊗ T_st`, with `R_st`, `T_st` the cross
  reductions of the factors (`crossRed`), their Eq. (33);
* `isNormalized_of_maxMixed`: a state with a maximally mixed reduction is normalized, so the
  normalization of a coupled state need not be checked separately.
-/

namespace AME7

open OpenQuantumProblem35

variable {n d₁ d₂ : ℕ}

/-- The cross reduction `(a, b) ↦ ∑_z ψ(a z) · conj ψ'(b z)` of two states to the first `m`
parties. -/
noncomputable def crossRed {d : ℕ} (m : ℕ) (hm : m ≤ n) (ψ ψ' : StateVector n d) :
    Matrix (Config m d) (Config m d) ℂ :=
  fun a b ↦ ∑ z : Config (n - m) d, ψ (combineFirst m hm a z) * star (ψ' (combineFirst m hm b z))

lemma crossRed_self {d m : ℕ} (hm : m ≤ n) (ψ : StateVector n d) :
    crossRed m hm ψ ψ = reducedDensityFirst m hm ψ := rfl

/-- The coupled state `(φ₀ ⊗ χ₀ + φ₁ ⊗ χ₁) / √2`. -/
noncomputable def coupledState (φ : Fin 2 → StateVector n d₁) (χ : Fin 2 → StateVector n d₂) :
    StateVector n (d₁ * d₂) :=
  mkStateVector fun x ↦ ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ∑ s, φ s (splitL x) * χ s (splitR x)

/-- Permuting the parties of a coupled state permutes all four factors. -/
lemma permuteState_coupledState (π : Equiv.Perm (Fin n)) (φ : Fin 2 → StateVector n d₁)
    (χ : Fin 2 → StateVector n d₂) :
    permuteState π (coupledState φ χ) =
      coupledState (fun s ↦ permuteState π (φ s)) (fun s ↦ permuteState π (χ s)) := by
  ext x
  simp only [permuteState_apply, coupledState, mkStateVector_apply]
  rfl

lemma sqrt_two_inv_mul_star : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * star (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) =
    (2 : ℂ)⁻¹ := by
  simp only [star_inv₀, Complex.star_def, Complex.conj_ofReal]
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt zero_le_two]
  push_cast
  rfl

/-- **The reduction of a coupled state** is `½ ∑_{s,t} R_st ⊗ T_st`. -/
theorem reduced_coupledState {m : ℕ} (hm : m ≤ n) (φ : Fin 2 → StateVector n d₁)
    (χ : Fin 2 → StateVector n d₂) (a b : Config m (d₁ * d₂)) :
    reducedDensityFirst m hm (coupledState φ χ) a b =
      (2 : ℂ)⁻¹ * ∑ s, ∑ t, crossRed m hm (φ s) (φ t) (splitL a) (splitL b) *
        crossRed m hm (χ s) (χ t) (splitR a) (splitR b) := by
  have hz : ∀ z : Config (n - m) (d₁ * d₂),
      coupledState φ χ (combineFirst m hm a z) * star (coupledState φ χ (combineFirst m hm b z)) =
        (2 : ℂ)⁻¹ * ∑ s, ∑ t,
          (φ s (combineFirst m hm (splitL a) (splitL z)) *
              star (φ t (combineFirst m hm (splitL b) (splitL z)))) *
            (χ s (combineFirst m hm (splitR a) (splitR z)) *
              star (χ t (combineFirst m hm (splitR b) (splitR z)))) := by
    intro z
    simp only [coupledState, mkStateVector_apply, splitL_combineFirst, splitR_combineFirst,
      star_mul', star_sum]
    rw [mul_mul_mul_comm, sqrt_two_inv_mul_star, Finset.sum_mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun s _ ↦ Finset.sum_congr rfl fun t _ ↦ by ring
  simp only [reducedDensityFirst, hz, ← Finset.mul_sum]
  congr 1
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun s _ ↦ ?_)
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun t _ ↦ ?_)
  simp only [crossRed]
  rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (splitEquiv (n - m)) _ _ fun z ↦ rfl

/-- Splitting a configuration into the first `m` parties and the rest is a bijection. -/
def combineEquiv {d m : ℕ} (hm : m ≤ n) : Config m d × Config (n - m) d ≃ Config n d where
  toFun w := combineFirst m hm w.1 w.2
  invFun x := (fun i ↦ x (leftIndex hm i), fun j ↦ x (rightIndex hm j))
  left_inv w := by
    ext <;> simp
  right_inv x := by
    funext i
    simp only [combineFirst]
    split_ifs with h
    · exact congrArg x (Fin.ext rfl)
    · exact congrArg x (Fin.ext (by simp [rightIndex]; omega))

/-- **A state with a maximally mixed reduction is normalized**: its squared norm is the trace of
the reduction, which is `1`. -/
theorem isNormalized_of_maxMixed {d m : ℕ} [NeZero d] (hm : m ≤ n) {ψ : StateVector n d}
    (h : HasMaximallyMixedFirstReduction m hm ψ) : IsNormalized ψ := by
  rw [isNormalized_iff_norm_sq_eq_one, EuclideanSpace.norm_sq_eq]
  have hd : ((d : ℂ) ^ m) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne d))
  have htr : ((∑ x, ‖ψ.ofLp x‖ ^ 2 : ℝ) : ℂ) = ∑ a, reducedDensityFirst m hm ψ a a := by
    push_cast
    rw [← (combineEquiv hm).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun z _ ↦ ?_
    rw [Complex.star_def, Complex.mul_conj']
    rfl
  have hval : ∑ a, reducedDensityFirst m hm ψ a a = 1 := by
    rw [h]
    simp only [maximallyMixed_apply, card_config, if_true, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    push_cast
    exact mul_inv_cancel₀ hd
  rw [hval] at htr
  exact_mod_cast htr

end AME7
