/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import AME72.Pauli

/-!
# The Bloch expansion, even and odd parts

Every operator on `n` qubits is a combination of Pauli strings, `X = ∑_α c_α(X) τ_α` with
`c_α(X) = 2^(-n) tr(τ_αᵀ X)` (`expansion`), and the coefficients of a Pauli string are `δ`
(`coef_tau`). The *even part* of `X` keeps the strings of even weight, the *odd part* those of odd
weight.

* `oddPart_anticomm`: the parity rule for operators,
  `odd {X, Y} = {even X, odd Y} + {odd X, even Y}`;
* `red_tau`: reducing a Pauli string to `U` keeps it, times `2^|Uᶜ|`, if it is the identity outside
  `U`, and kills it otherwise.
-/

@[expose] public section

namespace AME72

open OpenQuantumProblem35 Finset

variable {n : ℕ}

/-- The Bloch coefficient `c_α(X) = 2^(-n) tr(τ_αᵀ X)`, as a linear functional. -/
noncomputable def coef (α : Fin n → Fin 4) : Matrix (Config n 2) (Config n 2) ℂ →ₗ[ℂ] ℂ where
  toFun X := ((2 : ℂ) ^ n)⁻¹ * ∑ x, ∑ y, tau α x y * X x y
  map_add' X Y := by
    simp only [Matrix.add_apply, mul_add, sum_add_distrib]
  map_smul' c X := by
    simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum]
    exact sum_congr rfl fun x _ ↦ sum_congr rfl fun y _ ↦ by ring

lemma coef_apply (α : Fin n → Fin 4) (X : Matrix (Config n 2) (Config n 2) ℂ) :
    coef α X = ((2 : ℂ) ^ n)⁻¹ * ∑ x, ∑ y, tau α x y * X x y := rfl

/-- One qubit: the four basis matrices are complete. -/
lemma tau1_complete : ∀ s t u v : Fin 2,
    ∑ a : Fin 4, tau1 a s t * tau1 a u v =
      2 * (if s = u then 1 else 0) * (if t = v then 1 else 0) := by
  decide

/-- One qubit: the four basis matrices are orthogonal. -/
lemma tau1_orth : ∀ a b : Fin 4,
    ∑ s : Fin 2, ∑ t : Fin 2, tau1 a s t * tau1 b s t = 2 * (if a = b then 1 else 0) := by
  decide

/-- A product of one-qubit indicators is the indicator of all of them. -/
lemma prod_indicator {β : Type*} [DecidableEq β] (f g : Fin n → β) :
    ∏ i, ((if f i = g i then 1 else 0 : ℤ) : ℂ) = if f = g then 1 else 0 := by
  by_cases h : f = g
  · simp [h]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    rw [ite_eq_right h]
    exact prod_eq_zero (mem_univ i) (by simp [hi])

/-- Completeness of Pauli strings: `∑_α τ_α(x, y) τ_α(u, v) = 2^n δ(x, u) δ(y, v)`. -/
lemma sum_tau_mul_tau (x y u v : Config n 2) :
    ∑ α : Fin n → Fin 4, tau α x y * tau α u v =
      (2 : ℂ) ^ n * ((if x = u then 1 else 0) * (if y = v then 1 else 0)) := by
  simp only [tau, ← prod_mul_distrib]
  rw [sum_prod_eq' (fun i a ↦ (tau1 a (x i) (y i) : ℂ) * (tau1 a (u i) (v i) : ℂ))]
  have h : ∀ i, ∑ a : Fin 4, (tau1 a (x i) (y i) : ℂ) * (tau1 a (u i) (v i) : ℂ) =
      2 * (((if x i = u i then 1 else 0 : ℤ) : ℂ) * ((if y i = v i then 1 else 0 : ℤ) : ℂ)) := by
    intro i
    have := congrArg (fun z : ℤ ↦ (z : ℂ)) (tau1_complete (x i) (y i) (u i) (v i))
    push_cast at this ⊢
    rw [this]
    ring
  rw [prod_congr rfl fun i _ ↦ h i, prod_mul_distrib, prod_mul_distrib, prod_const, card_univ,
    Fintype.card_fin, prod_indicator, prod_indicator]

/-- **The Bloch expansion.** `X = ∑_α c_α(X) τ_α`. -/
theorem expansion (X : Matrix (Config n 2) (Config n 2) ℂ) :
    X = ∑ α, coef α X • tau α := by
  ext u v
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, smul_eq_mul, coef_apply]
  have h : ∑ x, ∑ y, X x y * ∑ α : Fin n → Fin 4, tau α x y * tau α u v = (2 : ℂ) ^ n * X u v := by
    simp only [sum_tau_mul_tau]
    rw [sum_eq_single u (fun x _ hx ↦ by simp [hx]) (by simp),
      sum_eq_single v (fun y _ hy ↦ by simp [hy]) (by simp)]
    simp only [ite_true, mul_one]
    ring
  calc X u v = ((2 : ℂ) ^ n)⁻¹ * ∑ x, ∑ y, X x y * ∑ α : Fin n → Fin 4, tau α x y * tau α u v := by
        rw [h]; field_simp
    _ = ∑ x, ∑ y, ∑ α : Fin n → Fin 4, ((2 : ℂ) ^ n)⁻¹ * (X x y * (tau α x y * tau α u v)) := by
        simp only [mul_sum]
    _ = ∑ α : Fin n → Fin 4, ∑ x, ∑ y, ((2 : ℂ) ^ n)⁻¹ * (X x y * (tau α x y * tau α u v)) :=
        (sum_congr rfl fun _ _ ↦ sum_comm).trans sum_comm
    _ = _ := sum_congr rfl fun α _ ↦ by
        rw [mul_sum, sum_mul]
        refine sum_congr rfl fun x _ ↦ ?_
        rw [mul_sum, sum_mul]
        exact sum_congr rfl fun y _ ↦ by ring

/-- **Orthogonality.** The coefficients of a Pauli string are `δ`. -/
theorem coef_tau (α β : Fin n → Fin 4) : coef α (tau β) = if α = β then 1 else 0 := by
  rw [coef_apply]
  have h : ∑ x, ∑ y, tau α x y * tau β x y = (2 : ℂ) ^ n * if α = β then 1 else 0 := by
    simp only [tau, ← prod_mul_distrib]
    rw [sum_sum_prod_eq (fun i s t ↦ (tau1 (α i) s t : ℂ) * (tau1 (β i) s t : ℂ))]
    have hi : ∀ i, ∑ s : Fin 2, ∑ t : Fin 2, (tau1 (α i) s t : ℂ) * (tau1 (β i) s t : ℂ) =
        2 * ((if α i = β i then 1 else 0 : ℤ) : ℂ) := by
      intro i
      have := congrArg (fun z : ℤ ↦ (z : ℂ)) (tau1_orth (α i) (β i))
      push_cast at this ⊢
      exact this
    rw [prod_congr rfl fun i _ ↦ hi i, prod_mul_distrib, prod_const, card_univ, Fintype.card_fin,
      prod_indicator]
  rw [h]
  field_simp

/-- The even part: the strings of even weight. -/
noncomputable def evenPart : Matrix (Config n 2) (Config n 2) ℂ →ₗ[ℂ]
    Matrix (Config n 2) (Config n 2) ℂ :=
  ∑ α, if Even (weight α) then (coef α).smulRight (tau α) else 0

/-- The odd part: the strings of odd weight. -/
noncomputable def oddPart : Matrix (Config n 2) (Config n 2) ℂ →ₗ[ℂ]
    Matrix (Config n 2) (Config n 2) ℂ :=
  ∑ α, if Even (weight α) then 0 else (coef α).smulRight (tau α)

lemma evenPart_apply (X : Matrix (Config n 2) (Config n 2) ℂ) :
    evenPart X = ∑ α, (if Even (weight α) then coef α X else 0) • tau α := by
  rw [evenPart, LinearMap.sum_apply]
  exact sum_congr rfl fun α _ ↦ by split_ifs <;> simp

lemma oddPart_apply (X : Matrix (Config n 2) (Config n 2) ℂ) :
    oddPart X = ∑ α, (if Even (weight α) then 0 else coef α X) • tau α := by
  rw [oddPart, LinearMap.sum_apply]
  exact sum_congr rfl fun α _ ↦ by split_ifs <;> simp

/-- The odd part of a Pauli string: itself if its weight is odd, `0` if even. -/
lemma oddPart_tau (γ : Fin n → Fin 4) :
    oddPart (tau γ) = if Even (weight γ) then 0 else tau γ := by
  rw [oddPart_apply]
  simp only [coef_tau]
  rw [sum_eq_single γ (fun α _ hα ↦ by simp [hα]) (by simp)]
  by_cases h : Even (weight γ) <;> simp [h]

/-- The anticommutator of two Pauli strings. -/
def anticomm (α β : Fin n → Fin 4) : Matrix (Config n 2) (Config n 2) ℂ :=
  tau α * tau β + tau β * tau α

/-- **The parity rule, for one pair of strings.** The odd part of `{τ_α, τ_β}` is all of it if the
weights of `α` and `β` have different parities, and `0` if they have the same parity. -/
lemma oddPart_anticomm_tau (α β : Fin n → Fin 4) :
    oddPart (anticomm α β) =
      if (Even (weight α) ↔ Even (weight β)) then 0 else anticomm α β := by
  rcases parity_rule α β with h | h
  · rw [anticomm, h, map_zero]
    simp
  · have hmul : mulStr β α = mulStr α β := funext fun i ↦ mul1_comm (α i) (β i)
    have hab : anticomm α β = (sgnStr α β + sgnStr β α) • tau (mulStr α β) := by
      rw [anticomm, tau_mul, tau_mul, hmul, add_smul]
    have hγ : Even (weight (mulStr α β)) ↔ (Even (weight α) ↔ Even (weight β)) := by
      rw [Nat.even_add, Nat.even_add] at h
      tauto
    rw [hab, map_smul, oddPart_tau]
    by_cases hα : Even (weight α) <;> by_cases hβ : Even (weight β) <;> simp [hα, hβ, hγ]

/-- Two expanded operators: `{∑ a_α τ_α, ∑ b_β τ_β} = ∑_{α, β} a_α b_β {τ_α, τ_β}`. -/
lemma anticomm_expand (a b : (Fin n → Fin 4) → ℂ) :
    (∑ α, a α • tau α) * (∑ β, b β • tau β) + (∑ β, b β • tau β) * (∑ α, a α • tau α) =
      ∑ α, ∑ β, (a α * b β) • anticomm α β := by
  rw [sum_mul_sum, sum_mul_sum]
  rw [show (∑ β, ∑ α, (b β • tau β) * (a α • tau α)) = ∑ α, ∑ β, (b β • tau β) * (a α • tau α)
    from sum_comm, ← sum_add_distrib]
  refine sum_congr rfl fun α _ ↦ ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun β _ ↦ ?_
  rw [anticomm, smul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, smul_smul, mul_comm (b β) (a α)]

/-- **The parity rule for operators.** `odd {X, Y} = {even X, odd Y} + {odd X, even Y}`. -/
theorem oddPart_anticomm (X Y : Matrix (Config n 2) (Config n 2) ℂ) :
    oddPart (X * Y + Y * X) =
      (evenPart X * oddPart Y + oddPart Y * evenPart X) +
        (oddPart X * evenPart Y + evenPart Y * oddPart X) := by
  have eX := expansion X
  have eY := expansion Y
  have hXY : X * Y + Y * X = ∑ α, ∑ β, (coef α X * coef β Y) • anticomm α β := by
    rw [← anticomm_expand, ← eX, ← eY]
  rw [hXY, evenPart_apply X, oddPart_apply Y, evenPart_apply Y, oddPart_apply X, anticomm_expand,
    anticomm_expand, ← sum_add_distrib, map_sum]
  refine sum_congr rfl fun α _ ↦ ?_
  rw [← sum_add_distrib, map_sum]
  refine sum_congr rfl fun β _ ↦ ?_
  rw [map_smul, oddPart_anticomm_tau, ← add_smul]
  by_cases hα : Even (weight α) <;> by_cases hβ : Even (weight β) <;> simp [hα, hβ]

/-- One qubit: reducing a basis matrix keeps it if the qubit is kept, and traces it out (giving
`2` for the identity, `0` otherwise) if not. -/
lemma kern_tau1 : ∀ (b : Bool) (a : Fin 4) (x x' : Fin 2),
    ∑ s : Fin 2, ∑ t : Fin 2, (kern b x x' s t : ℤ) * tau1 a s t =
      (if b then 1 else 2 * (if a = 0 then 1 else 0)) * tau1 a x x' := by
  decide

/-- **Reducing a Pauli string.** `red U τ_α = 2^|Uᶜ| τ_α` if `α` is the identity outside `U`, and
`0` otherwise. -/
theorem red_tau (U : Finset (Fin n)) (α : Fin n → Fin 4) :
    red U (tau α) = if (∀ i, i ∉ U → α i = 0) then (2 : ℂ) ^ Uᶜ.card • tau α else 0 := by
  ext x x'
  have hprod : ∏ i, ((if decide (i ∈ U) then 1 else 2 * (if α i = 0 then 1 else 0) : ℤ) : ℂ) =
      if (∀ i, i ∉ U → α i = 0) then (2 : ℂ) ^ Uᶜ.card else 0 := by
    simp only [decide_eq_true_eq]
    push_cast
    rw [prod_ite, prod_const_one, one_mul, prod_mul_distrib, prod_const, prod_boole]
    have hc : (univ.filter fun i ↦ i ∉ U).card = Uᶜ.card := by
      congr 1
      ext i
      simp
    rw [hc]
    by_cases h : ∀ i, i ∉ U → α i = 0
    · rw [ite_eq_left h, ite_eq_left (fun i hi ↦ h i (by simpa using hi)), mul_one]
    · rw [ite_eq_right h, ite_eq_right (fun h' ↦ h fun i hi ↦ h' i (by simpa using hi)), mul_zero]
  simp only [red, kernProd, tau, ← prod_mul_distrib]
  rw [sum_sum_prod_eq (fun i s t ↦ (kern (decide (i ∈ U)) (x i) (x' i) s t : ℂ) *
    (tau1 (α i) s t : ℂ))]
  have hi : ∀ i, ∑ s : Fin 2, ∑ t : Fin 2,
      (kern (decide (i ∈ U)) (x i) (x' i) s t : ℂ) * (tau1 (α i) s t : ℂ) =
        ((if decide (i ∈ U) then 1 else 2 * (if α i = 0 then 1 else 0) : ℤ) : ℂ) *
          (tau1 (α i) (x i) (x' i) : ℂ) := by
    intro i
    exact_mod_cast kern_tau1 (decide (i ∈ U)) (α i) (x i) (x' i)
  rw [prod_congr rfl fun i _ ↦ hi i, prod_mul_distrib, hprod]
  split_ifs <;> simp [Matrix.smul_apply, tau]

end AME72
