/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import AME7.Coupled
import AME7.Certificate

/-!
# The binary sector: the Steane logical states

The `[7, 3, 4]` simplex code `C` of Shi, Zhang, Zhao and Li (2026, Eq. (7) and Table I) and its
coset `C + 1` give the two seven-qubit states `codeState 0 = |0_L⟩` and `codeState 1 = |1_L⟩`, each
the uniform superposition of eight words (Eq. (8)). Words are stored as 7-bit masks.

For a permutation `π`, let `S` be the set of parties sent to the first three positions, and `R_st`
the cross reductions of the permuted states. Three finite facts about the sixteen words, checked by
the kernel for every set of three parties, give (their Eqs. (10), (13)):

* `codeRed_diag`: `R₀₀ + R₁₁ = ¼ · 1`;
* `codeRed_cross`: `R₀₁ = R₁₀ = 0` unless `S` is a line of the Fano plane.
-/

namespace AME7

open OpenQuantumProblem35

/- ### Placing levels through a permutation -/

section Place

variable {n m d : ℕ}

/-- Levels `u` on the parties that `π` sends to the first `m` positions, `z` on the rest. -/
def place (π : Equiv.Perm (Fin n)) (hm : m ≤ n) (u : Config m d) (z : Config (n - m) d) :
    Config n d :=
  permuteConfig π (combineFirst m hm u z)

/-- The parties that `π` sends to the first `m` positions. -/
def keptSet (π : Equiv.Perm (Fin n)) (m : ℕ) : Finset (Fin n) :=
  (firstHalf n m).map π.symm.toEmbedding

lemma mem_keptSet (π : Equiv.Perm (Fin n)) (i : Fin n) : i ∈ keptSet π m ↔ (π i).1 < m := by
  simp [keptSet, firstHalf]

/-- The first-block levels of a configuration, read through `π`. -/
def firstOf (π : Equiv.Perm (Fin n)) (hm : m ≤ n) (x : Config n d) : Config m d :=
  fun k ↦ x (π.symm (leftIndex hm k))

/-- The other levels of a configuration, read through `π`. -/
def restOf (π : Equiv.Perm (Fin n)) (hm : m ≤ n) (x : Config n d) : Config (n - m) d :=
  fun k ↦ x (π.symm (rightIndex hm k))

/-- Configurations are pairs of first-block and other levels, through `π`. -/
def placeEquiv (π : Equiv.Perm (Fin n)) (hm : m ≤ n) : Config m d × Config (n - m) d ≃ Config n d
    where
  toFun w := place π hm w.1 w.2
  invFun x := (firstOf π hm x, restOf π hm x)
  left_inv w := by
    ext k <;> simp [place, firstOf, restOf, permuteConfig]
  right_inv x := by
    funext i
    by_cases h : (π i).1 < m
    · have : leftIndex hm ⟨(π i).1, h⟩ = π i := Fin.ext rfl
      simp [place, permuteConfig, combineFirst, firstOf, h, this]
    · have : rightIndex hm ⟨(π i).1 - m, by omega⟩ = π i := Fin.ext (by simp [rightIndex]; omega)
      simp [place, permuteConfig, combineFirst, restOf, h, this]

/-- Off the kept parties, the placed levels come from `z` alone. -/
lemma place_off (π : Equiv.Perm (Fin n)) (hm : m ≤ n) (u v : Config m d) (z : Config (n - m) d)
    (i : Fin n) (hi : i ∉ keptSet π m) : place π hm u z i = place π hm v z i := by
  rw [mem_keptSet] at hi
  simp [place, permuteConfig, combineFirst, hi]

/-- On the kept parties, the placed levels come from `u` alone. -/
lemma place_on (π : Equiv.Perm (Fin n)) (hm : m ≤ n) (u : Config m d) (z z' : Config (n - m) d)
    (i : Fin n) (hi : i ∈ keptSet π m) : place π hm u z i = place π hm u z' i := by
  rw [mem_keptSet] at hi
  simp [place, permuteConfig, combineFirst, hi]

lemma place_injective (π : Equiv.Perm (Fin n)) (hm : m ≤ n) {u v : Config m d}
    {z : Config (n - m) d} (h : place π hm u z = place π hm v z) : u = v := by
  have := congrArg Prod.fst ((placeEquiv π hm).injective (show placeEquiv π hm (u, z) =
    placeEquiv π hm (v, z) from h))
  exact this

/-- A sum over the other levels is a sum over the configurations that agree with `u` on the kept
parties. -/
lemma sum_place (π : Equiv.Perm (Fin n)) (hm : m ≤ n) (u : Config m d) (z₀ : Config (n - m) d)
    (f : Config n d → ℂ) :
    ∑ z, f (place π hm u z) =
      ∑ x, if (∀ i ∈ keptSet π m, x i = place π hm u z₀ i) then f x else 0 := by
  rw [← (placeEquiv π hm).sum_comp, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single u]
  · exact Finset.sum_congr rfl fun z _ ↦ (if_pos fun i hi ↦ place_on π hm u z z₀ i hi).symm
  · intro v _ hv
    refine Finset.sum_eq_zero fun z _ ↦ ?_
    rw [if_neg]
    intro hall
    apply hv
    funext k
    have hk : π.symm (leftIndex hm k) ∈ keptSet π m := by
      rw [mem_keptSet]
      simp [leftIndex]
    have := hall _ hk
    rw [place_on π hm u z₀ z _ hk] at this
    simpa [placeEquiv, place, permuteConfig, combineFirst, leftIndex] using this
  · simp

end Place

/- ### Words as masks -/

/-- A seven-qubit word as its mask `∑ wᵢ 2^i`. -/
def wordMask (w : Config 7 2) : ℕ := (finFunctionFinEquiv w : ℕ)

lemma testBit_wordMask (w : Config 7 2) (i : Fin 7) :
    (wordMask w).testBit i.1 = decide (w i = 1) := by
  have h := finFunctionFinEquiv_symm_apply_val (finFunctionFinEquiv w) i
  rw [Equiv.symm_apply_apply] at h
  rw [Nat.testBit_eq_decide_div_mod_eq, wordMask, ← h]
  generalize w i = b
  fin_cases b <;> simp

lemma testBit_wordMask_ge (w : Config 7 2) {i : ℕ} (hi : 7 ≤ i) : (wordMask w).testBit i = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le (finFunctionFinEquiv w).2
    (Nat.pow_le_pow_right (by norm_num) hi))

lemma eq_iff_decide (a b : Fin 2) : a = b ↔ decide (a = 1) = decide (b = 1) := by
  fin_cases a <;> fin_cases b <;> simp

/-- Two words agree on the bits of `M` exactly when their masks agree there. -/
lemma agree_iff (w w' : Config 7 2) (M : ℕ) :
    (wordMask w ^^^ wordMask w') &&& M = 0 ↔ ∀ i : Fin 7, M.testBit i.1 = true → w i = w' i := by
  constructor
  · intro h i hi
    have := congrArg (fun x ↦ x.testBit i.1) h
    simp only [Nat.testBit_land, Nat.testBit_xor, testBit_wordMask, hi, Bool.and_true,
      Nat.zero_testBit] at this
    rw [eq_iff_decide]
    simpa using this
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_land, Nat.testBit_xor, Nat.zero_testBit]
    by_cases hi : i < 7
    · by_cases hM : M.testBit i
      · have := (eq_iff_decide _ _).mp (h ⟨i, hi⟩ hM)
        have h1 := testBit_wordMask w ⟨i, hi⟩
        have h2 := testBit_wordMask w' ⟨i, hi⟩
        simp only at h1 h2
        rw [h1, h2, this]
        simp
      · simp [hM]
    · rw [testBit_wordMask_ge w (by omega), testBit_wordMask_ge w' (by omega)]
      simp

/-- The parties outside a set, as bits of `127 ^^^ mask`. -/
lemma testBit_compl_maskOf (A : Finset (Fin 7)) (i : Fin 7) :
    (127 ^^^ maskOf A).testBit i.1 = true ↔ i ∉ A := by
  rw [Nat.testBit_xor, ← testBit_maskOf A i]
  have : (127 : ℕ).testBit i.1 = true := by
    have hi := i.2
    interval_cases (i : ℕ) <;> decide
  rw [this]
  cases (maskOf A).testBit i.1 <;> simp

/- ### The code data -/

/-- The simplex code `C` (`s = 0`) and its coset `C + 1` (`s = 1`), words as masks (Table I). -/
def codeMasks : Fin 2 → List ℕ :=
  ![[0, 29, 39, 58, 78, 83, 105, 116], [11, 22, 44, 49, 69, 88, 98, 127]]

/-- The lines `{t, t + 1, t + 3}` of the Fano plane, as masks (their Eq. (12), Fig. 1). -/
def fanoMasks : List ℕ := [11, 22, 44, 49, 69, 88, 98]

/-- The masks of the sets of three parties. -/
def cutMasks : List ℕ := (List.range 128).filter fun m ↦ popcount7 m = 3

/- The kernel checks the three facts about the sixteen words for every set of three parties. -/

/-- Two words of the same coset that agree outside a set of three parties are equal (each coset
has minimum distance four). -/
theorem code_same : ∀ m ∈ cutMasks, ∀ s : Fin 2, ∀ x ∈ codeMasks s, ∀ y ∈ codeMasks s,
    (x ^^^ y) &&& (127 ^^^ m) = 0 → x = y := by
  decide +kernel

/-- Every pattern on a set of three parties is met by exactly two of the sixteen words (the
Hamming code is an orthogonal array of strength three and index two). -/
theorem code_count : ∀ m ∈ cutMasks, ∀ p < 128,
    ((List.range 128).filter fun x ↦ decide ((x ∈ codeMasks 0 ∨ x ∈ codeMasks 1) ∧
      (x ^^^ p) &&& m = 0)).length = 2 := by
  decide +kernel

/-- Off the Fano lines, no word of `C` agrees with a word of `C + 1` outside the set. -/
theorem code_cross : ∀ m ∈ cutMasks, m ∉ fanoMasks → ∀ x ∈ codeMasks 0, ∀ y ∈ codeMasks 1,
    (x ^^^ y) &&& (127 ^^^ m) ≠ 0 := by
  decide +kernel

/-- The two cosets are disjoint. -/
theorem code_disjoint : ∀ x ∈ codeMasks 0, x ∉ codeMasks 1 := by
  decide +kernel

lemma maskOf_mem_cutMasks {A : Finset (Fin 7)} (hA : A.card = 3) : maskOf A ∈ cutMasks := by
  rw [cutMasks, List.mem_filter, List.mem_range]
  exact ⟨maskOf_lt A, by simpa [popcount7_maskOf] using hA⟩

/- ### The states and their cross reductions -/

/-- `1 / √8`. -/
noncomputable def c8 : ℂ := ((Real.sqrt 8 : ℝ) : ℂ)⁻¹

lemma c8_mul_star : c8 * star c8 = (8 : ℂ)⁻¹ := by
  simp only [c8, star_inv₀, Complex.star_def, Complex.conj_ofReal]
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  push_cast
  rfl

lemma c8_mul_conj : c8 * (starRingEnd ℂ) c8 = (8 : ℂ)⁻¹ := c8_mul_star

/-- The Steane logical states: `|0_L⟩` (`s = 0`) and `|1_L⟩` (`s = 1`). -/
noncomputable def codeState (s : Fin 2) : StateVector 7 2 :=
  mkStateVector fun w ↦ if wordMask w ∈ codeMasks s then c8 else 0

/-- The cross reductions of the permuted logical states, to the first three parties. -/
noncomputable def codeRed (π : Equiv.Perm (Fin 7)) (s t : Fin 2) :
    Matrix (Config 3 2) (Config 3 2) ℂ :=
  crossRed 3 (by norm_num) (permuteState π (codeState s)) (permuteState π (codeState t))

lemma codeRed_apply (π : Equiv.Perm (Fin 7)) (s t : Fin 2) (u v : Config 3 2) :
    codeRed π s t u v = ∑ z : Config (7 - 3) 2,
      (if wordMask (place π (by norm_num) u z) ∈ codeMasks s ∧
          wordMask (place π (by norm_num) v z) ∈ codeMasks t then (8 : ℂ)⁻¹ else 0) := by
  simp only [codeRed, crossRed, permuteState_apply, codeState]
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  simp only [place]
  split_ifs <;> simp_all [c8_mul_conj]

/-- Placed configurations agree off the kept parties, in mask form. -/
lemma place_agree (π : Equiv.Perm (Fin 7)) (u v : Config 3 2) (z : Config (7 - 3) 2) :
    (wordMask (place π (by norm_num) u z) ^^^ wordMask (place π (by norm_num) v z)) &&&
      (127 ^^^ maskOf (keptSet π 3)) = 0 := by
  rw [agree_iff]
  intro i hi
  exact place_off π _ u v z i ((testBit_compl_maskOf _ i).mp hi)

lemma card_keptSet (π : Equiv.Perm (Fin 7)) : (keptSet π 3).card = 3 := by
  rw [keptSet, Finset.card_map, card_firstHalf (by norm_num)]

/-- **Off the Fano lines the binary cross terms vanish** (their Eq. (36)). -/
theorem codeRed_cross (π : Equiv.Perm (Fin 7)) (hS : maskOf (keptSet π 3) ∉ fanoMasks)
    (s t : Fin 2) (hst : s ≠ t) : codeRed π s t = 0 := by
  have hcut := maskOf_mem_cutMasks (card_keptSet π)
  ext u v
  rw [codeRed_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun z _ ↦ ?_
  rw [if_neg]
  rintro ⟨hx, hy⟩
  have hagree := place_agree π u v z
  fin_cases s <;> fin_cases t
  · exact hst rfl
  · exact code_cross _ hcut hS _ hx _ hy hagree
  · rw [Nat.xor_comm] at hagree
    exact code_cross _ hcut hS _ hy _ hx hagree
  · exact hst rfl

/-- **The binary diagonal terms add up to `¼ · 1`** (their Eq. (10)). -/
theorem codeRed_diag (π : Equiv.Perm (Fin 7)) :
    codeRed π 0 0 + codeRed π 1 1 = (4 : ℂ)⁻¹ • 1 := by
  have hcut := maskOf_mem_cutMasks (card_keptSet π)
  ext u v
  rw [Matrix.add_apply, codeRed_apply, codeRed_apply, ← Finset.sum_add_distrib,
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases huv : u = v
  · subst huv
    simp only [and_self]
    -- Combine the two cosets, then count with the kernel fact.
    have hcomb : ∀ z : Config (7 - 3) 2,
        ((if wordMask (place π (by norm_num) u z) ∈ codeMasks 0 then (8 : ℂ)⁻¹ else 0) +
          if wordMask (place π (by norm_num) u z) ∈ codeMasks 1 then (8 : ℂ)⁻¹ else 0) =
        if (wordMask (place π (by norm_num) u z) ∈ codeMasks 0 ∨
          wordMask (place π (by norm_num) u z) ∈ codeMasks 1) then (8 : ℂ)⁻¹ else 0 := by
      intro z
      by_cases h0 : wordMask (place π (by norm_num) u z) ∈ codeMasks 0
      · simp [h0, code_disjoint _ h0]
      · by_cases h1 : wordMask (place π (by norm_num) u z) ∈ codeMasks 1 <;> simp [h0, h1]
    simp only [hcomb]
    set z₀ : Config (7 - 3) 2 := fun _ ↦ 0
    rw [sum_place π (by norm_num) u z₀
      (fun x ↦ if wordMask x ∈ codeMasks 0 ∨ wordMask x ∈ codeMasks 1 then (8 : ℂ)⁻¹ else 0)]
    have hcond : ∀ x : Config 7 2, (∀ i ∈ keptSet π 3, x i = place π (by norm_num) u z₀ i) ↔
        (wordMask x ^^^ wordMask (place π (by norm_num) u z₀)) &&& maskOf (keptSet π 3) = 0 := by
      intro x
      rw [agree_iff]
      exact ⟨fun h i hi ↦ h i ((testBit_maskOf _ i).mp hi),
        fun h i hi ↦ h i ((testBit_maskOf _ i).mpr hi)⟩
    simp only [hcond, ← ite_and]
    set P := wordMask (place π (by norm_num) u z₀)
    set M := maskOf (keptSet π 3)
    have hsum : ∑ x : Config 7 2, (if (wordMask x ^^^ P) &&& M = 0 ∧
        (wordMask x ∈ codeMasks 0 ∨ wordMask x ∈ codeMasks 1) then (8 : ℂ)⁻¹ else 0) =
        ∑ y : Fin 128, (if ((y : ℕ) ^^^ P) &&& M = 0 ∧
          ((y : ℕ) ∈ codeMasks 0 ∨ (y : ℕ) ∈ codeMasks 1) then (8 : ℂ)⁻¹ else 0) :=
      Fintype.sum_equiv finFunctionFinEquiv _ _ fun _ ↦ rfl
    rw [hsum, Fin.sum_univ_eq_sum_range (fun y ↦ if (y ^^^ P) &&& M = 0 ∧
      (y ∈ codeMasks 0 ∨ y ∈ codeMasks 1) then (8 : ℂ)⁻¹ else 0), ← Finset.sum_filter,
      Finset.sum_const, nsmul_eq_mul]
    have hcount := code_count M hcut P (finFunctionFinEquiv (place π (by norm_num) u z₀)).2
    have hcard : (Finset.filter (fun y ↦ (y ^^^ P) &&& M = 0 ∧
        (y ∈ codeMasks 0 ∨ y ∈ codeMasks 1)) (Finset.range 128)).card = 2 := by
      refine Eq.trans ?_ hcount
      rw [← List.toFinset_card_of_nodup (List.nodup_range.filter _),
        List.toFinset_filter, List.toFinset_range]
      congr 1
      ext y
      simp [and_comm]
    rw [hcard]
    norm_num
  · rw [if_neg huv, mul_zero]
    refine Finset.sum_eq_zero fun z _ ↦ ?_
    have hagree := place_agree π u v z
    have key : ∀ s : Fin 2, ¬ (wordMask (place π (by norm_num) u z) ∈ codeMasks s ∧
        wordMask (place π (by norm_num) v z) ∈ codeMasks s) := by
      rintro s ⟨hx, hy⟩
      have hxy := code_same _ hcut s _ hx _ hy hagree
      exact huv (place_injective π (by norm_num) (finFunctionFinEquiv.injective (Fin.ext hxy)))
    rw [if_neg (key 0), if_neg (key 1), add_zero]

end AME7
