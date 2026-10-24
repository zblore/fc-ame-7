/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import AME7.GraphState
import AME7.Data

/-!
# Cut certificates for seven parties, checked in natural-number arithmetic

A graph matrix on seven parties with `k` digits each is given by an integer table `T` on the
coordinates, numbered `c = k i + a` (`idx`); the matrix of the quadratic form is its party-wise
upper triangle (`graphU`). For a cut `A` of three parties, a certificate is an integer matrix `R`
from the coordinates outside `A` to those inside with `T[A, Aᶜ] · R = d · 1`, exactly or modulo
`p`. If `p = 0` in `ZMod q` and `d` is a unit there, the block of `T` is injective on the
coordinates of `A`, which is the cut condition (`cutInj_of_inverse`).

The kernel checks every certificate in natural-number and integer arithmetic (`certOK`), and that
there is one for every set of three parties (`popcount7`). `cutInj_all_of_certs` turns those
checks into the cut condition for every set of three parties, for any `q`.
-/

namespace AME7

open OpenQuantumProblem35
open scoped Matrix

variable {q : ℕ} [NeZero q] {k : ℕ}

/-- The natural-number index `k i + a` of the coordinate `(i, a)`. -/
def idx (p : Coord 7 k) : ℕ := (finProdFinEquiv p : ℕ)

lemma idx_eq (p : Coord 7 k) : idx p = p.2.1 + k * p.1.1 := by
  simp [idx, finProdFinEquiv_apply_val]

lemma idx_lt (p : Coord 7 k) : idx p < 7 * k := (finProdFinEquiv p).2

lemma idx_injective : Function.Injective (idx (k := k)) := fun _ _ h ↦
  finProdFinEquiv.injective (Fin.ext h)

lemma idx_div (p : Coord 7 k) : idx p / k = p.1.1 := by
  have hk : 0 < k := Nat.pos_of_ne_zero fun h ↦ by have := p.2.2; omega
  rw [idx_eq, Nat.add_mul_div_left _ _ hk, Nat.div_eq_of_lt p.2.2, zero_add]

/-- Whether coordinate `c` lies in the cut with mask `m`. -/
def inCut (k m c : ℕ) : Bool := m.testBit (c / k)

/-- The position of coordinate `c` among the coordinates inside (`b = true`) or outside the cut. -/
def pos (k m c : ℕ) (b : Bool) : ℕ := ((List.range c).filter fun c' ↦ inCut k m c' == b).length

/-- Entry `(j, l)` of a certificate, for `j` outside the cut and `l` inside. -/
def certR (k m : ℕ) (L : List ℤ) (j l : ℕ) : ℤ :=
  L.getD (3 * k * pos k m j false + pos k m l true) 0

/-- Entry `(i, l)` of `T[A, Aᶜ] · R`. -/
def entry (k : ℕ) (T : ℕ → ℕ → ℤ) (m : ℕ) (L : List ℤ) (i l : ℕ) : ℤ :=
  ((List.range (7 * k)).map fun j ↦ if inCut k m j then 0 else T i j * certR k m L j l).sum

/-- A certificate `(m, d, L)` is good when `T[A, Aᶜ] · R = d · 1` modulo `p` on the cut. -/
def certOK (k p : ℕ) (T : ℕ → ℕ → ℤ) (c : ℕ × ℤ × List ℤ) : Bool :=
  (List.range (7 * k)).all fun i ↦ (List.range (7 * k)).all fun l ↦
    !(inCut k c.1 i && inCut k c.1 l) ||
      (entry k T c.1 c.2.2 i l - if i = l then c.2.1 else 0) % (p : ℤ) == 0

/-- The number of the seven parties in mask `m`. -/
def popcount7 (m : ℕ) : ℕ := ((List.range 7).filter fun i ↦ m.testBit i).length

/-- The party-wise upper triangle of `T`: the matrix of the quadratic form. -/
def graphU (k : ℕ) (T : ℕ → ℕ → ℤ) : Matrix (Coord 7 k) (Coord 7 k) (ZMod q) :=
  fun p r ↦ if p.1 < r.1 then (T (idx p) (idx r) : ZMod q) else 0

omit [NeZero q] in
/-- Off the party-diagonal blocks, `U + Uᵀ` is the table. -/
lemma graphU_add (T : ℕ → ℕ → ℤ) (hT : ∀ i < 7 * k, ∀ j < 7 * k, T i j = T j i)
    (p r : Coord 7 k) (h : p.1 ≠ r.1) :
    (graphU (q := q) k T + (graphU (q := q) k T)ᵀ : Matrix (Coord 7 k) (Coord 7 k) (ZMod q)) p r =
      (T (idx p) (idx r) : ZMod q) := by
  simp only [Matrix.add_apply, Matrix.transpose_apply, graphU]
  rcases lt_or_gt_of_ne h with h' | h'
  · simp [h', h'.not_gt]
  · simp [h', h'.not_gt, hT _ (idx_lt p) _ (idx_lt r)]

/-- A sum over `List.range (7k)` is a sum over the coordinates. -/
lemma sum_range_coord {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ((List.range (7 * k)).map f).sum = ∑ p : Coord 7 k, f (idx p) := by
  rw [← List.sum_toFinset f List.nodup_range, List.toFinset_range, Finset.sum_range]
  exact (Fintype.sum_equiv finProdFinEquiv _ _ fun _ ↦ rfl).symm

omit [NeZero q] in
/-- **A block with a right inverse up to a unit is injective**: the cut condition follows. -/
theorem cutInj_of_inverse {n : ℕ} (S : Matrix (Coord n k) (Coord n k) (ZMod q))
    (A : Finset (Fin n)) (R : Coord n k → Coord n k → ZMod q) (d : ZMod q) (hd : IsUnit d)
    (h : ∀ i, i.1 ∈ A → ∀ l, l.1 ∈ A →
      ∑ j, (if j.1 ∈ A then 0 else S i j * R j l) = if i = l then d else 0) :
    CutInj S A := by
  intro w hw hcol
  funext l
  by_cases hl : l.1 ∈ A
  · have key : d * w l = 0 := by
      calc d * w l = ∑ i, w i * (if i = l then d else 0) := by simp [mul_comm]
        _ = ∑ i, w i * ∑ j, (if j.1 ∈ A then 0 else S i j * R j l) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          by_cases hi : i.1 ∈ A
          · rw [h i hi l hl]
          · simp [hw i hi]
        _ = ∑ j, (if j.1 ∈ A then 0 else (∑ i, w i * S i j) * R j l) := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          split_ifs <;> simp [Finset.sum_mul, mul_assoc]
        _ = 0 := by
          refine Finset.sum_eq_zero fun j _ ↦ ?_
          split_ifs with hj
          · rfl
          · simp [hcol j hj]
    exact hd.mul_right_eq_zero.mp key
  · exact hw l hl

omit [NeZero q] in
/-- A passed certificate check, as an identity in `ZMod q`. -/
lemma certOK_sum {p : ℕ} (hp : ((p : ℤ) : ZMod q) = 0) {T : ℕ → ℕ → ℤ} {c : ℕ × ℤ × List ℤ}
    (hc : certOK k p T c = true) (i l : Coord 7 k) (hi : inCut k c.1 (idx i) = true)
    (hl : inCut k c.1 (idx l) = true) :
    ∑ j : Coord 7 k, (if inCut k c.1 (idx j) then 0 else
        (T (idx i) (idx j) : ZMod q) * (certR k c.1 c.2.2 (idx j) (idx l) : ZMod q)) =
      if i = l then (c.2.1 : ZMod q) else 0 := by
  have h : (entry k T c.1 c.2.2 (idx i) (idx l) - if idx i = idx l then c.2.1 else 0) % (p : ℤ)
      = 0 := by
    simp only [certOK, List.all_eq_true, List.mem_range] at hc
    simpa [hi, hl] using hc _ (idx_lt i) _ (idx_lt l)
  obtain ⟨t, ht⟩ := Int.dvd_of_emod_eq_zero h
  have hcast : ((entry k T c.1 c.2.2 (idx i) (idx l) : ℤ) : ZMod q) =
      ∑ j : Coord 7 k, (if inCut k c.1 (idx j) then 0 else
        (T (idx i) (idx j) : ZMod q) * (certR k c.1 c.2.2 (idx j) (idx l) : ZMod q)) := by
    rw [entry, sum_range_coord, Int.cast_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    split_ifs <;> simp
  have hz := congrArg (fun z : ℤ ↦ (z : ZMod q)) ht
  simp only [Int.cast_sub, Int.cast_mul, hp, zero_mul] at hz
  rw [← hcast, sub_eq_zero.mp hz]
  by_cases hil : i = l
  · simp [hil]
  · simp [hil, idx_injective.ne hil]

/-- The mask of a set of parties: the sum of `2 ^ i` over its members. -/
def maskOf (A : Finset (Fin 7)) : ℕ := ∑ i ∈ A.map Fin.valEmbedding, 2 ^ i

lemma testBit_maskOf (A : Finset (Fin 7)) (i : Fin 7) :
    (maskOf A).testBit i.1 = true ↔ i ∈ A := by
  rw [← Nat.mem_bitIndices, ← List.mem_toFinset, maskOf, Finset.toFinset_bitIndices_sum_two_pow]
  simp [Fin.val_inj]

lemma maskOf_lt (A : Finset (Fin 7)) : maskOf A < 128 := by
  calc maskOf A ≤ ∑ i ∈ Finset.range 7, 2 ^ i := by
        refine Finset.sum_le_sum_of_subset fun x hx ↦ ?_
        obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hx
        simp [a.2]
    _ < 128 := by decide

lemma popcount7_maskOf (A : Finset (Fin 7)) : popcount7 (maskOf A) = A.card := by
  have hnd : ((List.range 7).filter fun i ↦ (maskOf A).testBit i).Nodup :=
    List.nodup_range.filter _
  rw [popcount7, ← List.toFinset_card_of_nodup hnd, List.toFinset_filter, List.toFinset_range,
    ← Finset.card_map Fin.valEmbedding]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_map, Fin.valEmbedding_apply]
  constructor
  · rintro ⟨hx, hb⟩
    exact ⟨⟨x, hx⟩, (testBit_maskOf A ⟨x, hx⟩).mp hb, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.2, (testBit_maskOf A a).mpr ha⟩

lemma inCut_maskOf (A : Finset (Fin 7)) (p : Coord 7 k) :
    inCut k (maskOf A) (idx p) = true ↔ p.1 ∈ A := by
  rw [inCut, idx_div]
  exact testBit_maskOf A p.1

omit [NeZero q] in
/-- **Every set of three parties passes the cut condition**, given checked certificates. -/
theorem cutInj_all_of_certs (p : ℕ) (T : ℕ → ℕ → ℤ) (certs : List (ℕ × ℤ × List ℤ))
    (hT : ∀ i < 7 * k, ∀ j < 7 * k, T i j = T j i)
    (hok : certs.all (certOK k p T) = true)
    (hmask : certs.map Prod.fst = (List.range 128).filter fun m ↦ popcount7 m = 3)
    (hp : ((p : ℤ) : ZMod q) = 0) (hd : ∀ c ∈ certs, IsUnit ((c.2.1 : ℤ) : ZMod q)) :
    ∀ A : Finset (Fin 7), A.card = 7 / 2 →
      CutInj (graphU (q := q) k T + (graphU (q := q) k T)ᵀ) A := by
  intro A hA
  have hm : maskOf A ∈ certs.map Prod.fst := by
    rw [hmask, List.mem_filter, List.mem_range]
    exact ⟨maskOf_lt A, by simpa [popcount7_maskOf] using hA⟩
  obtain ⟨c, hc, hcm⟩ := List.mem_map.mp hm
  have hok' : certOK k p T c = true := List.all_eq_true.mp hok c hc
  refine cutInj_of_inverse _ A (fun j l ↦ (certR k c.1 c.2.2 (idx j) (idx l) : ZMod q)) _
    (hd c hc) fun i hi l hl ↦ ?_
  rw [← certOK_sum hp hok' i l (by rw [hcm]; exact (inCut_maskOf A i).mpr hi)
    (by rw [hcm]; exact (inCut_maskOf A l).mpr hl)]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  by_cases hj : j.1 ∈ A
  · simp [hj, hcm, (inCut_maskOf A j).mpr hj]
  · have hb : inCut k c.1 (idx j) = false := by
      rw [hcm]
      exact Bool.eq_false_iff.mpr (mt (inCut_maskOf A j).mp hj)
    rw [if_neg hj, hb, if_neg Bool.false_ne_true, graphU_add T hT i j fun h ↦ hj (h ▸ hi)]

end AME7
