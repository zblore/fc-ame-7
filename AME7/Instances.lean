/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import AME7.Certificate

/-!
# AME(7, q) for every odd `q`, AME(7, 4) and AME(7, 8)

Three graph states on seven parties, each AME by `graphState_isAME` and a kernel-checked
certificate for every set of three parties (`AME7.Certificate`):

* **odd `q`:** `Γ`, the complement of the 7-cycle, over `ZMod q` (Shi, Zhang, Zhao and Li 2026,
  Eq. (2)). Each certificate is an integer adjugate with `Γ[A, Aᶜ] · R = d · 1` exactly and
  `d ∈ {1, -1, 2}`, a unit modulo every odd `q`. One proof covers every odd `q`.
* **`4` and `8`:** circulant graph matrices over `GF(4)` and `GF(8)` in binary form (`k = 2, 3`
  digits over `ZMod 2`), with inverses modulo `2`. These two witnesses were found for this project
  by computer search.
-/

namespace AME7

open OpenQuantumProblem35
open scoped Matrix

/-- `Γ`, the complement of the 7-cycle: `Γ i j = 1` iff `i - j ≢ 0, ±1 (mod 7)`. -/
def gammaT (i j : ℕ) : ℤ :=
  if (i + 7 - j) % 7 = 0 ∨ (i + 7 - j) % 7 = 1 ∨ (i + 7 - j) % 7 = 6 then 0 else 1

/-- The binary table over `GF(4)`. -/
def table4 (i j : ℕ) : ℤ := ((table4Rows.getD i []).getD j 0 : ℤ)

/-- The binary table over `GF(8)`. -/
def table8 (i j : ℕ) : ℤ := ((table8Rows.getD i []).getD j 0 : ℤ)

/- The kernel checks: symmetry of the tables, the certificates, their masks and their `d`. -/

theorem gammaT_symm : ∀ i < 7 * 1, ∀ j < 7 * 1, gammaT i j = gammaT j i := by decide +kernel

theorem table4_symm : ∀ i < 7 * 2, ∀ j < 7 * 2, table4 i j = table4 j i := by decide +kernel

theorem table8_symm : ∀ i < 7 * 3, ∀ j < 7 * 3, table8 i j = table8 j i := by decide +kernel

theorem oddCerts_ok : oddCerts.all (certOK 1 0 gammaT) = true := by decide +kernel

theorem certs4_ok : certs4.all (certOK 2 2 table4) = true := by decide +kernel

theorem certs8_ok : certs8.all (certOK 3 2 table8) = true := by decide +kernel

theorem oddCerts_masks :
    oddCerts.map Prod.fst = (List.range 128).filter fun m ↦ popcount7 m = 3 := by decide +kernel

theorem certs4_masks :
    certs4.map Prod.fst = (List.range 128).filter fun m ↦ popcount7 m = 3 := by decide +kernel

theorem certs8_masks :
    certs8.map Prod.fst = (List.range 128).filter fun m ↦ popcount7 m = 3 := by decide +kernel

theorem oddCerts_dets :
    oddCerts.all (fun c ↦ decide (c.2.1 = 1 ∨ c.2.1 = -1 ∨ c.2.1 = 2)) = true := by
  decide +kernel

theorem certs4_dets : certs4.all (fun c ↦ decide (c.2.1 = 1)) = true := by decide +kernel

theorem certs8_dets : certs8.all (fun c ↦ decide (c.2.1 = 1)) = true := by decide +kernel

/- ## Odd `q` -/

variable {q : ℕ} [NeZero q]

omit [NeZero q] in
/-- `1`, `-1` and `2` are units modulo an odd `q`. -/
lemma isUnit_of_odd (hq : Odd q) {d : ℤ} (hd : d = 1 ∨ d = -1 ∨ d = 2) :
    IsUnit (d : ZMod q) := by
  have h2 : IsUnit (2 : ZMod q) := by
    simpa using (ZMod.isUnit_iff_coprime 2 q).mpr (Nat.coprime_two_left.mpr hq)
  rcases hd with rfl | rfl | rfl
  · simp
  · simp
  · simpa using h2

/-- **AME(7, q) for every odd `q`**: the graph state of `Γ` over `ZMod q`. -/
theorem odd_isAME (hq : Odd q) : IsAME (graphState (q := q) (graphU 1 gammaT)) :=
  graphState_isAME _ (cutInj_all_of_certs 0 gammaT oddCerts gammaT_symm oddCerts_ok
    oddCerts_masks (by simp) fun c hc ↦ isUnit_of_odd hq
      (of_decide_eq_true (List.all_eq_true.mp oddCerts_dets c hc)))

/-- **AME(7, q) exists for every odd `q`.** -/
theorem existsAME_odd (hq : Odd q) : ExistsAME 7 q := by
  have h : ExistsAME 7 (q ^ 1) := ⟨_, odd_isAME hq⟩
  rwa [pow_one] at h

/- ## Four and eight levels -/

/-- **AME(7, 4)**: the binary form of a graph state over `GF(4)`. -/
theorem existsAME_four : ExistsAME 7 4 :=
  ⟨_, graphState_isAME (q := 2) (k := 2) _ (cutInj_all_of_certs 2 table4 certs4 table4_symm
    certs4_ok certs4_masks (by decide) fun c hc ↦ by
      rw [of_decide_eq_true (List.all_eq_true.mp certs4_dets c hc)]
      exact isUnit_one)⟩

/-- **AME(7, 8)**: the binary form of a graph state over `GF(8)`. -/
theorem existsAME_eight : ExistsAME 7 8 :=
  ⟨_, graphState_isAME (q := 2) (k := 3) _ (cutInj_all_of_certs 2 table8 certs8 table8_symm
    certs8_ok certs8_masks (by decide) fun c hc ↦ by
      rw [of_decide_eq_true (List.all_eq_true.mp certs8_dets c hc)]
      exact isUnit_one)⟩

end AME7
