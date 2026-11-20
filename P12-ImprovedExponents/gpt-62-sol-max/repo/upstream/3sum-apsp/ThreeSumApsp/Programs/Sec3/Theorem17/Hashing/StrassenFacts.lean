/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec3.Theorem17.Hashing.RingOps
public import ThreeSumApsp.Spec.Sec3.Theorem17.Strassen

/-!
# Strassen's algorithm in seven uniform phases: the pure side

An entry of a matrix is a vector of `p` numbers, an element of the ring ℤ[x]/(x^p - 1), whose
product is `cconv p`; `vlinList s A B` is the list `A + s B`, which the routine vlin writes.  The
routine for Strassen's algorithm clears the four quarters of the result and then runs seven
phases.  A phase forms `S = A₁ + s_A A₂`, `T = B₁ + s_B B₂`, `M = S · T` (recursively) and adds
`s₁ M` and `s₂ M` to two quarters of the result; the signs are 1, -1 or 0.  This file has the facts
about lists that the proof about the routine uses:

* lengths (`length_vlinList`, `length_quarter`, `length_strassenList`);
* magnitudes: for operands bounded by `α` and `β`, all numbers that are formed at level `j` are
  bounded by `strassenBound p j α β = 32^j p α β` (`absLe_strassenList`);
* these invariants are preserved by the shared table of seven phases.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

/-- The bounds of the two operands add up. -/
theorem _root_.ThreeSumApsp.AbsLe.vlinList {s a b : ℤ} {A B : List ℤ} (hA : AbsLe A a)
    (hB : AbsLe B b)
    (hs : |s| ≤ 1) : AbsLe (vlinList s A B) (a + b) := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hiA : i < A.length := by simp only [Spec.vlinList, List.length_zipWith] at hi; omega
  have hiB : i < B.length := by simp only [Spec.vlinList, List.length_zipWith] at hi; omega
  simp only [Spec.vlinList, List.getElem_zipWith]
  have hsy : |s * B[i]| ≤ b := by
    rw [abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) hs).trans (hB.getElem hiB)
  exact le_trans (abs_add_le _ _) (add_le_add (hA.getElem hiA) hsy)

/-- A larger bound. -/
theorem _root_.ThreeSumApsp.AbsLe.trans_le {l : List ℤ} {a b : ℤ} (h : AbsLe l a) (hab : a ≤ b) :
    AbsLe l b := fun x hx => (h x hx).trans hab

/-- Zeros are bounded by 0. -/
theorem absLe_zeros (q : ℕ) : AbsLe (zeros q) 0 := by
  intro x hx
  simp_all

/-- A quarter of a list of 4 q numbers has q numbers. -/
theorem length_quarter {q t : ℕ} {l : List ℤ} (h : l.length = 4 * q) (ht : t < 4) :
    (quarter q t l).length = q := by
  have h1 : (t + 1) * q ≤ 4 * q := Nat.mul_le_mul_right q (by omega)
  have h2 : (t + 1) * q = t * q + q := by ring
  light_side [quarter, h]

/-- A bound for a list is a bound for its quarters. -/
theorem _root_.ThreeSumApsp.AbsLe.quarter {q t : ℕ} {l : List ℤ} {a : ℤ} (h : AbsLe l a) :
    AbsLe (quarter q t l) a :=
  fun x hx => h x (List.mem_of_mem_drop (List.mem_of_mem_take hx))

/-- A quarter of an array of 4 q numbers is an array of q numbers. -/
theorem _root_.Light.ArrayAt.quarter {μ : ℕ → ℤ} {a q t top : ℕ} {l : List ℤ} {U : ℤ}
    (h : ArrayAt μ a l (4 * q) U top) (ht : t < 4) :
    ArrayAt μ (a + t * q) (quarter q t l) q U top :=
  h.drop_take (Nat.mul_add_le_mul ht le_rfl)

/-- The list A + s B, once it stands at dst, is an array, and the bounds of A and B add up. -/
theorem _root_.Light.ArrayAt.vlinList {μ μ' : ℕ → ℤ} {a dst n top top' : ℕ} {A B : List ℤ}
    {s U V W : ℤ} (hA : ArrayAt μ a A n U top) (lenB : B.length = n) (leB : AbsLe B V)
    (hs : |s| ≤ 1) (seg : Seg μ' dst (vlinList s A B)) (hW : U + V ≤ W := by light_arith)
    (below : dst + n ≤ top' := by light_arith) : ArrayAt μ' dst (vlinList s A B) n W top' :=
  { len := length_vlinList s hA.len lenB, seg, bound := (hA.bound.vlinList leB hs).trans_le hW
    below }

/-- A product in the ring has p numbers. -/
theorem length_cconv (p : ℕ) (A B : List ℤ) : (cconv p A B).length = p := by simp [cconv]

private theorem length_fold_phases {q : ℕ} {M : PhaseRow → List ℤ} {rows : List PhaseRow}
    (hM : ∀ r ∈ rows, (M r).length = q) {L : ℕ → List ℤ} (hL : ∀ t, (L t).length = q) :
    ∀ t, ((rows.foldl (fun L r => r.accum L (M r)) L) t).length = q := by
  induction rows generalizing L with
  | nil => exact hL
  | cons r rows ih =>
    apply ih (fun s hs => hM s (List.mem_cons_of_mem _ hs))
    intro t
    simp only [PhaseRow.accum, Function.update_apply]
    split <;> (try split) <;> simp [hL, vlinList, hM r (by simp)]

/-- The product has the same length as the operands. -/
theorem length_strassenList (p : ℕ) :
    ∀ (j : ℕ) (A B : List ℤ), A.length = 4 ^ j * p → B.length = 4 ^ j * p →
      (strassenList p j A B).length = 4 ^ j * p
  | 0, A, B, _, _ => by simp [strassenList, length_cconv]
  | j + 1, A, B, hA, hB => by
    let q := 4 ^ j * p
    have hA' : A.length = 4 * q := by dsimp [q]; grind
    have hB' : B.length = 4 * q := by dsimp [q]; grind
    have hM r (hr : r ∈ phaseTable) :
        (phaseProduct (strassenList p j) q A B r).length = q := by
      have h := PhaseRow.of_mem hr
      exact length_strassenList p j _ _
        (length_vlinList _ (length_quarter hA' h.a1) (length_quarter hA' h.a2))
        (length_vlinList _ (length_quarter hB' h.b1) (length_quarter hB' h.b2))
    let C := phaseTable.foldl (fun L r => r.accum L (phaseProduct (strassenList p j) q A B r))
      (fun _ => zeros q)
    have h : ∀ t, (C t).length = q := length_fold_phases hM (fun _ => List.length_replicate)
    change (C 0 ++ C 1 ++ C 2 ++ C 3).length = _
    grind

/-- The product of a phase. -/
def phaseM (p j : ℕ) (sA : ℤ) (A1 A2 : List ℤ) (sB : ℤ) (B1 B2 : List ℤ) : List ℤ :=
  strassenList p j (vlinList sA A1 A2) (vlinList sB B1 B2)

/-- The bound on all the numbers that the routine forms at level `j`, for operands bounded by `α`
and `β`. -/
def strassenBound (p j : ℕ) (α β : ℤ) : ℤ := 32 ^ j * (p * α * β)

/-- The bound is not negative. -/
theorem strassenBound_nonneg {p j : ℕ} {α β : ℤ} (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    0 ≤ strassenBound p j α β := by
  unfold strassenBound
  positivity

/-- The bound of level j + 1 in terms of the bound of level j, for operands that are sums of two. -/
theorem strassenBound_succ (p j : ℕ) (α β : ℤ) :
    strassenBound p (j + 1) α β = 8 * strassenBound p j (2 * α) (2 * β) := by
  unfold strassenBound
  ring

/-- The bound on the entries of the product of two matrices of zeros and ones. -/
theorem strassenBound_one_one (p K : ℕ) : strassenBound p K 1 1 = ((32 ^ K * p : ℕ) : ℤ) := by
  unfold strassenBound
  simp

/-- The bound is at least the bound α for the first operand. -/
theorem le_strassenBound_left {p j : ℕ} {α β : ℤ} (hp : 1 ≤ p) (hα : 1 ≤ α) (hβ : 1 ≤ β) :
    α ≤ strassenBound p j α β := by
  have hpow : (1 : ℤ) ≤ 32 ^ j := one_le_pow₀ (by norm_num)
  have hpZ : (1 : ℤ) ≤ p := by exact_mod_cast hp
  calc α = 1 * (1 * α * 1) := by ring
    _ ≤ 32 ^ j * (p * α * β) := by gcongr

/-- The bound is at least the bound β for the second operand. -/
theorem le_strassenBound_right {p j : ℕ} {α β : ℤ} (hp : 1 ≤ p) (hα : 1 ≤ α) (hβ : 1 ≤ β) :
    β ≤ strassenBound p j α β := by
  have hpow : (1 : ℤ) ≤ 32 ^ j := one_le_pow₀ (by norm_num)
  have hpZ : (1 : ℤ) ≤ p := by exact_mod_cast hp
  calc β = 1 * (1 * 1 * β) := by ring
    _ ≤ 32 ^ j * (p * α * β) := by gcongr

/-- A product in the ring is bounded by p α β. -/
theorem absLe_cconv {p : ℕ} {A B : List ℤ} {α β : ℤ} (leA : AbsLe A α) (leB : AbsLe B β)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) : AbsLe (cconv p A B) (p * α * β) := by
  intro x hx
  rw [cconv_eq_map_convPartialSum] at hx
  obtain ⟨r, -, rfl⟩ := List.mem_map.mp hx
  have := abs_convPartialSum_le (p := p) leA leB hα hβ r p
  lia

private theorem absLe_fold_phases {m b : ℤ} {M : PhaseRow → List ℤ} {rows : List PhaseRow}
    (hM : ∀ r ∈ rows, AbsLe (M r) m) (h0 : 0 ≤ m) (hOk : ∀ r ∈ rows, r.Ok)
    {L : ℕ → List ℤ} (hL : ∀ t, AbsLe (L t) b) :
    ∀ t, AbsLe ((rows.foldl (fun L r => r.accum L (M r)) L) t) (b + rows.length * m) := by
  induction rows generalizing L b with
  | nil => simpa using hL
  | cons r rows ih =>
    have hr := hOk r (by simp)
    have hm := hM r (by simp)
    have hab t : AbsLe (r.accum L (M r) t) (b + m) := by
      simp only [PhaseRow.accum, Function.update_apply]
      split
      · exact (hL _).vlinList hm hr.s2
      split
      · exact (hL _).vlinList hm hr.s1
      exact (hL _).trans_le (by omega)
    simpa only [List.foldl_cons, List.length_cons, Nat.cast_add, Nat.cast_one,
      add_mul, one_mul, add_assoc, add_comm, add_left_comm] using
      ih (fun s hs => hM s (List.mem_cons_of_mem _ hs))
        (fun s hs => hOk s (List.mem_cons_of_mem _ hs)) hab

/-- The entries of the result of the routine, and of the products of its phases, are bounded. -/
theorem absLe_strassenList (p : ℕ) :
    ∀ (j : ℕ) (A B : List ℤ) (α β : ℤ), AbsLe A α → AbsLe B β → 0 ≤ α → 0 ≤ β →
      AbsLe (strassenList p j A B) (strassenBound p j α β)
  | 0, A, B, α, β, leA, leB, hα, hβ => by
    simp_all [strassenList, strassenBound, absLe_cconv] <;> omega
  | j + 1, A, B, α, β, leA, leB, hα, hβ => by
    let q := 4 ^ j * p
    let m := strassenBound p j (2 * α) (2 * β)
    have h0 : 0 ≤ m := strassenBound_nonneg (by omega) (by omega)
    have hM r (hr : r ∈ phaseTable) : AbsLe (phaseProduct (strassenList p j) q A B r) m := by
      have h := PhaseRow.of_mem hr
      exact absLe_strassenList p j _ _ _ _
        ((leA.quarter.vlinList leA.quarter h.sA).trans_le (by omega))
        ((leB.quarter.vlinList leB.quarter h.sB).trans_le (by omega)) (by omega) (by omega)
    have h := absLe_fold_phases hM h0 (fun _ => PhaseRow.of_mem) (fun _ => absLe_zeros q)
    have h' t := (h t).trans_le (show (0 : ℤ) + (phaseTable.length : ℤ) * m ≤ 8 * m by
      change 0 + (7 : ℤ) * m ≤ 8 * m; omega)
    rw [strassenList, strassenBound_succ]
    intro x hx
    simp only [List.mem_append] at hx
    aesop

end Light.Sec3
