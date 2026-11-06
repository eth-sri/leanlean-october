/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Lang.TopProcedure
import ThreeSumApsp.Programs.Tasks
import ThreeSumApsp.Spec.Sec3.Theorem21b.RepeatedSquaring

/-!
# The (min,+)-product: from a solver of the task to a program for the layout of the end statement

The (min,+)-product (Theorem 22).  `realized_minPlusProduct`: if the task `mpTask` is
solved in time T, then `EndStatement.MinPlusProduct` is solved on the word RAM within a constant
times T.

The input is n in cell 0, the first matrix from cell 1 and the second from cell 1 + n².  The product
goes to the n² cells from 1 + 2n², and the free pointer is 1 + 3n² (`minPlusInst`).  The input meets
the task's precondition (`pre_minPlusProduct`).  A solver leaves the list `minPlusList` in the
output cells, and each of its entries is a minimum as `EndStatement.MinPlusProduct` asks for: it is
attained, and it is a lower bound (`post_minPlusProduct`).
-/


namespace Light.Sec3

open ThreeSumApsp.WordRam ThreeSumApsp.Spec

variable (x : Bounded EndStatement.MinPlusProduct)

/-- The input: the size and the two matrices, row by row. -/
theorem input_minPlusProduct :
    (ofEnd EndStatement.MinPlusProduct).input x =
      (x.n : ℤ) :: (rowMajor x.x.1 ++ rowMajor x.x.2) := by
  simp [EndStatement.MinPlusProduct, rowByRow_eq]

/-- The input takes 1 + 2n² cells. -/
theorem length_input_minPlusProduct :
    ((ofEnd EndStatement.MinPlusProduct).input x).length = 1 + 2 * (x.n * x.n) := by
  grind [input_minPlusProduct, List.length_cons, List.length_append, length_rowMajor]

/-- The entries of the two matrices are within the bound. -/
theorem abs_le_of_mem_minPlusProduct {a : ℤ}
    (ha : a ∈ rowMajor x.x.1 ++ rowMajor x.x.2) : |a| ≤ (x.U : ℤ) :=
  by simp_all [Bounded.abs_le, EndStatement.MinPlusProduct, rowByRow_eq]

/-- The instance of the task: where the two matrices and the product stand. -/
def minPlusInst (x : Bounded EndStatement.MinPlusProduct) : mpTask.Inst :=
  ⟨x.n, x.U, 1, 1 + x.n * x.n, 1 + 2 * (x.n * x.n), rowMajor x.x.1, rowMajor x.x.2⟩

/-- The input of the end statement meets the precondition of the task. -/
theorem pre_minPlusProduct (hn : 1 ≤ x.n)
    (hU : 1 ≤ x.U) :
    mpTask.Pre (minPlusInst x) (memOf ((ofEnd EndStatement.MinPlusProduct).input x))
      (1 + 3 * (x.n * x.n)) := by
  have hA : (rowMajor x.x.1).length = x.n * x.n := length_rowMajor _
  rw [input_minPlusProduct]
  exact
  ⟨hn, hU, hA, length_rowMajor _, seg_first _ _ _, by
      have := seg_second x.n (rowMajor x.x.1) (rowMajor x.x.2)
      aesop, fun a (ha : a ∈ rowMajor x.x.1) => abs_le_of_mem_minPlusProduct x (by simp_all), fun a (ha : a ∈ rowMajor x.x.2) => abs_le_of_mem_minPlusProduct x (by simp_all), by grind [minPlusInst], by grind [minPlusInst], by grind [minPlusInst], Or.inl (by grind [minPlusInst]), Or.inl (by grind [minPlusInst])⟩

/-- What the task leaves in the output cells is the (min,+)-product as the end statement asks for
it. -/
theorem post_minPlusProduct (r : ℤ) (μ' : ℕ → ℤ)
    (hn : 1 ≤ x.n)
    (h : mpTask.Post (minPlusInst x) (memOf ((ofEnd EndStatement.MinPlusProduct).input x))
      (1 + 3 * (x.n * x.n)) r μ') :
    (ofEnd EndStatement.MinPlusProduct).IsAnswer x (verdictOf false 1) fun i =>
      μ' (((ofEnd EndStatement.MinPlusProduct).input x).length + i) := by
  have hseg : Seg μ' (1 + 2 * (x.n * x.n)) (minPlusList x.n (rowMajor x.x.1) (rowMajor x.x.2)) :=
    h.1
  refine ⟨by tauto, fun i j => ?_⟩
  -- the output cell of the pair (i, j) holds the entry of the list
  have hcell : μ' (((ofEnd EndStatement.MinPlusProduct).input x).length +
      (i * x.n + j)) = minPlusEntry x.n (rowMajor x.x.1) (rowMajor x.x.2) i j := by
    rw [length_input_minPlusProduct,
      hseg.getD (by simp_all [length_minPlusList, Nat.mul_add_lt_mul])]
    exact entry_minPlusList _ _ i.isLt j.isLt
  obtain ⟨l, hl, hmin⟩ := exists_minPlusEntry_eq hn (rowMajor x.x.1) (rowMajor x.x.2) i j
  refine ⟨⟨⟨l, hl⟩, hcell.trans ?_⟩, fun l' => hcell.le.trans ?_⟩
  · -- the entry is attained
    grind [getD_rowMajor]
  · -- the entry is a lower bound
    have := minPlusEntry_le x.n (rowMajor x.x.1) (rowMajor x.x.2) i j l'.isLt
    grind [getD_rowMajor]

/-- What connects the (min,+)-product in the layout of the end statement with the task.  The program
always accepts: the answer is in the output cells. -/
def wrapMinPlus : Wrap EndStatement.MinPlusProduct mpTask false where
  args := [v 1, v 2, k 1, k 1 +' v 3, k 1 +' k 2 *' v 3, k 1 +' k 3 *' v 3]
  inst := minPlusInst
  fr x := 1 + 3 * (x.n * x.n)
  size_eq _ := rfl
  bound_eq _ := rfl
  fr_pos x := by omega
  fr_le x := by omega
  vals x σ hn hU hnn := by simp [mpTask, minPlusInst, hn, hU, hnn]
  safe x lim σ _ _ hnn hw := safe_fourAddresses (by omega) hnn hw
  zero x hn _ := ⟨⟨fun _ => trivial, fun _ => rfl⟩, fun i => absurd i.isLt (by omega)⟩
  pre := pre_minPlusProduct
  post := post_minPlusProduct

/-- **The (min,+)-product**: if the task is solved in time T, then the product is computed on the
word RAM within a constant times T. -/
theorem realized_minPlusProduct (T : ℕ → ℝ → ℝ) (h : SolvedIn mpTask T) :
    Realized EndStatement.MinPlusProduct T :=
  wrapMinPlus.realized h
