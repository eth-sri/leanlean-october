/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Tactic
public import ThreeSumApsp.Util.RamArith
public import PaperStatements
public import ThreeSumApsp.Lang.Lib.Seg

/-!
# Reading the trusted layout

Matrices are written row by row (`rowMajor`), and an input is a concatenation of lists.  This file
says which number is in which cell (`getD_rowMajor`, `seg_memOf`, `matAt_of_seg`).
-/

public section

namespace Light

open ThreeSumApsp.WordRam

private theorem rowMajor_succ {n m} A :
    rowMajor A = (List.finRange m).map (A 0) ++ rowMajor fun i : Fin n => A i.succ := by
  simp [rowMajor, List.finRange_succ, List.flatMap_map]

theorem length_rowMajor : ∀ {n m } (A : Fin n → Fin m → ℤ), (rowMajor A).length = n * m
  | 0, m, A => by simp [rowMajor]
  | n + 1, m, A => by
    rw [rowMajor_succ, List.length_append, length_rowMajor, List.length_map, List.length_finRange]
    ring

/-- The entry `(i, j)` of an `n × m` matrix is at place `i m + j`. -/
theorem getD_rowMajor : ∀ {n m } (A ) (i : Fin n) (j : Fin m),
    (rowMajor A).getD (i * m + j) 0 = A i j
  | 0, _, _, i, _ => i.elim0
  | n + 1, m, A, i, j => by
    rw [rowMajor_succ]
    refine Fin.cases ?_ (fun i' => ?_) i
    · grind
    · rw [List.getD_append_right _ _ _ _ (by ram_arith)]
      have : (i'.succ : ℕ) * m + (j : ℕ) - ((List.finRange m).map (A 0)).length =
          (i' : ℕ) * m + (j : ℕ) := by
        ram_arith [Nat.add_mul]
      rw [this]
      exact getD_rowMajor _ i' j

/-- A cell in the first part of a concatenation. -/
theorem memOf_append_left {l₁} l₂ {a} (h : a < l₁.length) :
    memOf (l₁ ++ l₂) a = memOf l₁ a := by
  grind [memOf]

/-- A cell after the first part of a concatenation. -/
theorem memOf_append_right l₁ l₂ a :
    memOf (l₁ ++ l₂) (l₁.length + a) = memOf l₂ a := by
  grind [memOf]

/-- A part of a concatenation is a segment of the memory. -/
theorem seg_memOf l₁ l l₂ : Seg (memOf (l₁ ++ l ++ l₂)) l₁.length l := by
  intro i hi
  rw [List.append_assoc, memOf_append_right, memOf_append_left _ hi]
  exact List.getD_eq_getElem _ _ hi

/-- The first of two lists after the size. -/
def seg_first n l₁ l₂ := by
  simpa using seg_memOf [n] l₁ l₂

/-- The second of two lists after the size. -/
theorem seg_second n l₁ l₂ :
    Seg (memOf (n :: l₁ ++ l₂)) (1 + l₁.length) l₂ := by
  have := seg_memOf (n :: l₁) l₂ []
  simpa [Nat.add_comm] using this

/-- A square matrix written row by row: the two definitions agree. -/
theorem rowByRow_eq {n} (w : Fin n → Fin n → ℤ) : EndStatement.rowByRow w = rowMajor w := by
  simp [EndStatement.rowByRow, rowMajor, List.ofFn_eq_map, List.flatMap_def]

end Light
