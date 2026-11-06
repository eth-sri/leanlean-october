/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Tactic
public import PaperStatements
public import ThreeSumApsp.Util.Index
public import ThreeSumApsp.Util.List

/-!
# The problems for Section 3.4, read from lists of integers

A routine has its input in arrays.  Here an array is a list of integers, a matrix is stored row by
row, and a cell is read with `List.getD _ _ 0` (`entry`).  This file says which instance of Exact
Triangle, Negative Triangle, Convolution-3SUM, 3SUM or APSP such lists hold (`vecOf`, `triOf`,
`graphOf`), and what the (min,+)-product of two lists is (`minPlusEntry`, `minPlusList`).  Two
operations on matrices serve several reductions: `affL m c` replaces each entry `x` by `m x + c`,
and `subMat` cuts out a block.

An entry of the (min,+)-product is computed as a running minimum.  It is at most each of the sums
`A[i,k] + B[k,j]` (`minPlusEntry_le`) and it is one of them (`exists_minPlusEntry_eq`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## Instances -/

/-- The entry `(i, j)` of a matrix with `n` columns that is stored in the list `L`, row by row. -/
abbrev entry n (L : List ℤ) i j := L.getD (i * n + j) 0

/-- The `N` numbers in a list. -/
def vecOf N (x : List ℤ) : Fin N → ℤ := fun i => x.getD i 0

/-- The complete tripartite graph with `n` vertices per part whose three weight matrices are in
three lists, row by row: the weight of `(a, b)` at `a n + b` of the first, of `(b, c)` at `b n + c`
of the second, of `(a, c)` at `a n + c` of the third. -/
def triOf n (AB BC AC : List ℤ) : TriangleInstance ℤ n where
  wAB a b := AB.getD (a * n + b) 0
  wBC b c := BC.getD (b * n + c) 0
  wAC a c := AC.getD (a * n + c) 0

/-- The weight matrix of a directed graph on `n` vertices: the weight of the edge `(i, j)` is in
cell `i n + j` of `w` if cell `i n + j` of `adj` holds 1, and there is no edge otherwise. -/
def graphOf n (adj w : List ℤ) : Fin n → Fin n → WithTop ℤ := fun i j =>
  if adj.getD (i * n + j) 0 = 1 then (w.getD (i * n + j) 0 : ℤ) else ⊤

/-! ## Operations on matrices -/

/-- The list of the numbers `m x + c`. -/
def affL m c (l : List ℤ) := l.map fun x => m * x + c

/-- The list of the numbers `m x + c` is as long as the list of the `x`. -/
@[simp] theorem length_affL m c l : (affL m c l).length = l.length := by
  simp [affL]

/-! ## The (min,+)-product -/

/-- The smallest of `A[i,k] + B[k,j]` over `k < n`, by one pass, for `n ≥ 1`. -/
def minPlusEntry n A B i j :=
  (List.range (n - 1)).foldl
    (fun acc k => min acc (entry n A i (k + 1) + entry n B (k + 1) j))
    (entry n A i 0 + entry n B 0 j)

/-- The (min,+)-product of two `n × n` matrices, row by row. -/
def minPlusList n A B :=
  (List.range (n * n)).map fun q => minPlusEntry n A B (q / n) (q % n)

/-- The (min,+)-product has `n²` entries. -/
theorem length_minPlusList n A B : (minPlusList n A B).length = n * n := by
  simp [minPlusList]

/-- An entry of the product is at most each of the sums. -/
theorem minPlusEntry_le n A B i j {k} (hk : k < n) :
    minPlusEntry n A B i j ≤ entry n A i k + entry n B k j :=
  List.foldl_min_le (fun k => entry n A i k + entry n B k j) (n - 1) (by omega)

/-- An entry of the product is one of the sums. -/
theorem exists_minPlusEntry_eq {n} (hn : 1 ≤ n) A B i j :
    ∃ k < n, minPlusEntry n A B i j = entry n A i k + entry n B k j := by
  obtain ⟨k, hk, he⟩ :=
    List.exists_foldl_min_eq (fun k => entry n A i k + entry n B k j) (n - 1)
  exact ⟨k, by omega, he⟩

/-- The entries of the product of two matrices with entries of absolute value at most `U` have
absolute value at most `2U`. -/
theorem abs_minPlusEntry_le {n} (hn : 1 ≤ n) {A B} {U} (hU : 0 ≤ U)
    (hA : AbsLe A U) (hB : AbsLe B U) i j : |minPlusEntry n A B i j| ≤ 2 * U := by
  obtain ⟨k, -, he⟩ := exists_minPlusEntry_eq hn A B i j
  have  := AbsLe.abs_getD_le hU hA (i * n + k)
  have  := AbsLe.abs_getD_le hU hB (k * n + j)
  rw [he]
  exact (abs_add_le _ _).trans (by linarith)

/-- The entry `(i, j)` of the product stands at the place `i n + j`. -/
theorem entry_minPlusList {n} A B {i j} (hi : i < n) (hj : j < n) :
    entry n (minPlusList n A B) i j = minPlusEntry n A B i j := by
  rw [entry, minPlusList, List.getD_map_range _ (Nat.mul_add_lt_mul hi hj),
    Nat.mul_add_div_of_lt hj,
    Nat.mul_add_mod_of_lt hj]

end ThreeSumApsp.Spec
