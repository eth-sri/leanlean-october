module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

/-!
The universal coefficient Gram matrix of mixed products of two uniformly
overlapping complex frames. The native-frame-to-matrix correspondence remains a
separate obligation. This module proves the whole fixed matrix is positive,
including every coefficient vector, rather than testing one representative.
-/

@[expose] public section

namespace Glennie.UniformMixedGram
noncomputable section

def gramEntry (i j k l : Fin 3) : ℝ :=
  if i = k then (if j = l then 2 / 9 else 1 / 18)
  else (if j = l then 1 / 18 else -1 / 36)
variable (a : Fin 3 → Fin 3 → ℝ)
include a in

def quadratic  : ℝ :=
  ∑ i, ∑ j, ∑ k, ∑ l, a i j * gramEntry i j k l * a k l
include a in

def squares  : ℝ := ∑ i, ∑ j, (a i j) ^ 2
include a in
def rows  (i : Fin 3) : ℝ := ∑ j, a i j
include a in
def cols  (j : Fin 3) : ℝ := ∑ i, a i j
include a in
def total  : ℝ := ∑ i, rows a i
include a in

theorem quadratic_identity  :
    36 * quadratic a = 3 * squares a + 3 * (∑ i, (rows a i) ^ 2) +
      3 * (∑ j, (cols a j) ^ 2) - (total a) ^ 2 := by
  simp [quadratic, gramEntry, squares, rows, cols, total, Fin.sum_univ_three]
  ring
include a in

theorem row_cauchy  :
    (total a) ^ 2 ≤ 3 * (∑ i, (rows a i) ^ 2) := by
  simp only [total, Fin.sum_univ_three]
  nlinarith [sq_nonneg (rows a 0 - rows a 1),
    sq_nonneg (rows a 0 - rows a 2), sq_nonneg (rows a 1 - rows a 2)]
include a in

/-- A uniform lower bound that proves all nine mixed products are independent. -/
theorem quadratic_lower_bound  :
    squares a / 12 ≤ quadratic a := by
  have hidentity := quadratic_identity a
  have hcauchy := row_cauchy a
  have hcol : 0 ≤ ∑ j, (cols a j) ^ 2 := by positivity
  linarith
include a in

theorem quadratic_eq_zero_iff  :
    quadratic a = 0 ↔ ∀ i j, a i j = 0 := by
  constructor
  · intro hzero
    have hbound := quadratic_lower_bound a
    have hsnonneg : 0 ≤ squares a := by unfold squares; positivity
    have hs : squares a = 0 := by linarith
    intro i j
    have hrow : (∑ l, (a i l) ^ 2) ≤ squares a := by
      exact Finset.single_le_sum (s := Finset.univ)
        (f := fun k : Fin 3 => ∑ l, (a k l) ^ 2)
        (by intro k hk; positivity) (Finset.mem_univ i)
    have hentry : (a i j) ^ 2 ≤ ∑ l, (a i l) ^ 2 := by
      exact Finset.single_le_sum (s := Finset.univ)
        (f := fun l : Fin 3 => (a i l) ^ 2)
        (by intro l hl; positivity) (Finset.mem_univ j)
    have heq : (a i j) ^ 2 = 0 := by nlinarith [sq_nonneg (a i j)]
    exact sq_eq_zero_iff.mp heq
  · intro h
    simp [quadratic, h]

end
end Glennie.UniformMixedGram
