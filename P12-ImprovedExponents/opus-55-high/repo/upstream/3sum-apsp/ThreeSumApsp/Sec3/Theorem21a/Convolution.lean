/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import PaperStatements

/-!
# Theorem 21(a): Convolution-3SUM reduces to Exact Triangle

[VW13, Theorem 4.3] in the form needed for Theorem 21(a): Convolution-3SUM on `N < t²`
numbers becomes `2t` instances of Exact Triangle on `t` vertices per part.  In instance `s` the
triangle `(a, b, c)` stands for the pair `i = at + b`, `j = ct + s - b` (`convTemplate`).  Every
solution is such a triangle (`exists_hasZeroTriangle`), and a zero triangle is a solution, because
an index out of range gives a weight so large that the sum is positive
(`convolution3SUM_of_isZeroTriangle`).  Together: `convolution3SUM_iff`, and with `t = ⌊√N⌋ + 1`,
`theorem_21a_convolution_to_exact`.
-/


namespace ThreeSumApsp

namespace Theorem21

/-- Instance `s` of the reduction from Convolution-3SUM.  The triangle `(a, b, c)` stands for the
pair `i = a t + b`, `j = c t + s - b`, for which `i + j = (a + c) t + s`: the edge `(a, b)` carries
`x_i`, the edge `(b, c)` carries `x_j`, and the edge `(a, c)` carries `-x_{i+j}`.  An edge whose
index is out of range gets the filler weight. -/
def convTemplate (t N s : ℕ) : TriangleTemplate t N where
  eAB a b := if h : a.val * t + b.val < N then some (false, ⟨a.val * t + b.val, h⟩) else none
  eBC b c :=
    if h : b.val ≤ c.val * t + s ∧ c.val * t + s - b.val < N then
      some (false, ⟨c.val * t + s - b.val, h.2⟩)
    else none
  eAC a c :=
    if h : (a.val + c.val) * t + s < N then some (true, ⟨(a.val + c.val) * t + s, h⟩) else none

variable {N t s : ℕ} {x : Fin N → ℤ} {fill : ℤ}

/-- The weight of the edge `(a, b)`. -/
theorem convTemplate_AB (a b : Fin t) :
    templateWeight x fill ((convTemplate t N s).eAB a b)
      = if h : a.val * t + b.val < N then x ⟨a.val * t + b.val, h⟩ else fill := by
  simp [convTemplate]
  aesop

/-- The weight of the edge `(b, c)`. -/
theorem convTemplate_BC (b c : Fin t) :
    templateWeight x fill ((convTemplate t N s).eBC b c)
      = if h : b.val ≤ c.val * t + s ∧ c.val * t + s - b.val < N then
          x ⟨c.val * t + s - b.val, h.2⟩ else fill := by
  simp [convTemplate]
  aesop

/-- The weight of the edge `(a, c)`. -/
theorem convTemplate_AC (a c : Fin t) :
    templateWeight x fill ((convTemplate t N s).eAC a c)
      = if h : (a.val + c.val) * t + s < N then -x ⟨(a.val + c.val) * t + s, h⟩ else fill := by
  simp [convTemplate]
  aesop

/-- A solution `(i, j)` is the triangle `(⌊i/t⌋, i mod t, ⌊j/t⌋)` of the instance
`s = (j mod t) + (i mod t)`. -/
theorem exists_hasZeroTriangle (hNt : N < t * t)
    {i j : Fin N} (hij : i.val + j.val < N) (h : x i + x j = x ⟨i.val + j.val, hij⟩) :
    ∃ s < 2 * t, ((convTemplate t N s).instantiate x fill).HasZeroTriangle := by
  have ht : 0 < t := by grind
  have hit := Nat.mod_lt i.val ht
  have hjt := j.val.mod_lt ht
  have hj := j.val.div_add_mod' t
  -- The three indices are `i`, `j` and `i + j`, so they are in range.
  have hAB := i.val.div_add_mod' t
  refine ⟨j.val % t + i.val % t, by omega, ⟨i.val / t, Nat.div_lt_of_lt_mul (i.isLt.trans hNt)⟩,
    ⟨i.val % t, hit⟩, ⟨j.val / t, Nat.div_lt_of_lt_mul (j.isLt.trans hNt)⟩, ?_⟩
  simp [TriangleInstance.IsZeroTriangle, TriangleInstance.S, TriangleTemplate.instantiate,
    convTemplate_AB, convTemplate_BC, convTemplate_AC]
  grind

variable {U : ℤ}

/-- With the filler `2U + 1`, every weight is at least `-U`. -/
theorem neg_le_templateWeight (hU : 0 ≤ U)
    (hx : ∀ i, |x i| ≤ U) (o : Option (Bool × Fin N)) : -U ≤ templateWeight x (2 * U + 1) o := by
  rcases o with _ | ⟨_ | _, i⟩ <;> simp only [templateWeight]
  · omega
  · grind
  grind

/-- A zero triangle of an instance with the filler `2U + 1` is a solution. -/
theorem convolution3SUM_of_isZeroTriangle (hU : 0 ≤ U)
    (hx : ∀ i, |x i| ≤ U) {a b c : Fin t}
    (h : ((convTemplate t N s).instantiate x (2 * U + 1)).IsZeroTriangle a b c) :
    Convolution3SUM x := by
  simp [TriangleInstance.IsZeroTriangle, TriangleInstance.S, TriangleTemplate.instantiate] at h
  have hgeAB := neg_le_templateWeight hU hx ((convTemplate t N s).eAB a b)
  have hgeBC := neg_le_templateWeight hU hx ((convTemplate t N s).eBC b c)
  have hgeAC := neg_le_templateWeight hU hx ((convTemplate t N s).eAC a c)
  -- One filler `2U + 1` and two weights that are at least `-U` have a positive sum, so the three
  -- indices are in range.
  have hAB : a.val * t + b.val < N := by
    by_contra hout
    rw [convTemplate_AB, dif_neg hout] at h
    omega
  have hBC : b.val ≤ c.val * t + s ∧ c.val * t + s - b.val < N := by
    by_contra hout
    rw [convTemplate_BC, dif_neg hout] at h
    omega
  have hAC : (a.val + c.val) * t + s < N := by
    by_contra hout
    rw [convTemplate_AC, dif_neg hout] at h
    omega
  rw [convTemplate_AB, convTemplate_BC, convTemplate_AC, dif_pos hBC] at h
  -- The triangle stands for `i = at + b` and `j = ct + s - b`, and `i + j = (a + c)t + s`.
  have hsum : a.val * t + b.val + (c.val * t + s - b.val) = (a.val + c.val) * t + s := by
    grind
  refine ⟨⟨a.val * t + b.val, hAB⟩, ⟨c.val * t + s - b.val, hBC.2⟩, by simp_all, ?_⟩
  grind

/-- The reduction of [VW13, Theorem 4.3], for `N < t²` numbers of absolute value at most `U`: there
are `i`, `j` with `x_i + x_j = x_{i+j}` if and only if one of the instances `s < 2t`, with the
filler `2U + 1`, has a zero triangle. -/
theorem convolution3SUM_iff (hN : 1 ≤ N) (hNt : N < t * t)
    (hx : ∀ i, |x i| ≤ U) :
    Convolution3SUM x ↔
      ∃ s < 2 * t, ((convTemplate t N s).instantiate x (2 * U + 1)).HasZeroTriangle := by
  constructor
  · rintro ⟨i, j, hij, h⟩
    exact exists_hasZeroTriangle hNt hij h
  · rintro ⟨s, -, a, b, c, h⟩
    exact convolution3SUM_of_isZeroTriangle ((abs_nonneg _).trans (by tauto)) hx h
