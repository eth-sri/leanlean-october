/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Tactic
public import ThreeSumApsp.Util.Asymptotics.PowLittleO
public import Mathlib.Analysis.Complex.ExponentialBounds
public import ThreeSumApsp.Util.RamArith
public import PaperStatements
public import ThreeSumApsp.Spec.Sec3.Problems
public import ThreeSumApsp.Util.BinaryPrefixes

/-!
# Negative Triangle from Exact Triangle, on lists of integers

For Theorem 21(b), after [VW13, Proposition 3.4]: whether a triangle has negative weight is
expressed by O(log U) equations between binary prefixes of the shifted weights.

* The weights in `[-U, U]` are shifted to the natural numbers `x = w(a,b) + U`, `y = w(b,c) + U`,
  `v = 2U - w(a,c)`, so that a triangle is negative exactly if `x + y < v`.  The routine computes
  the prefixes `⌊z/2^ℓ⌋` (`prefQ`) of all the numbers `2x`, `2y`, `2v`, which are at most `6U`, at
  once (`negStart`, `bounds_of_mem_negStart`, `zipWith_shiftQ`, `map_shiftR`).
* For each level `ℓ` and for `e = 2` and `e = 3` the reduction makes the instance of Exact Triangle
  with the weights `⌊2x/2^ℓ⌋`, `⌊2y/2^ℓ⌋` and `e - ⌊2v/2^ℓ⌋` (`negThird`, `triOf_level`).  There is
  a negative triangle if and only if one of these instances, at a level `ℓ < L` where `3U < 2^L`,
  has a zero triangle (`hasNegativeTriangle_iff_exists_level`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## The instances of the levels -/

/-- At the top level the prefixes are zero. -/
theorem map_prefQ_start {L} {Z} (h : ∀ z ∈ Z, 0 ≤ z ∧ z < 2 ^ L) :
    Z.map (prefQ L) = affL 0 0 Z :=
  List.map_congr_left fun z hz => by simp [prefQ_start (h z hz).1 (h z hz).2]

section

variable {n U : ℕ} {AB BC AC : List ℤ}

end

end ThreeSumApsp.Spec
