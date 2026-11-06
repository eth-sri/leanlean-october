/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Statements
import CCDN.Curve.AffineCurveCount
import CCDN.Surface.AuxiliaryExponent

/-! Counting the nonlinear components of a surface section using their
total Hilbert degree and the affine curve counting theorem. -/

namespace CCDN
section

/-- The number of integral points of height at most `B` on a finite union of sets is at most
the sum of the numbers of such points on the individual sets. -/
theorem count_biUnion_finset_le {n : ℕ} {ι : Type*}
    (s : Finset ι) (X : ι → Set (RatPoint n)) (B : ℝ) :
    count (⋃ i ∈ s, X i) B ≤ ∑ i ∈ s, count (X i) B := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [count, integralPoints]
  | @insert i s hi ih =>
    simpa [Finset.set_biUnion_insert, Finset.sum_insert hi] using
      (count_union_le (X i) (⋃ j ∈ s, X j) B).trans (Nat.add_le_add_left ih _)

