/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.PolynomialPredicates
import CCDN.Plane.IntegralAffineLine
import CCDN.Surface.DirectionSum
import CCDN.Surface.LineDirections
import CCDN.Surface.NonlinearCount
import CCDN.Surface.ParallelLines

/-! Finite families of rational affine lines on a surface. Grouping
lines by their projective direction combines the primitive spacing bound
with the uniform reciprocal-height sum. -/

namespace CCDN
open MvPolynomial

/-- Weighted finite sums with a uniform bound on the cardinality of each
fiber. No injectivity of the indexing map is required. -/
theorem sum_comp_le_fiber_card_mul {α β : Type*} [DecidableEq β]
    (s : Finset α) (p : α → β) (w : β → ℝ) (M : ℝ)
    (hw : ∀ q ∈ s.image p, 0 ≤ w q)
    (hfiber : ∀ q ∈ s.image p, ((s.filter (fun x => p x = q)).card : ℝ) ≤ M) :
    ∑ x ∈ s, w (p x) ≤ M * ∑ q ∈ s.image p, w q := by
  calc
    _ = ∑ q ∈ s.image p, ∑ x ∈ s.filter (fun x => p x = q), w (p x) :=
      (Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem p hx) _).symm
    _ ≤ ∑ q ∈ s.image p, M * w q := by
      apply Finset.sum_le_sum
      intro q hq
      calc
        _ = ∑ _x ∈ s.filter (fun x => p x = q), w q :=
          Finset.sum_congr rfl (fun x hx => by grind)
        _ = ((s.filter (fun x => p x = q)).card : ℝ) * w q := by simp
        _ ≤ M * w q := mul_le_mul_of_nonneg_right (hfiber q hq) (hw q hq)
    _ = _ := (Finset.mul_sum _ _ _).symm

