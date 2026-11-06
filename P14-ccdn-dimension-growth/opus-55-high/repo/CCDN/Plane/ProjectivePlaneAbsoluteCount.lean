/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Height.ProjectiveZeroLocus
import CCDN.Plane.ScaledPlaneCount
import CCDN.Algebra.PrimitiveNormalization
import CCDN.ForMathlib.Log
import CCDN.Plane.ProjectivePlanePositionedCount
import CCDN.Plane.RationalPlaneAssembly

/-! An absolute d^4 B^(2/d) bound for primitive absolutely irreducible
homogeneous plane equations of degree at least two. -/

namespace CCDN
noncomputable section
open MvPolynomial

/-- The absolute constant of `projective_plane_primitive_absolute_count`. Write
`E = heightDeterminantError projectivePlaneDeterminantConstant`.

* Small coefficient height: the auxiliary degree is at most
  `d + log R + 2 exp (E + 23) d³ (1 + log H / d²) R^(2/d) / |lc|^(1/d²) + 2`
  (`projective_auxiliary_small_height_degree`), where `23 = 5 + 2 + 16` collects the
  archimedean error of `plane_rank_archimedean_error` and the remainders of the box and
  coefficient terms in `plane_auxiliary_log_degree_bound`. Positioning the leading coefficient
  costs `log H ≤ log |lc| + 14 d²` (`exists_translated_coefficient_position`), hence the factor
  `exp 14` (`scaled_positioned_height_ratio_le`). The translated radius `R = (d + 1) B`
  satisfies `R^(2/d) ≤ e² B^(2/d)`, and `d + log R + 2 ≤ 5 d³ B^(2/d)`; this gives
  `exp 2` and the leading `5` (`projective_positioned_bound_le`).
* Large coefficient height: the auxiliary degree is at least `32 d` and at most
  `32 d + 8 exp (E + 6 + T) d³ + 2 ≤ (34 + 8 exp (E + 6 + T)) d³`
  (`projective_auxiliary_large_height_degree`), where `6 = 5 + 1` and the `8 = 2 · 4` come from
  `plane_auxiliary_large_height_log_bound`, and `T = 14` is the positioning loss; hence
  `E + 20`.

Bézout multiplies either degree bound by `d`. -/
def projectivePlaneAbsoluteConstant : ℝ :=
  5 + 2 * Real.exp (heightDeterminantError projectivePlaneDeterminantConstant + 23) *
      Real.exp 14 * Real.exp 2 +
    (34 + 8 * Real.exp (heightDeterminantError projectivePlaneDeterminantConstant + 20))

/-- The constant `projectivePlaneAbsoluteConstant` is positive. -/
lemma projectivePlaneAbsoluteConstant_pos : 0 < projectivePlaneAbsoluteConstant := by
  unfold projectivePlaneAbsoluteConstant
  positivity

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {d : ℕ} {B : ℝ}

