/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.CutPlaneTopology

/-! The complement of the nonnegative real axis is a simply connected regular domain for the
Gauss system. -/

@[expose] public section

open Set

namespace DOZZ.Proofs

/-- The slit plane obtained by removing the nonnegative real axis. -/
def gaussNegativeCutPlane : Set ℂ := {z | z.im ≠ 0 ∨ z.re < 0}

/-- The negative cut plane is open. -/
theorem gaussNegativeCutPlane_isOpen : IsOpen gaussNegativeCutPlane := by
  exact id
    (IsOpen.union (IsOpen.preimage Complex.continuous_im isOpen_compl_singleton)
      (IsOpen.preimage Complex.continuous_re isOpen_Iio))

/-- The negative cut plane avoids the two singularities of the Gauss system. -/
theorem gaussNegativeCutPlane_subset_regularPlane :
    gaussNegativeCutPlane ⊆ gaussRegularPlane := by
  intro z hz
  change z ≠ 0 ∧ z ≠ 1
  constructor <;> rintro rfl <;> norm_num [gaussNegativeCutPlane] at hz

/-- The negative cut plane is star-convex about `-1/2`. -/
theorem gaussNegativeCutPlane_starConvex : StarConvex ℝ (-1 / 2 : ℂ) gaussNegativeCutPlane := by
  change StarConvex ℝ (-1 / 2 : ℂ) {z : ℂ | z.im ≠ 0 ∨ z.re ∈ Iio 0}
  simpa only [Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_ofNat] using
    starConvex_complex_with_real_slice (convex_Iio (0 : ℝ))
      (show (-1 / 2 : ℝ) ∈ Iio 0 by norm_num)

end DOZZ.Proofs
