/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.Planar.DifferenceScale
public import DOZZ.Hypergeom.Planar.TaylorDiscreteLaplacian
public import DOZZ.Hypergeom.Planar.RieszConvolution
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! A dominated discrete-Laplacian limit for the difference parent integral. -/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace DOZZ.Proofs

/-- The four-direction discrete Laplacian of the first-order-subtracted difference kernel. -/
noncomputable def planarDifferenceDiscreteQuotient (k β : ℝ) (t : ℝ) (u : ℂ) : ℝ :=
  planarDiscreteLaplacian (fun z => DOZZ.planarDifferenceKernel k β z u) t 1

/-- The difference quotient is the positive radial Laplacian kernel after cancellation. -/
theorem planarDifferenceDiscreteQuotient_eq_kernel (k β : ℝ) (t : ℝ)
    (u : ℂ) :
    planarDifferenceDiscreteQuotient k β t u =
      ‖u‖ ^ (-β) * normPowerDiscreteLaplacian k t (u - 1) := by
  unfold planarDifferenceDiscreteQuotient planarDiscreteLaplacian DOZZ.planarDifferenceKernel normPowerDiscreteLaplacian
  simp only [sub_add_eq_sub_sub, sub_sub_eq_add_sub, add_sub_right_comm u, Real.rpow_neg (norm_nonneg u)]
  ring

end DOZZ.Proofs
