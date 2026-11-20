/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.Planar.DifferenceIntegrable
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import DOZZ.Hypergeom.Planar.TaylorScale

/-! Rotation and scaling of the first-order-subtracted difference integral. -/

@[expose] public section

open MeasureTheory
open scoped Topology

namespace DOZZ.Proofs

/-- The uncorrected difference has the same dilation degree. -/
theorem planarDifferenceKernel_integral_scale_norm (k β : ℝ)
    (hk : 0 < k) (hβ : k < β) (hβ₂ : β < 2) (z : ℂ) :
    (∫ u : ℂ, DOZZ.planarDifferenceKernel k β z u) =
      ‖z‖ ^ (2 + k - β) * (∫ u : ℂ, DOZZ.planarDifferenceKernel k β 1 u) := by
  rw [show 2 + k - β = k - β + 2 by ring]
  refine planar_integral_homogeneous _ _ (by linarith) (fun u => by simp [DOZZ.planarDifferenceKernel]) ?_ z
  intro z hz u
  simpa only [DOZZ.planarDifferenceKernel, mul_one, zero_mul, add_zero] using
    planar_power_kernel_mul k β 0 z 1 u hz

end DOZZ.Proofs
