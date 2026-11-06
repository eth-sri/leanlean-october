/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.Isometry
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! # Complex scaling of planar integrals -/

public section
open MeasureTheory Complex
open scoped ComplexOrder
namespace DOZZ.Proofs

/-- The planar change of variables `x = y*z`, with its exact Jacobian. -/
theorem fusion_integral_mul_complex (F : ℂ → ℂ) (z : ℂ) (hz : z ≠ 0) :
    (∫ x : ℂ, F x) = (‖z‖ ^ 2 : ℝ) * (∫ y : ℂ, F (y * z)) := by
  let r := ‖z‖
  let ξ := z / (r : ℂ)
  have hr  := norm_pos_iff.mpr hz
  have hξ : ‖ξ‖ = 1 := by
    continuity
  have hξr : ξ * (r : ℂ) = z := by
    continuity
  let c : Circle := ⟨ξ, by
    change dist ξ 0 = 1
    simpa only [dist_zero_right] using hξ⟩
  let g := fun u : ℂ => F (ξ * u)
  have hrot : (∫ u : ℂ, g u) = ∫ x : ℂ, F x := by
    exact (LinearIsometryEquiv.measurePreserving (rotation c)).integral_comp
        (rotation c).toContinuousLinearEquiv.toHomeomorph.measurableEmbedding F
  have hs : (∫ y : ℂ, g (r • y)) = (((r ^ 2)⁻¹ : ℝ) : ℂ) * (∫ u : ℂ, g u) := by
    simpa only [Complex.finrank_real_complex, Complex.real_smul] using
      Measure.integral_comp_smul_of_nonneg volume g r (hR := hr.le)
  have hpoint : (fun y : ℂ => g (r • y)) = fun y => F (y * z) := by
    funext y
    dsimp only [g]
    rw [Complex.real_smul]
    congr 1
    rw [← hξr]
    ring
  continuity

end DOZZ.Proofs
