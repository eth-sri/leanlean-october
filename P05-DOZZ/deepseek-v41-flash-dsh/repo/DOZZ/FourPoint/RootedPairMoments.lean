/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.TwoRootedDomination
public import DOZZ.GMC.SharpMoments.SeibergWeight

/-! The positive Taylor square as an exact two-root integral, preserving both density factors. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The positive absolute kernel is measurable, with its prescribed values at the roots. -/
theorem gammaHalf_absolute_kernel_measurable (γ α₁ α₂ α₃ : ℝ) (z : ℂ) :
    Measurable (fun x => ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x / ‖x - z‖)) := by
  apply ENNReal.measurable_ofReal.comp
  have hxz : Measurable (fun x : ℂ => ‖x - z‖) := (measurable_id.sub_const z).norm
  exact (((hxz.pow_const _).mul ((measurable_const.max measurable_norm).pow_const _)).div
    ((measurable_norm.pow_const _).mul (((measurable_id.sub_const 1).norm).pow_const _))).div hxz

/-- The exact Coulomb mass is a measurable functional on all measures; no clipping is used. -/
theorem coulombMass_measure_measurable {N : ℕ} (γ : ℝ)
    (α : Fin N → ℝ) (z : Fin N → ℂ) (αinf : ℝ) :
    Measurable (fun μ : Measure ℂ => coulombMass γ μ α z αinf) :=
  Measure.measurable_lintegral (measurable_coulombWeight γ α z αinf)

end DOZZ.Proofs
