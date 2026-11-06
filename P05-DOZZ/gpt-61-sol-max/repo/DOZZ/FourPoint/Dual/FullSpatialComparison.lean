/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.FullSpatialComparison
public import DOZZ.FourPoint.Dual.SpatialKernel
import Mathlib.Tactic
/-! The compact conditional comparison extends to full separated spatial regions. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
namespace DOZZ.Proofs

abbrev dual_full_spatial_comparison
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (γ α₁ α₂ α₃ : ℝ) (z : ℂ) :=
  weighted_full_spatial_comparison P X Xc hX hc hm γ (dualFusionKernel γ α₁ α₂ α₃ z)
    (dual_kernel_measurable γ α₁ α₂ α₃ z) (dual_kernel_nonneg γ α₁ α₂ α₃ z)
    (dual_kernel_continuousOn γ α₁ α₂ α₃ z)

end DOZZ.Proofs
