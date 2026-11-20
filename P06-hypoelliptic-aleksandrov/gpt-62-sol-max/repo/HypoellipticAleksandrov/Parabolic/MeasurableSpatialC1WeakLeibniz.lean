module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialCoordinateShiftCarrierGeometry
public import HypoellipticAleksandrov.Parabolic.SpatialTranslationWeakDerivatives
public import HypoellipticAleksandrov.Parabolic.WeakDerivatives
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import HypoellipticAleksandrov.Parabolic.LocalCompactSupportIntegrationByParts
public import Mathlib.MeasureTheory.Integral.Prod
public import HypoellipticAleksandrov.Parabolic.TimeVelocitySmoothCompactPlateau
public import HypoellipticAleksandrov.Parabolic.WeakJetProduct
public import HypoellipticAleksandrov.Parabolic.WeakDerivativesCompactGlobalization
public import HypoellipticAleksandrov.Parabolic.WeakDerivativeSpacetimeMollification
public import HypoellipticAleksandrov.Parabolic.SpacetimeMollifierL2
public import HypoellipticAleksandrov.Analysis.L2ProductConvergence
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import HypoellipticAleksandrov.Analysis.BoundedMultiplierLp
import HypoellipticAleksandrov.Parabolic.LocalWeakTimeProduct

/-!
# Weak Leibniz rule for measurable-time, spatially smooth multipliers

This module proves the quantitative weak velocity product rule for bounded
jointly measurable scalar multipliers whose fixed-time spatial slices are
`C¹`.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Filter Function MeasureTheory Set Topology
open scoped ENNReal Topology
open SpacetimeMollifier

/-- A scalar that is `C¹` on an open time--velocity carrier has its literal
velocity derivative as its raw weak velocity derivative there. -/
theorem contDiffOn_one_hasWeakVelocityPartialDerivOn
    {d : ℕ} (U : Set (TimeVelocity d)) (hU : IsOpen U)
    (i : Fin d)
    (q : TimeVelocity d → ℝ) (hq : ContDiffOn ℝ 1 q U) :
    HasWeakVelocityPartialDerivOn U i q
      (fun z => velocityGradient q z i) :=   contDiffOn_one_hasWeakFDerivApplyOn hU (0, Pi.single i 1) hq

/-- A bounded `C¹` multiplier obeys the weak velocity Leibniz rule on an
arbitrary open carrier, with sharp componentwise `L²` bounds. -/
theorem velocityC1_mul_hasWeakVelocityPartialDerivOn_memLp_eLpNorm_le
    {d : ℕ} {U : Set (TimeVelocity d)} (hU : IsOpen U)
    (i : Fin d)
    (Bq Bdi : ℝ) (hBq : 0 ≤ Bq) (hBdi : 0 ≤ Bdi)
    (q : TimeVelocity d → ℝ) (hqC1 : ContDiffOn ℝ 1 q U)
    (hqBound : ∀ z ∈ U, |q z| ≤ Bq)
    (hdiBound : ∀ z ∈ U, |velocityGradient q z i| ≤ Bdi)
    (u dui : TimeVelocity d → ℝ)
    (hu : ParabolicMemLpOn U 2 u)
    (hdui : ParabolicMemLpOn U 2 dui)
    (hweak : HasWeakVelocityPartialDerivOn U i u dui) :
    AEStronglyMeasurable (fun z => velocityGradient q z i)
        (timeVelocityVolumeOn U) ∧
      ParabolicMemLpOn U 2 (fun z => q z * u z) ∧
      ParabolicMemLpOn U 2
        (fun z => q z * dui z + velocityGradient q z i * u z) ∧
      HasWeakVelocityPartialDerivOn U i
        (fun z => q z * u z)
        (fun z => q z * dui z + velocityGradient q z i * u z) ∧
      ENNReal.toReal
          (eLpNorm (fun z => q z * u z) 2 (timeVelocityVolumeOn U)) ≤
        Bq * ENNReal.toReal
          (eLpNorm u 2 (timeVelocityVolumeOn U)) ∧
      ENNReal.toReal
          (eLpNorm
            (fun z => q z * dui z + velocityGradient q z i * u z)
            2 (timeVelocityVolumeOn U)) ≤
        Bq * ENNReal.toReal
          (eLpNorm dui 2 (timeVelocityVolumeOn U)) +
        Bdi * ENNReal.toReal
          (eLpNorm u 2 (timeVelocityVolumeOn U)) :=   fderivApplyC1_mul_hasWeakFDerivApplyOn_memLp_eLpNorm_le hU (0, Pi.single i 1)
    Bq Bdi hBq hBdi q hqC1 hqBound hdiBound u dui hu hdui hweak

end HypoellipticAleksandrov.Parabolic
