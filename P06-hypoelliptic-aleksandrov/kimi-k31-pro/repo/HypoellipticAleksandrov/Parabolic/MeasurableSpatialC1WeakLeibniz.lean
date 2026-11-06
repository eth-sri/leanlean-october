module
public import HypoellipticAleksandrov.Parabolic.LocalWeakTimeProduct

public import HypoellipticAleksandrov.Parabolic.MeasurableSpatialC1RawWeakDerivative
public import HypoellipticAleksandrov.Parabolic.TimeVelocitySmoothCompactPlateau
public import HypoellipticAleksandrov.Parabolic.WeakJetProduct
public import HypoellipticAleksandrov.Parabolic.WeakDerivativesCompactGlobalization
public import HypoellipticAleksandrov.Parabolic.WeakDerivativeSpacetimeMollification
public import HypoellipticAleksandrov.Parabolic.SpacetimeMollifierL2
public import HypoellipticAleksandrov.Analysis.L2ProductConvergence
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

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
      (fun z => velocityGradient q z i) := by
  simpa only [HasWeakDirectionalDerivOn, HasWeakVelocityPartialDerivOn, velocityGradient] using
    contDiffOn_one_hasWeakDirectionalDerivOn U hU (0, Pi.single i 1) q hq

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
          (eLpNorm u 2 (timeVelocityVolumeOn U)) := by
  have h := directionalC1_mul_hasWeakDirectionalDerivOn_memLp_eLpNorm_le hU (0, Pi.single i 1)
    Bq Bdi hBq hBdi q hqC1 hqBound hdiBound u dui hu hdui hweak
  refine ⟨?_, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩
  change AEStronglyMeasurable (fun z => fderiv ℝ q z (0, Pi.single i 1)) (timeVelocityVolumeOn U)
  exact h.1

end HypoellipticAleksandrov.Parabolic
