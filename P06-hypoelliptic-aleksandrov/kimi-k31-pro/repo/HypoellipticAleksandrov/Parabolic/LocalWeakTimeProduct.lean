module
public import HypoellipticAleksandrov.Parabolic.BoundedWeakDirectionalProduct

public import HypoellipticAleksandrov.Parabolic.WeakJetProduct
public import HypoellipticAleksandrov.Parabolic.TimeVelocitySmoothCompactPlateau
public import HypoellipticAleksandrov.Parabolic.WeakDerivativesCompactGlobalization
public import HypoellipticAleksandrov.Parabolic.WeakDerivativeSpacetimeMollification
public import HypoellipticAleksandrov.Parabolic.SpacetimeMollifierL2
public import HypoellipticAleksandrov.Analysis.L2ProductConvergence
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Filter Function MeasureTheory Set Topology
open scoped ENNReal Topology
open SpacetimeMollifier

/-- A scalar that is `C¹` on an open time--velocity carrier has its literal
time derivative as its raw weak time derivative there. -/
theorem contDiffOn_one_hasWeakTimeDerivOn
    {d : ℕ} (U : Set (TimeVelocity d)) (hU : IsOpen U)
    (q : TimeVelocity d → ℝ) (hq : ContDiffOn ℝ 1 q U) :
    HasWeakTimeDerivOn U q (timeDerivative q) := by
  simpa only [HasWeakDirectionalDerivOn, HasWeakTimeDerivOn, timeDerivative] using
    contDiffOn_one_hasWeakDirectionalDerivOn U hU (1, 0) q hq

/-- A bounded jointly `C¹` multiplier obeys the weak time Leibniz rule on an
open carrier, with quantitative `L²` control. -/
theorem timeC1_mul_hasWeakTimeDerivOn_memLp_eLpNorm_le
    {d : ℕ} {U : Set (TimeVelocity d)} (hU : IsOpen U)
    (Bq Bdt : ℝ) (hBq : 0 ≤ Bq) (hBdt : 0 ≤ Bdt)
    (q : TimeVelocity d → ℝ) (hqC1 : ContDiffOn ℝ 1 q U)
    (hqBound : ∀ z ∈ U, |q z| ≤ Bq)
    (hdtqBound : ∀ z ∈ U, |timeDerivative q z| ≤ Bdt)
    (u ut : TimeVelocity d → ℝ)
    (hu : ParabolicMemLpOn U 2 u)
    (hut : ParabolicMemLpOn U 2 ut)
    (hweak : HasWeakTimeDerivOn U u ut) :
    AEStronglyMeasurable (timeDerivative q) (timeVelocityVolumeOn U) ∧
      ParabolicMemLpOn U 2 (fun z ↦ q z * u z) ∧
      ParabolicMemLpOn U 2
        (fun z ↦ q z * ut z + timeDerivative q z * u z) ∧
      HasWeakTimeDerivOn U (fun z ↦ q z * u z)
        (fun z ↦ q z * ut z + timeDerivative q z * u z) ∧
      ENNReal.toReal (eLpNorm (fun z ↦ q z * u z) 2
          (timeVelocityVolumeOn U)) ≤
        Bq * ENNReal.toReal (eLpNorm u 2 (timeVelocityVolumeOn U)) ∧
      ENNReal.toReal (eLpNorm
          (fun z ↦ q z * ut z + timeDerivative q z * u z) 2
          (timeVelocityVolumeOn U)) ≤
        Bq * ENNReal.toReal (eLpNorm ut 2 (timeVelocityVolumeOn U)) +
          Bdt * ENNReal.toReal (eLpNorm u 2 (timeVelocityVolumeOn U)) := by
  have h := directionalC1_mul_hasWeakDirectionalDerivOn_memLp_eLpNorm_le hU (1, 0)
    Bq Bdt hBq hBdt q hqC1 hqBound hdtqBound u ut hu hut hweak
  refine ⟨?_, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩
  change AEStronglyMeasurable (fun z => fderiv ℝ q z (1, 0)) (timeVelocityVolumeOn U)
  exact h.1

end HypoellipticAleksandrov.Parabolic
