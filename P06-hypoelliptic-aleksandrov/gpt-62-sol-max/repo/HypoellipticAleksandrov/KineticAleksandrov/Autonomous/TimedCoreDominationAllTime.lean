module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDominationAllTime
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TimedCoreDominationIdentity
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisits
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonOrder

/-! # Genuine core domination by the all-time Green measure of the actual entrance count -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory

section
variable {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval)

/-- Each actual clipped active Green kernel is bounded by the full all-time active-strip kernel. -/
theorem enlargedActiveGreenKernel_le_allTime (T : ℝ) (p : Point) :
    enlargedVisitGreenKernel A (visitActiveUnion c J) T p ≤
      enlargedActiveGreenKernel A c p := by
  apply visitExtendKernel_le_of_subtype
  exact fun e => finiteUnionGreen_le_enlargedActiveGreenKernel A c J T (enlargedVisitPole _ T e)

/-- The genuine active Green mixture is bounded by its all-time active-strip extension. -/
theorem enlargedActiveGreenMixture_le_allTime (T : ℝ) (mu : Measure Point) :
    enlargedVisitGreenKernel A (visitActiveUnion c J) T ∘ₘ mu ≤
      enlargedActiveGreen A c mu := visitKernel_compMeasure_le mu (enlargedActiveGreenKernel_le_allTime A c J T)

/-- Core occupation is dominated by the actual all-time Green measure of the full visit count. -/
theorem enlargedOuterGreen_core_domination_of_finite_count (s T : ℝ) (hT : s < T)
    (P : Point) (hP : s ≤ P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier)
    [IsFiniteMeasure (enlargedVisitStarts A c J s T P)] :
    (enlargedVisitGreenKernel A J.toFiniteUnion T P).restrict
      {q | q.velocity 0 ∈ c.core} ≤
    (enlargedActiveGreen A c
      (Measure.sum (enlargedVisitEntrance A c J s T P))).restrict
        {q | q.velocity 0 ∈ c.core} := by
  let C : Set Point := {q | q.velocity 0 ∈ c.core}
  have hC : MeasurableSet C :=
    isClosed_Icc.measurableSet.preimage ((continuous_apply 0).comp continuous_velocity).measurable
  rw [enlargedOuterGreen_core_identity_of_finite_count A c J s T hT P hP]
  unfold enlargedActiveGreen
  rw [Measure.bind_sum _ _ (Kernel.aemeasurable _), Measure.restrict_sum _ hC]
  apply Measure.le_iff.mpr
  intro B hB
  rw [Measure.sum_apply _ hB, Measure.sum_apply _ hB]
  apply ENNReal.tsum_le_tsum
  intro n
  exact Measure.restrict_mono_measure
    (enlargedActiveGreenMixture_le_allTime A c J T
      (enlargedVisitEntrance A c J s T P n)) C B

end

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
