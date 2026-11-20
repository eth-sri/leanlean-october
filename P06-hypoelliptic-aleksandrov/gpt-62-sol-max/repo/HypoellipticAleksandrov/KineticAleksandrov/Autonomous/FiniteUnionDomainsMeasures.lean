module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FiniteUnionDomains
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.GreenTestExtensionCanonical
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoundedSourceLimitsInfinite

/-! # Componentwise physical Green and exit measures on finite disjoint interval unions -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

section
variable {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) (H : FiniteIntervalUnion)
include lam Lam A

/-- The union Green measure is the actual Green measure of the pole's unique component. -/
def finiteUnionGreen (T : WithTop ℝ)
    (e : FiniteUnionPole H T) : Measure Point :=
  stripGreen A (H.component (finiteUnionPoleIndex H T e)) T
    (finiteUnionComponentPole H T e)

/-- The finite-horizon union exit measure uses the same unique component. -/
def finiteUnionExit (T : ℝ)
    (e : FiniteUnionPole H (T : WithTop ℝ)) : Measure Point :=
  stripExit A (H.component (finiteUnionPoleIndex H T e)) T
    (finiteUnionComponentPole H T e)

end

section
variable {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) (H : FiniteIntervalUnion) (i : Fin H.count)

/-- Green measures do not depend on a component representation once membership is certified. -/
theorem finiteUnionGreen_component
    (T : WithTop ℝ) (e : StripPole (H.component i) T) :
    finiteUnionGreen A H T (componentPoleInclusion H i T e) =
      stripGreen A (H.component i) T e := by
  unfold finiteUnionGreen
  congr 1
  · rw [finiteUnionPoleIndex_inclusion]
  · exact (Subtype.heq_iff_coe_eq
      (fun p => by rw [finiteUnionPoleIndex_inclusion])).2 rfl

/-- Exit measures do not depend on a component representation once membership is certified. -/
theorem finiteUnionExit_component
    (T : ℝ) (e : StripPole (H.component i) (T : WithTop ℝ)) :
    finiteUnionExit A H T (componentPoleInclusion H i T e) =
      stripExit A (H.component i) T e := by
  unfold finiteUnionExit
  congr 1
  · rw [finiteUnionPoleIndex_inclusion]
  · exact (Subtype.heq_iff_coe_eq
      (fun p => by rw [finiteUnionPoleIndex_inclusion])).2 rfl

end

/-- Every componentwise union Green measure is finite, including at infinite time. -/
instance finiteUnionGreen_isFiniteMeasure
    
    {lam Lam : ℝ} 
    (A : SmoothAutonomous lam Lam) (H : FiniteIntervalUnion) (T : WithTop ℝ)
    (e : FiniteUnionPole H T) : IsFiniteMeasure (finiteUnionGreen A H T e) := by
  unfold finiteUnionGreen
  infer_instance

/-- Every finite-horizon componentwise union exit measure has mass one. -/
instance finiteUnionExit_isProbabilityMeasure
    
    {lam Lam : ℝ} 
    (A : SmoothAutonomous lam Lam) (H : FiniteIntervalUnion) (T : ℝ)
    (e : FiniteUnionPole H (T : WithTop ℝ)) :
    IsProbabilityMeasure (finiteUnionExit A H T e) := by
  unfold finiteUnionExit
  infer_instance

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
