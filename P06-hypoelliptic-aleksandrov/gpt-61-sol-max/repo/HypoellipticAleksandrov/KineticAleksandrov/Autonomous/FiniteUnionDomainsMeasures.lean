module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FiniteUnionDomains
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.GreenTestExtensionCanonical
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoundedSourceLimitsInfinite

/-! # Componentwise physical Green and exit measures on finite disjoint interval unions -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open MeasureTheory

variable (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam) (H : FiniteIntervalUnion)

/-- The union Green measure is the actual Green measure of the pole's unique component. -/
def finiteUnionGreen
     (T : WithTop ℝ)
    (e : FiniteUnionPole H T) : Measure Point :=
  stripGreen hH hLE hlam hLam A _ T
    (finiteUnionComponentPole H T e)

/-- The finite-horizon union exit measure uses the same unique component. -/
def finiteUnionExit
     (T : ℝ)
    (e : FiniteUnionPole H (T : WithTop ℝ)) : Measure Point :=
  stripExit hH hLE hlam hLam A _ T
    (finiteUnionComponentPole H T e)

variable (i : Fin H.count)

/-- Green measures do not depend on a component representation once membership is certified. -/
theorem finiteUnionGreen_component

    (T : WithTop ℝ) (e : StripPole (H.component i) T) :
    finiteUnionGreen hH hLE hlam hLam A H T (componentPoleInclusion H i T e) =
      stripGreen hH hLE hlam hLam A (H.component i) T e := by
  unfold finiteUnionGreen
  congr 1
  · rw [finiteUnionPoleIndex_inclusion]
  · exact (Subtype.heq_iff_coe_eq
      (fun p => by rw [finiteUnionPoleIndex_inclusion])).2 rfl

/-- Exit measures do not depend on a component representation once membership is certified. -/
theorem finiteUnionExit_component

    (T : ℝ) (e : StripPole (H.component i) (T : WithTop ℝ)) :
    finiteUnionExit hH hLE hlam hLam A H T (componentPoleInclusion H i T e) =
      stripExit hH hLE hlam hLam A (H.component i) T e := by
  unfold finiteUnionExit
  congr 1
  · rw [finiteUnionPoleIndex_inclusion]
  · exact (Subtype.heq_iff_coe_eq
      (fun p => by rw [finiteUnionPoleIndex_inclusion])).2 rfl



/-- Every finite-horizon componentwise union exit measure has mass one. -/
instance finiteUnionExit_isProbabilityMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : FiniteIntervalUnion) (T : ℝ)
    (e : FiniteUnionPole H (T : WithTop ℝ)) :
    IsProbabilityMeasure (finiteUnionExit hH hLE hlam hLam A H T e) := by
  unfold finiteUnionExit
  infer_instance

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
