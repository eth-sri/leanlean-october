module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FiniteUnionDomains
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.GreenTestExtensionCanonical
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoundedSourceLimitsInfinite

/-! # Componentwise physical Green and exit measures on finite disjoint interval unions -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/- The union Green measure is the actual Green measure of the pole's unique component. -/
def finiteUnionGreen
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : FiniteIntervalUnion) (T : WithTop ℝ)
    (e : FiniteUnionPole H T) : Measure Point :=
  stripGreen hH hLE hlam hLam A (H.component (finiteUnionPoleIndex H T e)) T
    (finiteUnionComponentPole H T e)

/- The finite-horizon union exit measure uses the same unique component. -/
def finiteUnionExit
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : FiniteIntervalUnion) (T : ℝ)
    (e : FiniteUnionPole H (T : WithTop ℝ)) : Measure Point :=
  stripExit hH hLE hlam hLam A (H.component (finiteUnionPoleIndex H T e)) T
    (finiteUnionComponentPole H T e)

/- Green measures do not depend on a component representation once membership is certified. -/
theorem finiteUnionGreen_component
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam } (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : FiniteIntervalUnion) (i : Fin H.count)
    (T : WithTop ℝ) (e : StripPole (H.component i) T) :
    finiteUnionGreen hH hLE hlam hLam A H T (componentPoleInclusion H i T e) =
      stripGreen hH hLE hlam hLam A (H.component i) T e := by
  unfold finiteUnionGreen
  congr 1
  · rw [finiteUnionPoleIndex_inclusion]
  · exact (Subtype.heq_iff_coe_eq
      (fun p => by rw [finiteUnionPoleIndex_inclusion])).2 rfl

/- Exit measures do not depend on a component representation once membership is certified. -/
theorem finiteUnionExit_component
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : FiniteIntervalUnion) (i : Fin H.count)
    (T : ℝ) (e : StripPole (H.component i) (T : WithTop ℝ)) :
    finiteUnionExit hH hLE hlam hLam A H T (componentPoleInclusion H i T e) =
      stripExit hH hLE hlam hLam A (H.component i) T e := by
  unfold finiteUnionExit
  congr 1
  · rw [finiteUnionPoleIndex_inclusion]
  · exact (Subtype.heq_iff_coe_eq
      (fun p => by rw [finiteUnionPoleIndex_inclusion])).2 rfl

/- Every componentwise union Green measure is finite, including at infinite time. -/
instance finiteUnionExit_isProbabilityMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : FiniteIntervalUnion) (T : ℝ)
    (e : FiniteUnionPole H (T : WithTop ℝ)) :
    IsProbabilityMeasure (finiteUnionExit hH hLE hlam hLam A H T e) := by
  unfold finiteUnionExit
  infer_instance

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
