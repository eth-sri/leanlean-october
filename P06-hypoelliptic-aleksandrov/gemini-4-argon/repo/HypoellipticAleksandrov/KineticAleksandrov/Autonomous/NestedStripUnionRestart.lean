module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripRestartPoles
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripKernelIntegral

/-! # Measurable point restart poles and exact source disintegration -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/- The actual internal exit of a single union pole, on the larger union pole carrier. -/
def finiteUnionPointRestartPoles
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam } (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : FiniteIntervalUnion) (sMinus T : ℝ)
    (e : FiniteUnionPole H1 (T : WithTop ℝ)) : Measure (FiniteUnionPole H2 (T : WithTop ℝ)) :=
  ((finiteUnionExit hH hLE hlam hLam A H1 T e).restrict
    (finiteUnionInternalExit H1 H2 sMinus T)).comap Subtype.val

/- Single-pole internal exits are finite. -/
theorem finiteUnionPointRestartPoles_measurable
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam } (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : FiniteIntervalUnion) (sMinus T : ℝ) :
    Measurable (finiteUnionPointRestartPoles hH hLE hlam hLam A H1 H2 sMinus T) := by
  exact nested_measurable_family_comap _
    (nested_measurable_family_restrict _ (finiteUnionExit_measurable hH hLE hlam hLam A H1 T)
      _ (measurableSet_finiteUnionInternalExit H1 H2 sMinus T)) _
        (measurableSet_finiteUnionPole H2 T)

/- The finite-source restart is exactly the actual measurable integral of point restarts. -/
theorem finiteUnionRestartPoleMeasure_disintegration
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam } (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : FiniteIntervalUnion) (sMinus T : ℝ)
    (nu : Measure (FiniteUnionPole H1 (T : WithTop ℝ))) :
    finiteUnionRestartPoleMeasure hH hLE hlam hLam A H1 H2 sMinus T nu =
      nu.bind (finiteUnionPointRestartPoles hH hLE hlam hLam A H1 H2 sMinus T) := by
  unfold finiteUnionRestartPoleMeasure finiteUnionRestartMeasure finiteUnionExitMixture
  have hr := nested_bind_restrict nu (finiteUnionExit hH hLE hlam hLam A H1 T)
    (finiteUnionExit_measurable hH hLE hlam hLam A H1 T)
    (finiteUnionInternalExit H1 H2 sMinus T)
    (measurableSet_finiteUnionInternalExit H1 H2 sMinus T)
  have hc := congrArg (fun μ : Measure Point => μ.comap
    (Subtype.val : FiniteUnionPole H2 (T : WithTop ℝ) → Point)) hr
  exact hc.trans (nested_comap_bind nu _
    (nested_measurable_family_restrict _ (finiteUnionExit_measurable hH hLE hlam hLam A H1 T)
      _ (measurableSet_finiteUnionInternalExit H1 H2 sMinus T)) _
        (measurableSet_finiteUnionPole H2 T))

/- Returning point restart poles to physical coordinates recovers the literal restricted exit. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
