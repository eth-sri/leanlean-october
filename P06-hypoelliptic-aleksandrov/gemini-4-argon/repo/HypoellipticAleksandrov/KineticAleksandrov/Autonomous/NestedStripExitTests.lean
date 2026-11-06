module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripSlab
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripIntervalBoundary

/-! # Exact nested exit decomposition on arbitrary compact ambient probes -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/- The actual larger exit mixture restarted from the smaller internal boundary. -/
def nestedIntervalRestartExit
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam } (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : Interval) (sMinus T : ℝ)
    (e : StripPole H1 (T : WithTop ℝ)) : Measure Point :=
  (nestedIntervalRestartPoles hH hLE hlam hLam A H1 H2 sMinus T e).bind
    (stripExit hH hLE hlam hLam A H2 T)

/- The actual restarted exit mixture is finite. -/
instance nestedIntervalRestartExit_isFiniteMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : Interval) (sMinus T : ℝ)
    (e : StripPole H1 (T : WithTop ℝ)) :
    IsFiniteMeasure (nestedIntervalRestartExit hH hLE hlam hLam A H1 H2 sMinus T e) := by
  constructor
  unfold nestedIntervalRestartExit
  rw [Measure.bind_apply MeasurableSet.univ
    (stripExit_measurable hH hLE hlam hLam A H2 T).aemeasurable]
  simp only [stripExit_mass_one, lintegral_const, one_mul]
  exact measure_lt_top _ _

/- Every compact probe satisfies the literal larger-exit equals outer-exit plus restart
  identity. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
