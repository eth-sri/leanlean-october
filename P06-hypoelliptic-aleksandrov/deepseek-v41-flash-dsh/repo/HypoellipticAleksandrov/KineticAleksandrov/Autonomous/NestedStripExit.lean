module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripExitTests
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripGreen

/-! # Literal Green and exit decomposition for a pole in nested intervals -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- The actual larger exit measure is the smaller outer exit plus its actual internal restart. -/
theorem nestedIntervalExit_identity
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : Interval)
    (hsub : H1.carrier ⊆ H2.carrier) (sMinus T : ℝ)
    (e : StripPole H1 (T : WithTop ℝ)) (he : sMinus < e.1.time) :
    stripExit hH hLE hlam hLam A H2 T (nestedPoleInclusion H1 H2 hsub T e) =
      (stripExit hH hLE hlam hLam A H1 T e).restrict (reconstructionExit H2 sMinus T) +
        nestedIntervalRestartExit hH hLE hlam hLam A H1 H2 sMinus T e := by
  apply nested_physical_measure_eq univ isOpen_univ
    (Filter.Eventually.of_forall (fun _ => mem_univ _))
    (Filter.Eventually.of_forall (fun _ => mem_univ _))
  intro f _ _
  rw [integral_add_measure (nestedProbe_integrable A f _)
    (nestedProbe_integrable A f _)]
  exact nestedIntervalExit_probe_identity hH hLE hlam hLam A H1 H2 hsub sMinus T e he f

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
