module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.GreenTestExtensionSmooth

/-! # Canonical autonomous exit measures from the unique evolution and Riesz characterizations -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open SectionTwo

/-- The canonical exit measure uses the independently characterized autonomous evolution. -/
def stripExit
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (T : ℝ)
    (e : StripPole H (T : WithTop ℝ)) : Measure Point :=
  stripExitOfRealization hlam hLam A H (stripEvolution hlam hLam A H)
    (stripEvolution_spec hlam hLam A H) T e

/-- Each canonical exit measure is finite. -/
instance stripExit_isFiniteMeasure
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (T : ℝ)
    (e : StripPole H (T : WithTop ℝ)) : IsFiniteMeasure (stripExit hlam hLam A H T e) := by
  unfold stripExit
  infer_instance

/-- The canonical family has Borel dependence on its valid pole. -/
theorem stripExit_measurable
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (T : ℝ) :
    Measurable (stripExit hlam hLam A H T) :=
  by apply stripExitOfRealization_measurable <;> assumption

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
