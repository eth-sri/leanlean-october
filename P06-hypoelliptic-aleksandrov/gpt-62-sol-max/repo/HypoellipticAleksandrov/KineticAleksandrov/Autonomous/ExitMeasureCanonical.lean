module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitBorel

/-! # Canonical autonomous exit measures from the unique evolution and Riesz characterizations -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open SectionTwo

/-- The canonical exit measure uses the independently characterized autonomous evolution. -/
def stripExit
    
    {lam Lam : ℝ} 
    (A : SmoothAutonomous lam Lam) (H : Interval) (T : ℝ)
    (e : StripPole H (T : WithTop ℝ)) : Measure Point :=
  stripExitOfRealization A H (stripEvolution A H)
    (stripEvolution_spec A H) T e

/-- Each canonical exit measure is finite. -/
instance stripExit_isFiniteMeasure
    
    {lam Lam : ℝ} 
    (A : SmoothAutonomous lam Lam) (H : Interval) (T : ℝ)
    (e : StripPole H (T : WithTop ℝ)) : IsFiniteMeasure (stripExit A H T e) := by
  unfold stripExit
  infer_instance

/-- The canonical family has Borel dependence on its valid pole. -/
theorem stripExit_measurable
    
    {lam Lam : ℝ} 
    (A : SmoothAutonomous lam Lam) (H : Interval) (T : ℝ) :
    Measurable (stripExit A H T) :=
  stripExitOfRealization_measurable A H _
    (stripEvolution_spec A H) T

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
