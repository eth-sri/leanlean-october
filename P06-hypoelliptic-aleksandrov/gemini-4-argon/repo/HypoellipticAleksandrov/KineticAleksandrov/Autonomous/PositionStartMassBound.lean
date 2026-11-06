module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionStartPointBounds
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionCellsSlab
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionStartIntegrated
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionStartLower

/-! # The position-start count inequality before full-space domination -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory

/- Pull the literal phase-space source box back to physical spacetime. -/
def positionStartBox (c : Clock) (Y : ℝ) : Set Point :=
  {q | (q.position 0, q.velocity 0) ∈ box 4 c.r Y}

/- The physical source box is measurable. -/
theorem measurableSet_positionStartBox (c : Clock) (Y : ℝ) :
    MeasurableSet (positionStartBox c Y) :=
  (box_measurable 4 c.r Y).preimage
    (((continuous_apply 0).comp continuous_position).measurable.prodMk
      ((continuous_apply 0).comp continuous_velocity).measurable)

/- One uniform generator constant bounds the count in every finite entrance mixture. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
