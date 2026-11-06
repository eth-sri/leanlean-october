module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursionUnconditionalSetting
import Mathlib.Tactic
import Lean.Elab.Tactic.Grind



/-! # Internal faces lie strictly inside the next alternating velocity domain -/

 public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set

variable (c : Clock)

/-- The closed entrance interval is strictly inside the open active interval. -/
theorem visitClosedEntrance_subset_active  : closure c.entrance ⊆ c.active := by

  rw [Clock.entrance, closure_Ioo (show c.vbar - c.r / 2 < c.vbar + c.r / 2 by linarith [c.positive]).ne]
  intro v hv
  change c.vbar - 3 * c.r / 4 < v ∧ v < c.vbar + 3 * c.r / 4
  constructor <;> linarith [hv.1, hv.2, c.positive]

/-- The active endpoints lie outside the closed entrance interval. -/
theorem visitActiveFrontier_disjoint_closedEntrance  :
    Disjoint (frontier c.active) (closure c.entrance) := by
  have ho : c.vbar - 3 * c.r / 4 < c.vbar + 3 * c.r / 4 := by linarith [c.positive]
  have hi : c.vbar - c.r / 2 < c.vbar + c.r / 2 := by linarith [c.positive]
  rw [Clock.active, frontier_Ioo ho, Clock.entrance, closure_Ioo hi.ne]
  apply Set.disjoint_left.mpr
  intro v hv hw
  rcases hv with hv | hv
  · grind
  · grind

variable (J : Interval) (s T : ℝ)

/-- Every incoming internal face point is an interior active-domain pole. -/
theorem visitIncomingFace_subset_activePole   :
    visitBoundary s T (visitEntranceInterval c) J ⊆
      visitPoleSet (visitActiveUnion c J) s T := by
  intro p hp
  refine ⟨hp.1, hp.2.1, ?_⟩
  rw [visitActiveUnion_carrier]
  refine ⟨visitClosedEntrance_subset_active c ?_, hp.2.2.2⟩

  exact (frontier_subset_closure hp.2.2.1)

/-- Every outgoing internal face point is an interior waiting-domain pole. -/
theorem visitOutgoingFace_subset_waitingPole   :
    visitBoundary s T (visitActiveInterval c) J ⊆
      visitPoleSet (visitWaitingUnion c J) s T := by
  intro p hp
  refine ⟨hp.1, hp.2.1, ?_⟩
  rw [visitWaitingUnion_carrier]
  refine ⟨hp.2.2.2, ?_⟩
  intro hv
  exact Set.disjoint_left.mp (visitActiveFrontier_disjoint_closedEntrance c) hp.2.2.1 hv

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
