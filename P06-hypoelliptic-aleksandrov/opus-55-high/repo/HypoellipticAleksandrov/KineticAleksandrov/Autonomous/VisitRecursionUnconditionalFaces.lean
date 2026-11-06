module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursionUnconditionalSetting
import Mathlib.Tactic

/-! # Internal faces lie strictly inside the next alternating velocity domain -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set

variable (c : Clock) (J : Interval) (s T : ℝ)

/-- The closed entrance interval is strictly inside the open active interval. -/
theorem visitClosedEntrance_subset_active  : closure c.entrance ⊆ c.active := by
  have ho : c.vbar - c.r / 2 < c.vbar + c.r / 2 := by linarith [c.positive]
  rw [Clock.entrance, closure_Ioo ho.ne]
  intro v hv
  change c.vbar - 3 * c.r / 4 < v ∧ v < c.vbar + 3 * c.r / 4
  grind

/-- The active endpoints lie outside the closed entrance interval. -/
theorem visitActiveFrontier_disjoint_closedEntrance  :
    Disjoint (frontier c.active) (closure c.entrance) := by
  have ho : c.vbar - 3 * c.r / 4 < c.vbar + 3 * c.r / 4 := by linarith [c.positive]
  have hi : c.vbar - c.r / 2 < c.vbar + c.r / 2 := by linarith
  rw [Clock.active, frontier_Ioo ho, Clock.entrance, closure_Ioo hi.ne]
  grind

/-- Every incoming internal face point is an interior active-domain pole. -/
theorem visitIncomingFace_subset_activePole  :
    visitBoundary s T (visitEntranceInterval c) J ⊆
      visitPoleSet (visitActiveUnion c J) s T := by
  intro p hp
  refine ⟨hp.1, hp.2.1, ?_⟩
  rw [visitActiveUnion_carrier]
  refine ⟨visitClosedEntrance_subset_active c ?_, hp.2.2.2⟩
  have hv := frontier_subset_closure hp.2.2.1
  exact hv

/-- Every outgoing internal face point is an interior waiting-domain pole. -/
theorem visitOutgoingFace_subset_waitingPole  :
    visitBoundary s T (visitActiveInterval c) J ⊆
      visitPoleSet (visitWaitingUnion c J) s T := by
  intro p hp
  refine ⟨hp.1, hp.2.1, ?_⟩
  rw [visitWaitingUnion_carrier]
  refine ⟨hp.2.2.2, ?_⟩
  intro hv
  exact Set.disjoint_left.mp (visitActiveFrontier_disjoint_closedEntrance c) hp.2.2.1 hv

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
