module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionInitial

/-! # Unconditional finite alternating Green and exit identities -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory

section
variable {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ)
  (hT : s < T) (P : Point) (hP : s ≤ P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier) (N : ℕ)
include lam Lam A c J s T hT P hP N

/-- The actual Green kernels satisfy the source's finite alternating identity. -/
theorem enlargedAlternating_green :
    let GA := enlargedVisitGreenKernel A (visitActiveUnion c J) T
    let GW := enlargedVisitGreenKernel A (visitWaitingUnion c J) T
    let GO := enlargedVisitGreenKernel A J.toFiniteUnion T
    let gamma := enlargedVisitEntrance A c J s T P
    let beta := enlargedVisitOutgoing A c J s T P
    GO P = visitInitialGreen P (visitEntranceInterval c) GW +
      ∑ n ∈ Finset.range N, (GA ∘ₘ gamma n + GW ∘ₘ beta n) + GO ∘ₘ gamma N := by
  apply alternating_green_of_nested_splitting
  · exact (enlargedInitial_nested A c J s T hT P hP).1
  · intro n
    exact (enlargedEntrance_nested A c J s T hT P hP n).1
  · intro n
    exact (enlargedOutgoing_nested A c J s T hT P n).1

/-- The actual exit kernels satisfy the source's finite alternating identity. -/
theorem enlargedAlternating_exit :
    let EA := enlargedVisitExitKernel A (visitActiveUnion c J) T
    let EW := enlargedVisitExitKernel A (visitWaitingUnion c J) T
    let EO := enlargedVisitExitKernel A J.toFiniteUnion T
    let gamma := enlargedVisitEntrance A c J s T P
    let beta := enlargedVisitOutgoing A c J s T P
    let outer := finiteUnionExitSet J.toFiniteUnion s T
    EO P = visitInitialExit P (visitEntranceInterval c) outer EW +
      ∑ n ∈ Finset.range N,
        ((EA ∘ₘ gamma n).restrict outer + (EW ∘ₘ beta n).restrict outer) +
          EO ∘ₘ gamma N := by
  apply alternating_exit_of_nested_splitting
  · exact (enlargedInitial_nested A c J s T hT P hP).2
  · intro n
    exact (enlargedEntrance_nested A c J s T hT P hP n).2
  · intro n
    exact (enlargedOutgoing_nested A c J s T hT P n).2

end

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
