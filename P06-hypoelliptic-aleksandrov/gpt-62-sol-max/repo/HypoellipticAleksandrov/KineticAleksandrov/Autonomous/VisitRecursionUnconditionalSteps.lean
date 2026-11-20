module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursionUnconditionalNested
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursionUnconditionalSupport
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursionUnconditionalInternalFaces

/-! # Unconditional active and waiting steps of the physical visit recursion -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory

section
variable {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ)
  (hT : s < T) (P : Point)
include lam Lam A c J s T hT P

/-- Every actual active visit has the genuine outer Green and exit splitting. -/
theorem visitEntrance_nested (hP : s < P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier) (n : ℕ) :
    let gamma := visitEntrancePiece A c J s T P n
    let beta := visitOutgoingPiece A c J s T P n
    visitUnionGreenKernel A J.toFiniteUnion s T ∘ₘ gamma =
      visitUnionGreenKernel A (visitActiveUnion c J) s T ∘ₘ gamma +
        visitUnionGreenKernel A J.toFiniteUnion s T ∘ₘ beta ∧
    visitUnionExitKernel A J.toFiniteUnion s T ∘ₘ gamma =
      (visitUnionExitKernel A (visitActiveUnion c J) s T ∘ₘ gamma).restrict
        (finiteUnionExitSet J.toFiniteUnion s T) +
        visitUnionExitKernel A J.toFiniteUnion s T ∘ₘ beta := by
  have hsub : (visitActiveUnion c J).carrier ⊆ J.toFiniteUnion.carrier := by
    rw [visitActiveUnion_carrier, Interval.toFiniteUnion_carrier]
    exact inter_subset_right
  have h := visitUnion_nested A (visitActiveUnion c J) J.toFiniteUnion
    hsub s T hT (visitEntrancePiece A c J s T P n)
    (visitEntrancePiece_ae_activePole A c J s T P hP n)
  simpa only [visitActive_internalExit, visitOutgoingPiece, visitBeta,
    visitEntrancePiece] using h

/-- Every actual waiting visit has the genuine outer Green and exit splitting. -/
theorem visitOutgoing_nested (n : ℕ) :
    let beta := visitOutgoingPiece A c J s T P n
    let gamma := visitEntrancePiece A c J s T P (n + 1)
    visitUnionGreenKernel A J.toFiniteUnion s T ∘ₘ beta =
      visitUnionGreenKernel A (visitWaitingUnion c J) s T ∘ₘ beta +
        visitUnionGreenKernel A J.toFiniteUnion s T ∘ₘ gamma ∧
    visitUnionExitKernel A J.toFiniteUnion s T ∘ₘ beta =
      (visitUnionExitKernel A (visitWaitingUnion c J) s T ∘ₘ beta).restrict
        (finiteUnionExitSet J.toFiniteUnion s T) +
        visitUnionExitKernel A J.toFiniteUnion s T ∘ₘ gamma := by
  have hsub : (visitWaitingUnion c J).carrier ⊆ J.toFiniteUnion.carrier := by
    rw [visitWaitingUnion_carrier, Interval.toFiniteUnion_carrier]
    exact sdiff_subset
  have h := visitUnion_nested A (visitWaitingUnion c J) J.toFiniteUnion
    hsub s T hT (visitOutgoingPiece A c J s T P n)
    (visitOutgoingPiece_ae_waitingPole A c J s T P n)
  simpa only [visitWaiting_internalExit, visitEntrancePiece, visitGamma,
    visitOutgoingPiece, visitBeta] using h

end

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
