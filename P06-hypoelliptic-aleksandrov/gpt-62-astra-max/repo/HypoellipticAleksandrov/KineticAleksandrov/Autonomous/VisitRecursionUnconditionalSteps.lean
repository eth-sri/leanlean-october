module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursionUnconditionalNested
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursionUnconditionalSupport
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursionUnconditionalInternalFaces

/-! # Unconditional active and waiting steps of the physical visit recursion -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory

variable {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)
    (c : Clock) (J : Interval) (s T : ℝ) (hT : s < T) (P : Point)
    (hP : s < P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier) (n : ℕ)
include hT

include hP in
/-- Every actual active visit has the genuine outer Green and exit splitting. -/
theorem visitEntrance_nested :
    let gamma := visitEntrancePiece hlam hLam A c J s T P n
    let beta := visitOutgoingPiece hlam hLam A c J s T P n
    visitUnionGreenKernel hlam hLam A J.toFiniteUnion s T ∘ₘ gamma =
      visitUnionGreenKernel hlam hLam A (visitActiveUnion c J) s T ∘ₘ gamma +
        visitUnionGreenKernel hlam hLam A J.toFiniteUnion s T ∘ₘ beta ∧
    visitUnionExitKernel hlam hLam A J.toFiniteUnion s T ∘ₘ gamma =
      (visitUnionExitKernel hlam hLam A (visitActiveUnion c J) s T ∘ₘ gamma).restrict
        (finiteUnionExitSet J.toFiniteUnion s T) +
        visitUnionExitKernel hlam hLam A J.toFiniteUnion s T ∘ₘ beta := by
  have hsub : (visitActiveUnion c J).carrier ⊆ J.toFiniteUnion.carrier := by
    rw [visitActiveUnion_carrier, Interval.toFiniteUnion_carrier]
    exact inter_subset_right
  have h := visitUnion_nested hlam hLam A (visitActiveUnion c J) J.toFiniteUnion
    hsub s T hT (visitEntrancePiece hlam hLam A c J s T P n)
    (visitEntrancePiece_ae_activePole hlam hLam A c J s T P hP n)
  simpa only [visitActive_internalExit, visitOutgoingPiece, visitBeta,
    visitEntrancePiece] using h

/-- Every actual waiting visit has the genuine outer Green and exit splitting. -/
theorem visitOutgoing_nested :
    let beta := visitOutgoingPiece hlam hLam A c J s T P n
    let gamma := visitEntrancePiece hlam hLam A c J s T P (n + 1)
    visitUnionGreenKernel hlam hLam A J.toFiniteUnion s T ∘ₘ beta =
      visitUnionGreenKernel hlam hLam A (visitWaitingUnion c J) s T ∘ₘ beta +
        visitUnionGreenKernel hlam hLam A J.toFiniteUnion s T ∘ₘ gamma ∧
    visitUnionExitKernel hlam hLam A J.toFiniteUnion s T ∘ₘ beta =
      (visitUnionExitKernel hlam hLam A (visitWaitingUnion c J) s T ∘ₘ beta).restrict
        (finiteUnionExitSet J.toFiniteUnion s T) +
        visitUnionExitKernel hlam hLam A J.toFiniteUnion s T ∘ₘ gamma := by
  have hsub : (visitWaitingUnion c J).carrier ⊆ J.toFiniteUnion.carrier := by
    rw [visitWaitingUnion_carrier, Interval.toFiniteUnion_carrier]
    exact sdiff_subset
  have h := visitUnion_nested hlam hLam A (visitWaitingUnion c J) J.toFiniteUnion
    hsub s T hT (visitOutgoingPiece hlam hLam A c J s T P n)
    (visitOutgoingPiece_ae_waitingPole hlam hLam A c J s T P n)
  simpa only [visitWaiting_internalExit, visitEntrancePiece, visitGamma,
    visitOutgoingPiece, visitBeta] using h

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
