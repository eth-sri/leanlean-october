module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursionUnconditionalNested
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursionUnconditionalSupport
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursionUnconditionalInternalFaces

/-! # Unconditional active and waiting steps of the physical visit recursion -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory

variable (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ) (hT : s < T) (P : Point)

include hT
/-- Every actual active visit has the genuine outer Green and exit splitting. -/
theorem visitEntrance_nested
     (hP : s < P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier) (n : ℕ) :
    let gamma := visitEntrancePiece hH hLE hlam hLam A c J s T P n
    let beta := visitOutgoingPiece hH hLE hlam hLam A c J s T P n
    visitUnionGreenKernel hH hLE hlam hLam A J.toFiniteUnion s T ∘ₘ gamma =
      visitUnionGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) s T ∘ₘ gamma +
        visitUnionGreenKernel hH hLE hlam hLam A J.toFiniteUnion s T ∘ₘ beta ∧
    visitUnionExitKernel hH hLE hlam hLam A J.toFiniteUnion s T ∘ₘ gamma =
      (visitUnionExitKernel hH hLE hlam hLam A (visitActiveUnion c J) s T ∘ₘ gamma).restrict
        (finiteUnionExitSet J.toFiniteUnion s T) +
        visitUnionExitKernel hH hLE hlam hLam A J.toFiniteUnion s T ∘ₘ beta := by

  have h := visitUnion_nested hH hLE hlam hLam A (visitActiveUnion c J) J.toFiniteUnion
    (by
        rw [visitActiveUnion_carrier, Interval.toFiniteUnion_carrier]
        exact inter_subset_right) s T hT (visitEntrancePiece hH hLE hlam hLam A c J s T P n)
    (visitEntrancePiece_ae_activePole hH hLE hlam hLam A c J s T P hP n)
  simpa only [visitActive_internalExit, visitOutgoingPiece, visitBeta,
    visitEntrancePiece] using h

/-- Every actual waiting visit has the genuine outer Green and exit splitting. -/
theorem visitOutgoing_nested
     (n : ℕ) :
    let beta := visitOutgoingPiece hH hLE hlam hLam A c J s T P n
    let gamma := visitEntrancePiece hH hLE hlam hLam A c J s T P (n + 1)
    visitUnionGreenKernel hH hLE hlam hLam A J.toFiniteUnion s T ∘ₘ beta =
      visitUnionGreenKernel hH hLE hlam hLam A (visitWaitingUnion c J) s T ∘ₘ beta +
        visitUnionGreenKernel hH hLE hlam hLam A J.toFiniteUnion s T ∘ₘ gamma ∧
    visitUnionExitKernel hH hLE hlam hLam A J.toFiniteUnion s T ∘ₘ beta =
      (visitUnionExitKernel hH hLE hlam hLam A (visitWaitingUnion c J) s T ∘ₘ beta).restrict
        (finiteUnionExitSet J.toFiniteUnion s T) +
        visitUnionExitKernel hH hLE hlam hLam A J.toFiniteUnion s T ∘ₘ gamma := by

  have h := visitUnion_nested hH hLE hlam hLam A (visitWaitingUnion c J) J.toFiniteUnion
    (by
        rw [visitWaitingUnion_carrier, Interval.toFiniteUnion_carrier]
        exact sdiff_subset) s T hT (visitOutgoingPiece hH hLE hlam hLam A c J s T P n)
    (visitOutgoingPiece_ae_waitingPole hH hLE hlam hLam A c J s T P n)
  simpa only [visitWaiting_internalExit, visitEntrancePiece, visitGamma,
    visitOutgoingPiece, visitBeta] using h

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
