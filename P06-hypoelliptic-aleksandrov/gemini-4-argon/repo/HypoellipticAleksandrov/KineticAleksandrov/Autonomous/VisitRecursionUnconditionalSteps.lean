module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursionUnconditionalNested
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursionUnconditionalSupport
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursionUnconditionalInternalFaces
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursionUnconditionalFaces

/-! # Unconditional active and waiting steps of the physical visit recursion -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory
open scoped Classical

/- Every actual active visit has the genuine outer Green and exit splitting. -/
theorem visitEntrance_nested
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam } (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T ) (hT : s < T)
    (P : Point) (hP : s < P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier) (n : ℕ) :
    let gamma := visitEntrancePiece hH hLE hlam hLam A c J s T P n
    let beta := visitOutgoingPiece hH hLE hlam hLam A c J s T P n
    visitUnionGreenKernel hH hLE hlam hLam A J.toFiniteUnion s T ∘ₘ gamma =
      visitUnionGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) s T ∘ₘ gamma +
        visitUnionGreenKernel hH hLE hlam hLam A J.toFiniteUnion s T ∘ₘ beta ∧
    visitUnionExitKernel hH hLE hlam hLam A J.toFiniteUnion s T ∘ₘ gamma =
      (visitUnionExitKernel hH hLE hlam hLam A (visitActiveUnion c J) s T ∘ₘ gamma).restrict
        (finiteUnionExitSet J.toFiniteUnion s T) +
        visitUnionExitKernel hH hLE hlam hLam A J.toFiniteUnion s T ∘ₘ beta := by
  have hsub : (visitActiveUnion c J).carrier ⊆ J.toFiniteUnion.carrier := by
    rw [visitActiveUnion_carrier, Interval.toFiniteUnion_carrier]
    exact inter_subset_right
  have h := visitUnion_nested hH hLE hlam hLam A (visitActiveUnion c J) J.toFiniteUnion
    hsub s T hT (visitEntrancePiece hH hLE hlam hLam A c J s T P n)
    (visitEntrancePiece_ae_activePole hH hLE hlam hLam A c J s T P hP n)
  simpa only [visitActive_internalExit, visitOutgoingPiece, visitBeta,
    visitEntrancePiece] using h

/- Every actual waiting visit has the genuine outer Green and exit splitting. -/
theorem visitOutgoing_nested
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam } (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T ) (hT : s < T)
    (P : Point) (n : ℕ) :
    let beta := visitOutgoingPiece hH hLE hlam hLam A c J s T P n
    let gamma := visitEntrancePiece hH hLE hlam hLam A c J s T P (n + 1)
    visitUnionGreenKernel hH hLE hlam hLam A J.toFiniteUnion s T ∘ₘ beta =
      visitUnionGreenKernel hH hLE hlam hLam A (visitWaitingUnion c J) s T ∘ₘ beta +
        visitUnionGreenKernel hH hLE hlam hLam A J.toFiniteUnion s T ∘ₘ gamma ∧
    visitUnionExitKernel hH hLE hlam hLam A J.toFiniteUnion s T ∘ₘ beta =
      (visitUnionExitKernel hH hLE hlam hLam A (visitWaitingUnion c J) s T ∘ₘ beta).restrict
        (finiteUnionExitSet J.toFiniteUnion s T) +
        visitUnionExitKernel hH hLE hlam hLam A J.toFiniteUnion s T ∘ₘ gamma := by
  have hsub : (visitWaitingUnion c J).carrier ⊆ J.toFiniteUnion.carrier := by
    rw [visitWaitingUnion_carrier, Interval.toFiniteUnion_carrier]
    exact sdiff_subset
  have _h_xinl_0 : ∀ᵐ p ∂visitOutgoingPiece hH hLE hlam hLam A c J s T P n, p ∈ visitPoleSet (visitWaitingUnion c J) s T := by
      exact (
    visitBeta_ae_waitingPole P c J s T _ _ n
    )
  have h := visitUnion_nested hH hLE hlam hLam A (visitWaitingUnion c J) J.toFiniteUnion
    hsub s T hT (visitOutgoingPiece hH hLE hlam hLam A c J s T P n)
    _h_xinl_0
  simpa only [visitWaiting_internalExit, visitEntrancePiece, visitGamma,
    visitOutgoingPiece, visitBeta] using h

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
