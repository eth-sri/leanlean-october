module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionMixtures
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionSupport
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
theorem enlargedEntrance_nested (hP : s ≤ P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier) (n : ℕ) :
    let gamma := enlargedVisitEntrance A c J s T P n
    let beta := enlargedVisitOutgoing A c J s T P n
    enlargedVisitGreenKernel A J.toFiniteUnion T ∘ₘ gamma =
      enlargedVisitGreenKernel A (visitActiveUnion c J) T ∘ₘ gamma +
        enlargedVisitGreenKernel A J.toFiniteUnion T ∘ₘ beta ∧
    enlargedVisitExitKernel A J.toFiniteUnion T ∘ₘ gamma =
      (enlargedVisitExitKernel A (visitActiveUnion c J) T ∘ₘ gamma).restrict
        (finiteUnionExitSet J.toFiniteUnion s T) +
        enlargedVisitExitKernel A J.toFiniteUnion T ∘ₘ beta := by
  have hsub : (visitActiveUnion c J).carrier ⊆ J.toFiniteUnion.carrier := by
    rw [visitActiveUnion_carrier, Interval.toFiniteUnion_carrier]
    exact inter_subset_right
  have h := enlargedUnion_nested A (visitActiveUnion c J) J.toFiniteUnion
    hsub s T hT (enlargedVisitEntrance A c J s T P n)
    ((enlargedEntrance_ae_activePole A c J s T P hP n).mono
      (fun _ hp => hp.2))
    ((enlargedEntrance_ae_activePole A c J s T P hP n).mono
      (fun _ hp => hp.1))
  simpa only [visitActive_internalExit, enlargedVisitOutgoing, visitBeta,
    enlargedVisitEntrance] using h

/-- Every actual waiting visit has the genuine outer Green and exit splitting. -/
theorem enlargedOutgoing_nested (n : ℕ) :
    let beta := enlargedVisitOutgoing A c J s T P n
    let gamma := enlargedVisitEntrance A c J s T P (n + 1)
    enlargedVisitGreenKernel A J.toFiniteUnion T ∘ₘ beta =
      enlargedVisitGreenKernel A (visitWaitingUnion c J) T ∘ₘ beta +
        enlargedVisitGreenKernel A J.toFiniteUnion T ∘ₘ gamma ∧
    enlargedVisitExitKernel A J.toFiniteUnion T ∘ₘ beta =
      (enlargedVisitExitKernel A (visitWaitingUnion c J) T ∘ₘ beta).restrict
        (finiteUnionExitSet J.toFiniteUnion s T) +
        enlargedVisitExitKernel A J.toFiniteUnion T ∘ₘ gamma := by
  have hsub : (visitWaitingUnion c J).carrier ⊆ J.toFiniteUnion.carrier := by
    rw [visitWaitingUnion_carrier, Interval.toFiniteUnion_carrier]
    exact sdiff_subset
  have h := enlargedUnion_nested A (visitWaitingUnion c J) J.toFiniteUnion
    hsub s T hT (enlargedVisitOutgoing A c J s T P n)
    ((enlargedOutgoing_ae_waitingPole A c J s T P n).mono
      (fun _ hp => hp.2))
    ((enlargedOutgoing_ae_waitingPole A c J s T P n).mono
      (fun _ hp => hp.1))
  simpa only [visitWaiting_internalExit, enlargedVisitEntrance, visitGamma,
    enlargedVisitOutgoing, visitBeta] using h

end

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
