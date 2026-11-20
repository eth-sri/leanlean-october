module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitTimeIntegrals
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassOutgoing
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripKernelIntegral
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreStartBandVisits

/-! # The actual short-time quadratic identity integrated over entrance measures -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory

section
variable {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T b : ℝ)
  (P : Point)
include lam Lam A c b

/-- The localized quadratic is integrable against every actual entrance measure. -/
theorem visitTimeQuadratic_integrable_entrance (n : ℕ) :
    Integrable (fun p => visitTimeCutoff b c.r c.positive p.time *
      visitQuadratic c (p.velocity 0))
      (visitEntrancePiece A c J s T P n) := by
  apply visitTimeQuadratic_integrable_of_active_support
  exact (visitGamma_ae_closedEntrance P c J s T _ _ n).mono
    (fun p hp => subset_closure (_root_.HypoellipticAleksandrov.KineticAleksandrov.Autonomous.enlargedEntrance_subset_active c hp))

/-- The localized quadratic also has exactly zero outgoing internal-face integral. -/
theorem visitTimeQuadratic_outgoing_integral_zero (n : ℕ) :
    (∫ p, visitTimeCutoff b c.r c.positive p.time * visitQuadratic c (p.velocity 0)
      ∂visitOutgoingPiece A c J s T P n) = 0 := by
  have hz : (fun p => visitTimeCutoff b c.r c.positive p.time *
      visitQuadratic c (p.velocity 0)) =ᵐ[
        visitOutgoingPiece A c J s T P n] 0 := by
    filter_upwards [visitQuadratic_ae_zero_outgoing A c J s T P n] with p hp
    rw [hp, mul_zero]
    rfl
  rw [integral_congr_ae hz]
  exact integral_zero _ _

/-- Every actual entrance satisfies the genuine integrated short-time quadratic identity. -/
theorem visitTimeQuadratic_entrance_green_identity
    (hP : s < P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier) (n : ℕ) :
    let mu := visitEntrancePiece A c J s T P n
    let E := visitUnionExitKernel A (visitActiveUnion c J) s T
    let G := visitUnionGreenKernel A (visitActiveUnion c J) s T
    let f := fun q : Point => visitTimeCutoff b c.r c.positive q.time *
      visitQuadratic c (q.velocity 0)
    (∫ p, f p ∂mu) = (∫ p, f p ∂E ∘ₘ mu) -
      ∫ p, forwardScalarOperator A.a f p ∂G ∘ₘ mu := by
  dsimp only
  refine integral_eq_comp_sub (visitTimeQuadratic_integrable_activeExitMixture A c J s T b _)
    (visitTimeQuadratic_operator_integrable_activeGreenMixture A c J s T b _) ?_
  filter_upwards [visitEntrancePiece_ae_activePole A c J s T P hP n] with p hp
  simpa only [visitUnionExitKernel, visitUnionGreenKernel, visitExtendKernel_apply_mem hp, visitPoleInclusion] using
    (show _ from visitTimeQuadratic_active_identity A c J b T (visitPoleInclusion _ s T ⟨p, hp⟩))

end

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
