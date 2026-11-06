module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitTimeIntegrals
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassOutgoing
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripKernelIntegral

/-! # The actual short-time quadratic identity integrated over entrance measures -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory

/- The localized quadratic is integrable against every actual entrance measure. -/
theorem visitTimeQuadratic_outgoing_integral_zero
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam } (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T b : ℝ)
    (P : Point) (n : ℕ) :
    (∫ p, visitTimeCutoff b c.r c.positive p.time * visitQuadratic c (p.velocity 0)
      ∂visitOutgoingPiece hH hLE hlam hLam A c J s T P n) = 0 := by
  have hz : (fun p => visitTimeCutoff b c.r c.positive p.time *
      visitQuadratic c (p.velocity 0)) =ᵐ[
        visitOutgoingPiece hH hLE hlam hLam A c J s T P n] 0 := by
    filter_upwards [visitQuadratic_ae_zero_outgoing hH hLE hlam hLam A c J s T P n] with p hp
    rw [hp, mul_zero]
    rfl
  rw [integral_congr_ae hz]
  exact integral_zero _ _

/- Every actual entrance satisfies the genuine integrated short-time quadratic identity. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
