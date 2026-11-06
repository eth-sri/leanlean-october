module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitConeTransition

/-! # Exact kinetic calculus for smooth functions of affine transport coordinates -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Parabolic
open SectionTwo TheoremA Evolution

/- The affine transport coordinate used to detect finite-speed violations. -/
def reconstructionConeCoordinate (alpha beta gamma : ℝ) (p : Point) : ℝ :=
  alpha * p.time + beta * p.position 0 + gamma

/- Composition with the cone transition is a genuine globally smooth physical test. -/
theorem reconstructionConeProbe_smooth (alpha beta gamma : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) ((expNegInvGlue ∘ reconstructionConeCoordinate alpha beta gamma) ∘
      reconstructionPhysicalHomeomorph) := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun x => expNegInvGlue
    (alpha * Evolution.timeCoord 1 x + beta * transportedCoord 1 x 0 + gamma))
  apply expNegInvGlue.contDiff.comp
  exact ((contDiff_const.mul (Evolution.timeCoord 1).contDiff).add
    (contDiff_const.mul ((contDiff_apply ℝ ℝ (0 : Fin 1)).comp
      (transportedCoord 1).contDiff))).add contDiff_const

/- A pure transport-coordinate probe has no velocity Hessian contribution. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
