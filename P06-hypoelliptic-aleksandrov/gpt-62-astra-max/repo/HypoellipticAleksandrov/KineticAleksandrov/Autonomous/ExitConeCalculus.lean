module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitConeTransition

/-! # Exact kinetic calculus for smooth functions of affine transport coordinates -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Parabolic
open SectionTwo TheoremA Evolution

variable (a : ℝ → ℝ → ℝ) (alpha beta gamma : ℝ) (p : Point)

include alpha beta gamma p in
/-- The affine transport coordinate used to detect finite-speed violations. -/
def reconstructionConeCoordinate : ℝ :=
  alpha * p.time + beta * p.position 0 + gamma

/-- Composition with the cone transition is a genuine globally smooth physical test. -/
theorem reconstructionConeProbe_smooth :
    ContDiff ℝ (⊤ : ℕ∞) ((expNegInvGlue ∘ reconstructionConeCoordinate alpha beta gamma) ∘
      reconstructionPhysicalHomeomorph) := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun x => expNegInvGlue
    (alpha * Evolution.timeCoord 1 x + beta * transportedCoord 1 x 0 + gamma))
  fun_prop

/-- A pure transport-coordinate probe has no velocity Hessian contribution. -/
theorem reconstructionConeProbe_operator :
    forwardScalarOperator a (expNegInvGlue ∘ reconstructionConeCoordinate alpha beta gamma) p =
      (alpha + p.velocity 0 * beta) *
        deriv expNegInvGlue (reconstructionConeCoordinate alpha beta gamma p) := by
  have hd (x : ℝ) :=
    ((expNegInvGlue.contDiff : ContDiff ℝ (⊤ : ℕ∞) expNegInvGlue).differentiable (by simp) x)
  have ht : kineticTimeDerivative
      (expNegInvGlue ∘ reconstructionConeCoordinate alpha beta gamma) p =
      deriv expNegInvGlue (reconstructionConeCoordinate alpha beta gamma p) * alpha := by
    simpa only [kineticTimeDerivative, reconstructionConeCoordinate, Function.comp_apply,
      id_eq, mul_one] using! ((hd _).hasDerivAt.comp p.time ((((hasDerivAt_id p.time).const_mul alpha).add_const (beta * p.position 0)).add_const gamma)).deriv
  have hx : kineticPositionGradient
      (expNegInvGlue ∘ reconstructionConeCoordinate alpha beta gamma) p 0 =
      deriv expNegInvGlue (reconstructionConeCoordinate alpha beta gamma p) * beta := by
    rw [kineticPositionGradient_scalar]
    simpa only [reconstructionConeCoordinate, Function.comp_apply, id_eq, mul_one] using! ((hd _).hasDerivAt.comp (p.position 0) ((((hasDerivAt_id (p.position 0)).const_mul beta).const_add (alpha * p.time)).add_const gamma)).deriv
  have hv : kineticVelocityHessian
      (expNegInvGlue ∘ reconstructionConeCoordinate alpha beta gamma) p 0 0 = 0 := by
    rw [kineticVelocityHessian_scalar]
    change deriv (deriv (fun _ : ℝ => expNegInvGlue
      (alpha * p.time + beta * p.position 0 + gamma))) (p.velocity 0) = 0
    have hh : deriv (fun _ : ℝ => expNegInvGlue
        (alpha * p.time + beta * p.position 0 + gamma)) = fun _ => 0 :=
      funext (fun x => deriv_const x _)
    simp
  unfold forwardScalarOperator
  rw [ht, hx, hv]
  ring

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
