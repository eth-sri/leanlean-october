module

public import HypoellipticAleksandrov.KineticAleksandrov.Decay.MaxPrincipleCalculus
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring

/-!
# Strict terminal perturbation of the transported operator

The perturbation changes only the first time derivative. In particular it
requires no mixed or second time derivative.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Decay
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic

/-- Subtract a positive affine function of remaining time. -/
def maximumTerminalTilt {d : ℕ} (u : KineticPoint d → ℝ) (ε T : ℝ) :
    KineticPoint d → ℝ := fun p => u p - ε * (T - p.time)

variable {d : ℕ} (u : KineticPoint d → ℝ) (ε T : ℝ) (p : KineticPoint d)

/-- The diffused Hessian is unchanged by the terminal perturbation. -/
theorem diffusedHessian_maximumTerminalTilt  :
    diffusedHessian (maximumTerminalTilt u ε T) p = diffusedHessian u p := by
  have heq : (fun y : PDE.Vec d => kineticPositionGradient
      (maximumTerminalTilt u ε T) ⟨p.time, y, p.velocity⟩) =
      fun y => kineticPositionGradient u ⟨p.time, y, p.velocity⟩ := by
    funext y
    ext i
    exact congrArg (fun L : PDE.Vec d →L[ℝ] ℝ => L _)
      (fderiv_sub_const (𝕜 := ℝ) (f := fun v => u _)
        (x := y) (ε * (T - p.time)))
  aesop

/-- The transported gradient is unchanged by the terminal perturbation. -/
theorem kineticVelocityGradient_maximumTerminalTilt  :
    kineticVelocityGradient (maximumTerminalTilt u ε T) p = kineticVelocityGradient u p := by
  ext i
  exact congrArg (fun L : PDE.Vec d →L[ℝ] ℝ => L _)
    (fderiv_sub_const (𝕜 := ℝ) (f := fun z => u _)
      (x := p.velocity) (ε * (T - p.time)))

/-- The first time derivative gains ε under the terminal perturbation. -/
theorem kineticTimeDerivative_maximumTerminalTilt  {u : KineticPoint d → ℝ}
    {p : KineticPoint d}
    (hu : DifferentiableAt ℝ (fun t => u ⟨t, p.position, p.velocity⟩) p.time)
    (ε T : ℝ) :
    kineticTimeDerivative (maximumTerminalTilt u ε T) p = kineticTimeDerivative u p + ε := by
  have hd : HasDerivAt (fun t => maximumTerminalTilt u ε T ⟨t, p.position, p.velocity⟩)
      (kineticTimeDerivative u p + ε) p.time := by
    convert hu.hasDerivAt.sub
      ((hasDerivAt_const (x := p.time) (c := ε)).mul
        ((hasDerivAt_const (x := p.time) (c := T)).sub (hasDerivAt_id p.time))) using 1
    all_goals aesop
  exact hd.deriv

/-- The terminal perturbation strictly increases the transported operator by ε. -/
theorem transportedForwardOperator_maximumTerminalTilt 
    (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d)
    {u : KineticPoint d → ℝ} {p : KineticPoint d}
    (hu : DifferentiableAt ℝ (fun t => u ⟨t, p.position, p.velocity⟩) p.time)
    (ε T : ℝ) :
    transportedForwardOperator B b (maximumTerminalTilt u ε T) p =
      transportedForwardOperator B b u p + ε := by
  rw [transportedForwardOperator_apply, transportedForwardOperator_apply,
    kineticTimeDerivative_maximumTerminalTilt hu,
    diffusedHessian_maximumTerminalTilt, kineticVelocityGradient_maximumTerminalTilt]
  ring

end HypoellipticAleksandrov.KineticAleksandrov.Decay
