module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ReflectionCalculus

/-! # Locality of the classical kinetic operator -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.TheoremA
open Parabolic Filter
open scoped Topology

/-- The total classical kinetic operator depends only on a neighbourhood of its point. -/
theorem forwardKineticOperator_eq_of_eventuallyEq {d : ℕ}
    (A : FullKineticCoefficient d) {u v : KineticPoint d → ℝ} {P : KineticPoint d}
    (h : u =ᶠ[𝓝 P] v) : forwardKineticOperator A u P = forwardKineticOperator A v P := by
  have ht : (fun t => u _) =ᶠ[𝓝 P.time]
      (fun t => v _) :=
    h.comp_tendsto (by
      simpa using (KineticPoint.continuous_mk continuous_id continuous_const
        continuous_const).continuousAt.tendsto (x := P.time))
  have hx : (fun x => u _) =ᶠ[𝓝 P.position]
      (fun x => v _) :=
    h.comp_tendsto (by
      simpa using (KineticPoint.continuous_mk continuous_const continuous_id
        continuous_const).continuousAt.tendsto (x := P.position))
  have hv : (fun w => u _) =ᶠ[𝓝 P.velocity]
      (fun w => v _) :=
    h.comp_tendsto (by
      simpa using (KineticPoint.continuous_mk continuous_const continuous_const
        continuous_id).continuousAt.tendsto (x := P.velocity))
  have hgrad : kineticPositionGradient u P = kineticPositionGradient v P := by
    ext i
    exact congrArg (fun L => L (PDE.basisVec i)) (hx.fderiv_eq (𝕜 := ℝ))
  have hvg : (fun w => PDE.classicalGradient (fun y => u ⟨P.time, P.position, y⟩) w)
      =ᶠ[𝓝 P.velocity]
      (fun w => PDE.classicalGradient (fun y => v ⟨P.time, P.position, y⟩) w) := by
    filter_upwards [hv.fderiv (𝕜 := ℝ)] with w hw
    aesop
  have hh : kineticVelocityHessian u P = kineticVelocityHessian v P := by
    ext i j
    exact congrArg (fun L => L (PDE.basisVec i) j) (hvg.fderiv_eq (𝕜 := ℝ))
  rw [forwardKineticOperator_apply, forwardKineticOperator_apply, hgrad, hh]
  have htime : kineticTimeDerivative u P = kineticTimeDerivative v P := ht.deriv_eq
  grind

end HypoellipticAleksandrov.KineticAleksandrov.TheoremA
