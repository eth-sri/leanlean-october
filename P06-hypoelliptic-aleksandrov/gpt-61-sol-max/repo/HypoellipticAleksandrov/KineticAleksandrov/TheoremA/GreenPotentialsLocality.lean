module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ReflectionCalculus

/-! # Locality of the classical kinetic operator -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.TheoremA
open Parabolic Filter
open scoped Topology

/-- The total classical kinetic operator depends only on a neighbourhood of its point. -/
theorem forwardKineticOperator_eq_of_eventuallyEq {d : ℕ}
    (A : FullKineticCoefficient d) {u v : HypoellipticAleksandrov.KineticScalarField d} {P : KineticPoint d}
    (h : u =ᶠ[𝓝 P] v) : forwardKineticOperator A u P = forwardKineticOperator A v P := by
  let sharedTerm_773cfd3fe7 := ((fun y => u ⟨P.time, P.position, y⟩))
  let sharedTerm_92ff390a09 := ((fun y => v ⟨P.time, P.position, y⟩))
  have ht : (fun t => u ⟨t, P.position, P.velocity⟩) =ᶠ[𝓝 P.time]
      (fun t => v ⟨t, P.position, P.velocity⟩) :=
    h.comp_tendsto ((ContinuousAt.tendsto
  (Continuous.continuousAt (KineticPoint.continuous_mk continuous_id continuous_const continuous_const))))
  have hx : (fun x => u ⟨P.time, x, P.velocity⟩) =ᶠ[𝓝 P.position]
      (fun x => v ⟨P.time, x, P.velocity⟩) :=
    h.comp_tendsto ((ContinuousAt.tendsto
  (Continuous.continuousAt (KineticPoint.continuous_mk continuous_const continuous_id continuous_const))))
  have hv : sharedTerm_773cfd3fe7 =ᶠ[𝓝 P.velocity]
      sharedTerm_92ff390a09 :=
    h.comp_tendsto ((ContinuousAt.tendsto
  (Continuous.continuousAt (KineticPoint.continuous_mk continuous_const continuous_const continuous_id))))
  have hgrad : kineticPositionGradient u P = kineticPositionGradient v P := by
    ext i
    exact congrArg (fun L => L (PDE.basisVec i)) (hx.fderiv_eq (𝕜 := ℝ))
  have hvg : (fun w => PDE.classicalGradient sharedTerm_773cfd3fe7 w)
      =ᶠ[𝓝 P.velocity]
      (fun w => PDE.classicalGradient sharedTerm_92ff390a09 w) := by
    filter_upwards [hv.fderiv (𝕜 := ℝ)] with w hw
    ext i
    exact congrArg (fun L => L (PDE.basisVec i)) hw
  have hh : kineticVelocityHessian u P = kineticVelocityHessian v P := by
    ext i j
    exact congrArg (fun L => L (PDE.basisVec i) j) (hvg.fderiv_eq (𝕜 := ℝ))
  rw [forwardKineticOperator_apply, forwardKineticOperator_apply, hgrad, hh]
  have htime : kineticTimeDerivative u P = kineticTimeDerivative v P := ht.deriv_eq
  rw [htime]

end HypoellipticAleksandrov.KineticAleksandrov.TheoremA
