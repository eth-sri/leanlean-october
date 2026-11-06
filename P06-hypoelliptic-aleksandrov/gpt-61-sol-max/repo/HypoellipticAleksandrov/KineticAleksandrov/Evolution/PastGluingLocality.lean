module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonCalculus

/-! # Locality of the viscous kinetic operator

Equality near a point preserves every literal slice derivative in the operator.
-/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov.Parabolic Filter
open scoped Topology

variable {n : ℕ}

section
variable {u v : PDE.ScalarField n} {x : PDE.Vec n} (h : u =ᶠ[𝓝 x] v)

include h
/-- Equal scalar germs have equal classical gradient germs. -/
theorem pastGluing_gradient_germ   : PDE.classicalGradient u =ᶠ[𝓝 x] PDE.classicalGradient v := by
  filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
  funext i
  exact congrArg (fun L : PDE.Vec n →L[ℝ] ℝ => L (PDE.basisVec i)) hy

/-- A scalar germ determines its gradient and differentiated-gradient values. -/
theorem pastGluing_gradient_hessian_eq   :
    PDE.classicalGradient u x = PDE.classicalGradient v x ∧
      fderiv ℝ (PDE.classicalGradient u) x = fderiv ℝ (PDE.classicalGradient v) x :=
  ⟨(pastGluing_gradient_germ h).eq_of_nhds, (pastGluing_gradient_germ h).fderiv_eq⟩
end


/-- Equal kinetic germs have equal viscous operator values, without regularity assumptions. -/
theorem viscousTransportedOperator_congr_germ
    (B : FullKineticCoefficient n) (b : PDE.VectorField n) (ε : ℝ)
    {u v : HypoellipticAleksandrov.KineticScalarField n} {p : KineticPoint n} (h : u =ᶠ[𝓝 p] v) :
    viscousTransportedOperator B b ε u p = viscousTransportedOperator B b ε v p := by
  have ht : (fun s => u ⟨s, p.position, p.velocity⟩) =ᶠ[𝓝 p.time]
      (fun s => v ⟨s, p.position, p.velocity⟩) :=
    h.comp_tendsto ((KineticPoint.continuous_mk continuous_id continuous_const
      continuous_const).tendsto p.time)
  have hy : (fun y => u ⟨p.time, y, p.velocity⟩) =ᶠ[𝓝 p.position]
      (fun y => v ⟨p.time, y, p.velocity⟩) :=
    h.comp_tendsto ((KineticPoint.continuous_mk continuous_const continuous_id
      continuous_const).tendsto p.position)
  have hz : (fun z => u ⟨p.time, p.position, z⟩) =ᶠ[𝓝 p.velocity]
      (fun z => v ⟨p.time, p.position, z⟩) :=
    h.comp_tendsto ((KineticPoint.continuous_mk continuous_const continuous_const
      continuous_id).tendsto p.velocity)

  have ez := pastGluing_gradient_hessian_eq hz
  have hd : diffusedHessian u p = diffusedHessian v p := by
    ext i j
    simp only [diffusedHessian_apply, kineticPositionGradient]
    exact congrArg (fun L : PDE.Vec n →L[ℝ] PDE.Vec n => L (PDE.basisVec i) j) (pastGluing_gradient_hessian_eq hy).2
  simp only [viscousTransportedOperator, transportedForwardOperator, kineticTimeDerivative,
    kineticVelocityGradient, kineticVelocityHessian, ht.deriv_eq, hd, ez.1, ez.2]

end HypoellipticAleksandrov.KineticAleksandrov
