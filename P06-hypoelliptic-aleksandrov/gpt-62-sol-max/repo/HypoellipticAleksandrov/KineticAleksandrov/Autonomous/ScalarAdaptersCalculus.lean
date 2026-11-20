module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ScalarAdapters
public import PDEFoundation.Sobolev.OneDimensional.SmoothTransport
import HypoellipticAleksandrov.KineticAleksandrov.Interval.KillingJets

/-! # Total scalar derivative bridges for the one-dimensional kinetic carrier -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov.Parabolic

section
variable (u : Point → ℝ) (p : Point)

/-- Native position differentiation is the scalar position derivative. -/
theorem kineticPositionGradient_scalar :
    kineticPositionGradient u p 0 =
      deriv (fun x => u ⟨p.time, fun _ => x, p.velocity⟩) (p.position 0) := (_root_.HypoellipticAleksandrov.KineticAleksandrov.Interval.scalar_deriv_eq_native (fun x => u ⟨p.time, x, p.velocity⟩) p.position).symm

/-- Native velocity differentiation is the scalar velocity derivative. -/
theorem kineticVelocityGradient_scalar :
    kineticVelocityGradient u p 0 =
      deriv (fun v => u ⟨p.time, p.position, fun _ => v⟩) (p.velocity 0) := (_root_.HypoellipticAleksandrov.KineticAleksandrov.Interval.scalar_deriv_eq_native (fun v => u ⟨p.time, p.position, v⟩) p.velocity).symm

/-- The native velocity Hessian is the second scalar velocity derivative. -/
theorem kineticVelocityHessian_scalar :
    kineticVelocityHessian u p 0 0 =
      deriv (deriv (fun v => u ⟨p.time, p.position, fun _ => v⟩)) (p.velocity 0) := by
  let g : PDE.Vec 1 → PDE.Vec 1 :=
    fun v => kineticVelocityGradient u ⟨p.time, p.position, v⟩
  have hg : (fun t : ℝ => g (fun _ => t) 0) =
      deriv (fun w => u ⟨p.time, p.position, fun _ => w⟩) := by
    funext t
    exact kineticVelocityGradient_scalar u ⟨p.time, p.position, fun _ => t⟩
  have he := _root_.HypoellipticAleksandrov.KineticAleksandrov.Interval.scalar_deriv_eq_native (fun v => g v 0) p.velocity
  rw [hg] at he
  have hi : (fderiv ℝ (fun v => g v 0) p.velocity) (PDE.basisVec 0) =
      (fderiv ℝ g p.velocity (PDE.basisVec 0)) 0 := by
    let E := PDE.scalarToVecOneContinuousLinearEquiv.symm
    change (fderiv ℝ (E ∘ g) p.velocity) (PDE.basisVec 0) = _
    rw [E.comp_fderiv]
    rfl
  exact hi.symm.trans he.symm

end

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
