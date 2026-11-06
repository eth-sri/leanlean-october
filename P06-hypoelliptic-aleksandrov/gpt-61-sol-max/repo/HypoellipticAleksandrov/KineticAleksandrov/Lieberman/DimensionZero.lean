module

public import HypoellipticAleksandrov.KineticAleksandrov.EllipsoidDirichlet
public import HypoellipticAleksandrov.Parabolic.ScalarDirichletData
import HypoellipticAleksandrov.Parabolic.C2ToScalarC12
import Aesop



/-! # The zero-dimensional ellipsoid Dirichlet solution -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Lieberman
open HypoellipticAleksandrov.Parabolic Set

/-- In dimension zero the terminal lift is constant and solves the whole problem. -/
theorem dimension_zero_solution (r₀ r₁ : ℝ) (Q : PDE.Mat 0) (A : CoefficientField 0)
    (b : PDE.TimeVectorField 0) (φ : PDE.ScalarField 0) :
    IsClassicalBackwardDirichletSolution r₀ r₁ (openEllipsoid Q) A b
      (fun _ _ => 0) (fun _ _ => 0) φ (fun _ => 0) (fun z => φ z.2) := by
  have heq : (fun z : TimeVelocity 0 => φ z.2) = fun _ => φ 0 :=
    funext (fun _ => congrArg φ (Subsingleton.elim _ _))
  have hΩ : openEllipsoid Q = univ := by
    ext x
    simp [openEllipsoid, PDE.vecDot]
  rw [heq]
  refine ⟨continuous_const.continuousOn,
    isScalarC12On_of_contDiff_two contDiff_const _, ?_, ?_, ?_⟩
  · simp_all [scalarTimeDerivative, matrixContraction, PDE.vecDot]
  · intro y _
    exact congrArg φ (Subsingleton.elim _ _)
  · aesop

end HypoellipticAleksandrov.KineticAleksandrov.Lieberman
