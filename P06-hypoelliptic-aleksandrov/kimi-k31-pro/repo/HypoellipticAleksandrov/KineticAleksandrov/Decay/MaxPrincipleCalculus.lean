module

import HypoellipticAleksandrov.Parabolic.ScalarClassical
public import HypoellipticAleksandrov.Parabolic.ScalarMaximum
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.Linarith

public import HypoellipticAleksandrov.KineticAleksandrov.Operator

/-!
# Pointwise calculus for the transported moving-domain maximum principle

Scalar Hessian calculations are applied to the diffused slice. No mixed or
second time derivatives are required.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Decay
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open Filter Set Matrix
open scoped MatrixOrder Topology

/-- A positive semidefinite diffusion contracts the Hessian at a diffused
slice maximum to a nonpositive scalar. -/
theorem diffused_contraction_nonpos_of_localMax {d : ℕ}
    {u : KineticPoint d → ℝ} {p : KineticPoint d} {A : PDE.Mat d}
    (hu : ContDiffAt ℝ 2 (fun y => u ⟨p.time, y, p.velocity⟩) p.position)
    (hmax : IsLocalMax (fun y => u ⟨p.time, y, p.velocity⟩) p.position)
    (hA : A.PosSemidef) :
    matrixContraction A (diffusedHessian u p) ≤ 0 := by
  let f : TimeVelocity d → ℝ := fun z => u ⟨z.1, z.2, p.velocity⟩
  have heq : scalarSpatialHessian f (p.time, p.position) = diffusedHessian u p := rfl
  rw [← heq]
  exact matrixContraction_nonpos_of_psd_neg hA
    (neg_scalarSpatialHessian_posSemidef_of_spatial_localMax hu hmax)
    (scalarSpatialHessian_isSymm_of_contDiffAt hu)

/-- A differentiable transported slice has zero gradient at a local maximum. -/
theorem transported_gradient_eq_zero_of_localMax {d : ℕ}
    {u : KineticPoint d → ℝ} {p : KineticPoint d}
    (hu : DifferentiableAt ℝ (fun z => u ⟨p.time, p.position, z⟩) p.velocity)
    (hmax : IsLocalMax (fun z => u ⟨p.time, p.position, z⟩) p.velocity) :
    kineticVelocityGradient u p = 0 := by
  ext i
  change fderiv ℝ (fun z => u ⟨p.time, p.position, z⟩)
    p.velocity (PDE.basisVec i) = 0
  rw [hmax.hasFDerivAt_eq_zero hu.hasFDerivAt]
  rfl

/-- Pointwise maximum calculus for the transported operator, with only the
anisotropic derivatives used by the source. -/
theorem transportedForwardOperator_nonpos_of_slice_localMax {d : ℕ}
    {B : FullKineticCoefficient d} {b : PDE.Vec d → PDE.Vec d}
    {u : KineticPoint d → ℝ} {p : KineticPoint d}
    (htime : kineticTimeDerivative u p ≤ 0)
    (hv : ContDiffAt ℝ 2 (fun y => u ⟨p.time, y, p.velocity⟩) p.position)
    (hz : DifferentiableAt ℝ (fun z => u ⟨p.time, p.position, z⟩) p.velocity)
    (hvmax : IsLocalMax (fun y => u ⟨p.time, y, p.velocity⟩) p.position)
    (hzmax : IsLocalMax (fun z => u ⟨p.time, p.position, z⟩) p.velocity)
    (hB : (B p.time p.position p.velocity).PosSemidef) :
    transportedForwardOperator B b u p ≤ 0 := by
  have hdiff := diffused_contraction_nonpos_of_localMax hv hvmax hB
  rw [transportedForwardOperator_apply,
    transported_gradient_eq_zero_of_localMax hz hzmax]
  simp only [PDE.vecDot, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
  exact add_nonpos htime hdiff

end HypoellipticAleksandrov.KineticAleksandrov.Decay
