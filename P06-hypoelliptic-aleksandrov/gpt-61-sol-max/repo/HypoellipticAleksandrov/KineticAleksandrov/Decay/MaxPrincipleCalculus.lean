module

import HypoellipticAleksandrov.Parabolic.ScalarClassical
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.Linarith

public import HypoellipticAleksandrov.KineticAleksandrov.Operator
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import HypoellipticAleksandrov.Parabolic.MinimumPrinciple
import all HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonCalculus
import all HypoellipticAleksandrov.KineticAleksandrov.Lieberman.TerminalLift
import all HypoellipticAleksandrov.Parabolic.Derivatives
import all HypoellipticAleksandrov.Parabolic.ScalarMaximum

open private HypoellipticAleksandrov.Parabolic.scalarSpatialHessian_quadratic_eq from HypoellipticAleksandrov.Parabolic.ScalarMaximum
open private HypoellipticAleksandrov.KineticAleksandrov.Lieberman.scalarSpatialHessian_apply_eq_sndFDeriv from HypoellipticAleksandrov.KineticAleksandrov.Lieberman.TerminalLift
open private HypoellipticAleksandrov.KineticAleksandrov.hasDerivAt_deriv_restrict_affine_line_of_contDiffAt from HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonCalculus
open private HypoellipticAleksandrov.Parabolic.neg_scalarSpatialHessian_posSemidef_of_spatial_localMax from HypoellipticAleksandrov.Parabolic.ScalarMaximum
open private HypoellipticAleksandrov.Parabolic.hasDerivAt_fderiv_restrict_affine_line from HypoellipticAleksandrov.Parabolic.Derivatives
open private HypoellipticAleksandrov.Parabolic.deriv_deriv_nonpos_of_isLocalMax from HypoellipticAleksandrov.Parabolic.Derivatives
open private HypoellipticAleksandrov.KineticAleksandrov.fderiv_fderiv_apply_nonpos_of_isLocalMax_affineLine from HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonCalculus
open private HypoellipticAleksandrov.Parabolic.matrixContraction_nonpos_of_psd_neg from HypoellipticAleksandrov.Parabolic.ScalarMaximum
open private HypoellipticAleksandrov.Parabolic.scalarSpatialHessian_isSymm_of_contDiffAt from HypoellipticAleksandrov.Parabolic.ScalarMaximum
open private HypoellipticAleksandrov.Parabolic.hasDerivAt_affine_line from HypoellipticAleksandrov.Parabolic.Derivatives


/-!
# Pointwise calculus for the transported moving-domain maximum principle

Scalar Hessian calculations are applied to the diffused slice. No mixed or
second time derivatives are required.
-/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Decay
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open Filter Matrix
open scoped MatrixOrder Topology

































/-- A positive semidefinite diffusion contracts the Hessian at a diffused
slice maximum to a nonpositive scalar. -/
theorem diffused_contraction_nonpos_of_localMax {d : ℕ}
    {u : HypoellipticAleksandrov.KineticScalarField d} {p : KineticPoint d} {A : PDE.Mat d}
    (hu : ContDiffAt ℝ 2 (fun y => u ⟨p.time, y, p.velocity⟩) p.position)
    (hmax : IsLocalMax (fun y => u ⟨p.time, y, p.velocity⟩) p.position)
    (hA : A.PosSemidef) :
    matrixContraction A (diffusedHessian u p) ≤ 0 := by


  rw [← (show scalarSpatialHessian (fun z => u ⟨z.1, z.2, p.velocity⟩) (p.time, p.position) = diffusedHessian u p from rfl)]
  exact _root_.HypoellipticAleksandrov.Parabolic.matrixContraction_nonpos_of_psd_neg hA
    (_root_.HypoellipticAleksandrov.Parabolic.neg_scalarSpatialHessian_posSemidef_of_spatial_localMax hu hmax)
    (_root_.HypoellipticAleksandrov.Parabolic.scalarSpatialHessian_isSymm_of_contDiffAt hu)

/-- A differentiable transported slice has zero gradient at a local maximum. -/
theorem transported_gradient_eq_zero_of_localMax {d : ℕ}
    {u : HypoellipticAleksandrov.KineticScalarField d} {p : KineticPoint d}
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
    {B : FullKineticCoefficient d} {b : PDE.VectorField d}
    {u : HypoellipticAleksandrov.KineticScalarField d} {p : KineticPoint d}
    (htime : kineticTimeDerivative u p ≤ 0)
    (hv : ContDiffAt ℝ 2 (fun y => u ⟨p.time, y, p.velocity⟩) p.position)
    (hz : DifferentiableAt ℝ (fun z => u ⟨p.time, p.position, z⟩) p.velocity)
    (hvmax : IsLocalMax (fun y => u ⟨p.time, y, p.velocity⟩) p.position)
    (hzmax : IsLocalMax (fun z => u ⟨p.time, p.position, z⟩) p.velocity)
    (hB : (B p.time p.position p.velocity).PosSemidef) :
    transportedForwardOperator B b u p ≤ 0 := by

  rw [transportedForwardOperator_apply,
    transported_gradient_eq_zero_of_localMax hz hzmax]
  simp only [PDE.vecDot, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
  exact add_nonpos htime (diffused_contraction_nonpos_of_localMax hv hvmax hB)

end HypoellipticAleksandrov.KineticAleksandrov.Decay
