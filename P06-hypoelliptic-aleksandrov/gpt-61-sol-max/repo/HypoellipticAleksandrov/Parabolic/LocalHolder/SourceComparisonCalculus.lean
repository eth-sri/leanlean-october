module

public import HypoellipticAleksandrov.Parabolic.ScalarDirichletData
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Add
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import all HypoellipticAleksandrov.KineticAleksandrov.Lieberman.TerminalLift
import all HypoellipticAleksandrov.Parabolic.ScalarDirichletComparison

open private HypoellipticAleksandrov.Parabolic.scalarSpatialHessian_sub from HypoellipticAleksandrov.Parabolic.ScalarDirichletComparison
open private HypoellipticAleksandrov.KineticAleksandrov.Lieberman.scalarSpatialHessian_apply_eq_sndFDeriv from HypoellipticAleksandrov.KineticAleksandrov.Lieberman.TerminalLift
open private HypoellipticAleksandrov.Parabolic.scalarParabolicZeroOrderOperator_sub from HypoellipticAleksandrov.Parabolic.ScalarDirichletComparison
open private HypoellipticAleksandrov.Parabolic.isScalarC12On_sub from HypoellipticAleksandrov.Parabolic.ScalarDirichletComparison
open private HypoellipticAleksandrov.Parabolic.scalarSpatialGradient_sub from HypoellipticAleksandrov.Parabolic.ScalarDirichletComparison
open private HypoellipticAleksandrov.Parabolic.scalarTimeDerivative_sub from HypoellipticAleksandrov.Parabolic.ScalarDirichletComparison


/-! # Classical subtraction for signed source corrections

These local public subtraction lemmas provide the calculus needed to combine positive
Dirichlet solutions without changing the comparison module.
-/

 public section

namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Filter Set
open scoped Topology

/-- Time derivatives commute with subtraction of classical functions. -/
alias scalarTimeDerivative_sub := _root_.HypoellipticAleksandrov.Parabolic.scalarTimeDerivative_sub


/-- Spatial gradients commute with subtraction of classical functions. -/
alias scalarSpatialGradient_sub := _root_.HypoellipticAleksandrov.Parabolic.scalarSpatialGradient_sub





/-- Spatial Hessians commute with subtraction of classical functions. -/
alias scalarSpatialHessian_sub := _root_.HypoellipticAleksandrov.Parabolic.scalarSpatialHessian_sub


/-- The anisotropic classical carrier is closed under subtraction. -/
alias isScalarC12On_sub := _root_.HypoellipticAleksandrov.Parabolic.isScalarC12On_sub


/-- The backward operator is linear on classical functions. -/
alias scalarParabolicZeroOrderOperator_sub := _root_.HypoellipticAleksandrov.Parabolic.scalarParabolicZeroOrderOperator_sub



end HypoellipticAleksandrov.Parabolic.LocalHolder
