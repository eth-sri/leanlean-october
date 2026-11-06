module

public import HypoellipticAleksandrov.Parabolic.ScalarDirichletComparison
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


/-!
# Scalar difference calculus for the occupation comparison

The comparison argument keeps its difference calculus private. This
module exposes the two facts needed to construct the occupation barrier defect.
-/

 public section



namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation

open HypoellipticAleksandrov.Parabolic Filter Set
open scoped MatrixOrder Topology













/-- Scalar classical regularity is stable under subtraction. -/
alias isScalarC12On_sub := _root_.HypoellipticAleksandrov.Parabolic.isScalarC12On_sub


/-- The scalar zero-order operator is linear on classical functions. -/
alias scalarParabolicZeroOrderOperator_sub := _root_.HypoellipticAleksandrov.Parabolic.scalarParabolicZeroOrderOperator_sub



end HypoellipticAleksandrov.KineticAleksandrov.Occupation
