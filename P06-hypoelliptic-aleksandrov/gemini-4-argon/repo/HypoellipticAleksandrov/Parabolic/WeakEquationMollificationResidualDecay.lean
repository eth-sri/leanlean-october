module

public import HypoellipticAleksandrov.Parabolic.WeakEquationMollification
public import HypoellipticAleksandrov.Parabolic.ParabolicConvolutionCommutator

/-!
# Compact decay of weak-equation mollification residuals

This module identifies the explicit residual of a supplied global weak jet
with the parabolic convolution commutator and obtains its compact finite-norm
decay from Borel elliptic coefficient data.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Filter MeasureTheory Set
open scoped ENNReal Topology

/- The residual of weak-equation mollification is definitionally the
coefficient--Hessian parabolic convolution commutator. -/
@[simp] theorem weakEquationMollificationResidual_eq_parabolicConvolutionCommutator
    {d p} (Aext : CoefficientField d)
    (g : ParabolicW12Function d Set.univ p) (n : Nat) :
    weakEquationMollificationResidual Aext g n =
      parabolicConvolutionCommutator Aext g.velocityHessian n :=
  rfl

/- The explicit weak-equation mollification residual of a supplied global
weak jet converges to zero in finite parabolic norm on every compact carrier. -/
end HypoellipticAleksandrov.Parabolic
