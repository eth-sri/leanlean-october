module

public import HypoellipticAleksandrov.Parabolic.ScalarDirichletComparison

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation

open HypoellipticAleksandrov.Parabolic Filter Set Matrix
open scoped MatrixOrder Topology

/-- Scalar classical regularity is stable under subtraction. -/
theorem isScalarC12On_sub {n : ℕ} {u v : TimeVelocity n → ℝ}
    {D : Set (TimeVelocity n)} (hu : IsScalarC12On u D) (hv : IsScalarC12On v D) :
    IsScalarC12On (fun q => u q - v q) D :=
  Parabolic.LocalHolder.isScalarC12On_sub hu hv

/-- The scalar zero-order operator is linear on classical functions. -/
theorem scalarParabolicZeroOrderOperator_sub {n : ℕ}
    (a : CoefficientField n) (b : ℝ → PDE.Vec n → PDE.Vec n)
    (c : ℝ → PDE.Vec n → ℝ) {u v : TimeVelocity n → ℝ}
    {D : Set (TimeVelocity n)} (hu : IsScalarC12On u D) (hv : IsScalarC12On v D)
    {z : TimeVelocity n} (hz : z ∈ D) :
    scalarParabolicZeroOrderOperator a b c (fun q => u q - v q) z =
      scalarParabolicZeroOrderOperator a b c u z -
        scalarParabolicZeroOrderOperator a b c v z :=
  Parabolic.LocalHolder.scalarParabolicZeroOrderOperator_sub a b c hu hv hz

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
