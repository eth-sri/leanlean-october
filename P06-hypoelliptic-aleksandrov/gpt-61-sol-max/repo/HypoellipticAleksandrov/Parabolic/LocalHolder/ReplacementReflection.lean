module

public import HypoellipticAleksandrov.Parabolic.LocalHolder.Replacement
public import HypoellipticAleksandrov.Parabolic.TimeReversal
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Batteries.Tactic.Alias
import HypoellipticAleksandrov.KineticAleksandrov.Occupation.LocalizedKrylovCalculus
import Lean.Elab.Tactic.SolveByElim



/-! # Time reflection of anisotropic classical replacements

The existing reflection t ↦ 1-t preserves the C12 carrier and changes the sign of
the time derivative. No second time derivative is required.
-/

 public section

namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Set

variable {d : ℕ}

/-- Time reflection reverses the scalar time derivative for the anisotropic carrier. -/
theorem scalarTimeDerivative_timeReflectedScalar_C12
    {u : HypoellipticAleksandrov.Parabolic.ScalarField d} {D : HypoellipticAleksandrov.Parabolic.Region d} (hu : IsScalarC12On u D)
    {z : TimeVelocity d} (hz : timeReflection z ∈ D) :
    scalarTimeDerivative (timeReflectedScalar u) z =
      -scalarTimeDerivative u (timeReflection z) := (KineticAleksandrov.Occupation.scalarTimeDerivative_timeReflectedScalar u z)

/-- Spatial Hessians are unaffected by reflecting only time. -/
theorem scalarSpatialHessian_timeReflectedScalar_C12
    (u : HypoellipticAleksandrov.Parabolic.ScalarField d) (z : TimeVelocity d) :
    scalarSpatialHessian (timeReflectedScalar u) z =
      scalarSpatialHessian u (timeReflection z) := rfl

/-- The anisotropic classical carrier transports through the existing time reflection. -/
theorem isScalarC12On_timeReflectedScalar  {u : HypoellipticAleksandrov.Parabolic.ScalarField d}
    {D : HypoellipticAleksandrov.Parabolic.Region d} (hu : IsScalarC12On u D) :
    IsScalarC12On (timeReflectedScalar u) (timeReflection ⁻¹' D) := (KineticAleksandrov.Occupation.isScalarC12On_timeReflectedScalar hu)


end HypoellipticAleksandrov.Parabolic.LocalHolder
