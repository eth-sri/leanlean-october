module

public import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementSource
public import HypoellipticAleksandrov.Parabolic.TimeReversal
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add

/-! # Time reflection of anisotropic classical replacements

The existing reflection t ↦ 1-t preserves the C12 carrier and changes the sign of
the time derivative. No second time derivative is required.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Set

/-- Time reflection reverses the scalar time derivative for the anisotropic carrier. -/
theorem scalarTimeDerivative_timeReflectedScalar_C12 {d : ℕ}
    {u : TimeVelocity d → ℝ} {D : Set (TimeVelocity d)} (hu : IsScalarC12On u D)
    {z : TimeVelocity d} (hz : timeReflection z ∈ D) :
    scalarTimeDerivative (timeReflectedScalar u) z =
      -scalarTimeDerivative u (timeReflection z) := by
  have h := (hu.timeSlice_hasDerivAt hz).comp z.1
    ((hasDerivAt_const z.1 (1 : ℝ)).sub (hasDerivAt_id z.1))
  change deriv (fun t => u (1 - t, z.2)) z.1 = _
  simpa only [Function.comp_def, timeReflection, Pi.sub_apply, id_eq, zero_sub,
    mul_neg, mul_one] using h.deriv

end HypoellipticAleksandrov.Parabolic.LocalHolder
