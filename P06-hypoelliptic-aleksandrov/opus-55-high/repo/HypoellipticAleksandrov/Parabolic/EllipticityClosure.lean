module

public import HypoellipticAleksandrov.Parabolic.LocalClassical
public import HypoellipticAleksandrov.Parabolic.ContactMap

/-!
# Closure of local lower ellipticity

This module records that lower Loewner ellipticity is closed under limits of
continuous coefficient fields.  It is deliberately pointwise: no openness,
compactness, or positive ellipticity constant is needed for this extension.
-/

@[expose] public section


namespace HypoellipticAleksandrov.Parabolic

open Matrix Set
open scoped MatrixOrder

variable (d : ℕ)



/-- The affine lower Loewner cone is closed in the native matrix topology. -/
theorem isClosed_setOf_lowerEllipticity  (lam : ℝ) :
    IsClosed {M : PDE.Mat d | lam • (1 : PDE.Mat d) ≤ M} := (isClosed_posSemidef d).preimage (continuous_id.sub continuous_const)

namespace HasLowerEllipticityOn

/-- A continuous lower ellipticity bound extends to the closure whenever the
closure stays within the coefficient's continuity set. -/
theorem closure
    {d : ℕ} {lam : ℝ} {A : CoefficientField d}
    {S U : Set (TimeVelocity d)}
    (h : HasLowerEllipticityOn lam A S)
    (hcont : IsContinuousCoefficientOn A U)
    (hclosureU : _root_.closure S ⊆ U) :
    HasLowerEllipticityOn lam A (_root_.closure S) := by
  have hmaps : MapsTo (coefficientAt A) S
      {M : PDE.Mat d | lam • (1) ≤ M} := h
  have hcontClosure : ContinuousOn (coefficientAt A) (_root_.closure S) :=
    hcont.mono hclosureU
  have hmapsClosure  :=
    hmaps.closure_of_continuousOn hcontClosure
  intro z hz
  have hzLower := hmapsClosure hz
  rwa [(isClosed_setOf_lowerEllipticity d lam).closure_eq] at hzLower

end HasLowerEllipticityOn

end HypoellipticAleksandrov.Parabolic
