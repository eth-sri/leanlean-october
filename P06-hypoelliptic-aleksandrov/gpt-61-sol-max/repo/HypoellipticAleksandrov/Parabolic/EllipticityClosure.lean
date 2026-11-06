module

public import HypoellipticAleksandrov.Parabolic.LocalClassical
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import all HypoellipticAleksandrov.Parabolic.ContactMap

open private HypoellipticAleksandrov.Parabolic.isClosed_posSemidef from HypoellipticAleksandrov.Parabolic.ContactMap
open private HypoellipticAleksandrov.Parabolic.isClosed_isHermitian from HypoellipticAleksandrov.Parabolic.ContactMap


/-!
# Closure of local lower ellipticity

This module records that lower Loewner ellipticity is closed under limits of
continuous coefficient fields.  It is deliberately pointwise: no openness,
compactness, or positive ellipticity constant is needed for this extension.
-/

 public section



namespace HypoellipticAleksandrov.Parabolic

open Matrix Set
open scoped MatrixOrder

variable (d : ℕ)







/-- The affine lower Loewner cone is closed in the native matrix topology. -/
theorem isClosed_setOf_lowerEllipticity  (lam : ℝ) :
    IsClosed {M : PDE.Mat d | lam • (1 : PDE.Mat d) ≤ M} := (Eq.mpr (id (congrArg (fun _a => IsClosed _a) (Set.ext fun M => le_iff)))
  (IsClosed.preimage (Continuous.sub continuous_id continuous_const) (isClosed_posSemidef d)))

namespace HasLowerEllipticityOn

/-- A continuous lower ellipticity bound extends to the closure whenever the
closure stays within the coefficient's continuity set. -/
theorem closure
    {d : ℕ} {lam : ℝ} {A : CoefficientField d}
    {S U : HypoellipticAleksandrov.Parabolic.Region d}
    (h : HasLowerEllipticityOn lam A S)
    (hcont : IsContinuousCoefficientOn A U)
    (hclosureU : _root_.closure S ⊆ U) :
    HasLowerEllipticityOn lam A (_root_.closure S) := by




  intro z hz
  have hzLower := ((show MapsTo (coefficientAt A) S
      (({M : PDE.Mat d | lam • (1 : PDE.Mat d) ≤ M})) from h).closure_of_continuousOn (hcont.mono hclosureU)) hz
  rwa [(isClosed_setOf_lowerEllipticity d lam).closure_eq] at hzLower

end HasLowerEllipticityOn

end HypoellipticAleksandrov.Parabolic
