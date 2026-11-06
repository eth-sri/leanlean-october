import GS.MatrixFactor.OrdinaryQR
import GS.MatrixGeometry.Cayley

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.DotProduct
import GS.Unitary.Projection
import Mathlib.Analysis.Matrix.PosDef



/-!
# Matrix Cayley algebra in the original GS matrix type

We use c(A) = (1 - A) * (1 + A)⁻¹. This convention is involutive on
{A | det (1 + A) ≠ 0}; its derivative at zero has sign -2.
All inverse identities have explicit determinant hypotheses. No smooth or
manifold structure is assumed here. Supports are the original `GS.UnitaryGeometry.CSupported`.

All algebraic claims below are proved without extra axioms.
-/

namespace GS.UnitaryManifold
export GS.MatrixBase (inv_mul cancel_right cancel_left cancel_congruence cayley admissible cayley_mul one_add_cayley_mul admissible_cayley cayley_involutive cayley_unitary cayley_isSkew admissible_zero cayley_zero admissible_one admissible_of_isSkew)
open GS.UnitaryGeometry








variable (block : Fin n → ℕ)

variable (A : CMat n)

theorem cayley_supported
    (hs : CSupported block A) (hA : admissible A) :
    CSupported block (cayley A) := by
  have h1 : GS.MatrixBase.CSupported block (1 : CMat n) := .one
  letI := Matrix.invertibleOfIsUnitDet (1 + A) (isUnit_iff_ne_zero.mpr hA)
  exact GS.MatrixBase.CSupported.mul
    (by intro i j hij; simp [h1 i j hij, hs i j hij])
    (GS.MatrixFactor.cSupported_inverse (h1.add hs))

@[simp] theorem cayley_one : cayley (1 : CMat n) = 0 := by
  simp [cayley]



end GS.UnitaryManifold
