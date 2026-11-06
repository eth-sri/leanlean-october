module

public import GS.Extensions.TransportedProjection
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Matrix.Normed

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Smoothness of the actual projection formulas in factor coordinates

All derivatives use the explicit entrywise sup norm, which induces the ordinary
finite-dimensional topology of matrices. Exact Frobenius optimality is proved
separately; no identification of these two norms is used.

These are real-analytic (hence C-infinity) statements on ambient factor-coordinate
spaces: in this mathlib version `ContDiff ℝ ⊤` denotes analytic regularity. Descending
the formulas to an abstract quotient manifold, and constructing the manifold,
are separate obligations, not implicit assumptions in the names below.
-/

noncomputable section
open Matrix
open scoped BigOperators
namespace GS.Extensions

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 theorem contDiff_matrix_mul {A B : E → Mat n}
    (hA : ContDiff ℝ ⊤ A) (hB : ContDiff ℝ ⊤ B) :
    ContDiff ℝ ⊤ (fun x => A x * B x) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  simp only [Matrix.mul_apply]
  apply ContDiff.sum
  intro k _
  exact ((contDiff_pi.mp (contDiff_pi.mp hA i) k).mul
    (contDiff_pi.mp (contDiff_pi.mp hB k) j))

end GS.Extensions
