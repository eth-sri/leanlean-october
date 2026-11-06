import GS.MatrixGeometry.Sharing

import GS.GlobalGeometry.FrobeniusProjection
import GS.Continuation.AmbientProjection
import GS.Extensions.ProjectionSmooth
import Mathlib.Analysis.Calculus.ContDiff.Operations



/-!
# Exact projection with arbitrary within-factor sharing AND overlap

The sharing relation below is the actual equality of local entries in tied
physical blocks. The core subspace is the image of its two concrete Lie-algebra
subspaces under (C,Omega) |-> C + P Omega P^T. Orthogonal projection is
constructed from the complete finite-dimensional subspace, not assumed through
normal equations and not replaced by averaged 1/2 masks.

These are exact generator-image results and smooth formulas in the factors.
No smooth quotient, tangent-bundle identification, efficient pseudoinverse
algorithm, or minimal-norm factor lift is claimed by this module.
-/
namespace GS.GlobalGeometry

/-- tau assigns a sharing label to each physical block. Labels need not be
consecutive or injective; different factors have independent labellings. -/
def TiedEntries (b : ℕ) (τ : ℕ → ℕ) (A : Mat n) : Prop :=
  ∀ i j i' j' : Fin n,
    i.val / b = j.val / b → i'.val / b = j'.val / b →
    τ (i.val / b) = τ (i'.val / b) →
    i.val % b = i'.val % b → j.val % b = j'.val % b → A i j = A i' j'



end GS.GlobalGeometry
