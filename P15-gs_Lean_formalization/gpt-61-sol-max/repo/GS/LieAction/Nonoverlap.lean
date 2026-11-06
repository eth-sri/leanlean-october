
import GS.LieAction.CompactQuotient
import GS.Shuffle
import GS.GeometryAlgebra



/-!
# The stabilizer in the real orthogonal non-overlap case

The entire O-block stabilizer is described, not just its tangent space.
It is equivalent to the 2^n diagonal sign matrices. This statement is for O,
not SO: separate determinant constraints would reduce the sign choices.

-/

namespace GS.LieAction
variable  {block₁ block₂ : Fin n → ℕ}

/-- Each intersection of a right block and a pulled-back left block contains
at most one coordinate. This is the exact no-offdiagonal-overlap condition. -/
def NoOffDiagonalOverlap (block₁ block₂ : Fin n → ℕ)
    (σ : Equiv.Perm (Fin n)) : Prop :=
  Function.Injective (fun i => (block₁ i, block₂ (σ i)))







end GS.LieAction
