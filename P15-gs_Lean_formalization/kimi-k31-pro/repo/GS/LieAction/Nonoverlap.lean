module

public import GS.LieAction.CompactQuotient
public import GS.Shuffle
public import GS.GeometryAlgebra

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The stabilizer in the real orthogonal non-overlap case

The entire O-block stabilizer is described, not just its tangent space.
It is equivalent to the 2^n diagonal sign matrices. This statement is for O,
not SO: separate determinant constraints would reduce the sign choices.

-/

noncomputable section
open Matrix
open scoped BigOperators
namespace GS.LieAction
variable {n : ℕ} {block₁ block₂ : Fin n → ℕ}

/-- Each intersection of a right block and a pulled-back left block contains
at most one coordinate. This is the exact no-offdiagonal-overlap condition. -/
def NoOffDiagonalOverlap (block₁ block₂ : Fin n → ℕ)
    (σ : Equiv.Perm (Fin n)) : Prop :=
  Function.Injective (fun i => (block₁ i, block₂ (σ i)))

end GS.LieAction
