module

public import GS.Projection

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Coordinate-correct overlap halving

The mask is defined in the coordinates of C and P Ω Pᵀ. Its pullback, not the
same array, must be applied to Ω. This module strengthens the original
entrywise conjugated-mask lemma to the entire correction operator.
This module is included in the full build and axiom audit.
-/
noncomputable section
open Matrix
namespace GS.Revision
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Pull a common-coordinate mask back to the original right-factor coordinates. -/
def pullMask (σ : Equiv.Perm ι) (p : ι → ι → Prop) : ι → ι → Prop :=
  fun i j => p (σ i) (σ j)

instance pullMaskDecidable (σ : Equiv.Perm ι) (p : ι → ι → Prop)
    [DecidableRel p] : DecidableRel (pullMask σ p) :=
  fun i j => inferInstanceAs (Decidable (p (σ i) (σ j)))

end GS.Revision
