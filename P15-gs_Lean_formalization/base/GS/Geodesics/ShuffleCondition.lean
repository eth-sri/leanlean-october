module

public import GS.LieAction.Nonoverlap
public import GS.OriginalLocalModel

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The exact scalar-shuffle nonoverlap condition

The numeric action is proved for the original scalar permutation, rather than
assumed as an extra convention. In common output coordinates the right block
label is the remainder modulo the number of original right blocks. Consequently
`b₂ ≤ k₁` gives the exact support condition used by the orbit-block geodesics.
-/

noncomputable section
namespace GS.Geodesics
open GS GS.LieAction

/-- The same original permutation transported to an explicitly named dimension. -/
def scalarShuffleOfSize {n k b : ℕ} (hN : n = k*b) : Equiv.Perm (Fin n) :=
  (Equiv.cast (congrArg Fin hN)).trans
    ((scalarShuffle k b).trans (Equiv.cast (congrArg Fin hN.symm)))

end GS.Geodesics
