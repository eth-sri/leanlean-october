module

public import RequestProject.GenusFullCubeCoverFillings
public import RequestProject.DeckChainTransport

@[expose] public section

/-! Equivariant cap fillings obtained by translating one actual filling per disk. -/
noncomputable section

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

abbrev fullCubeMarkBase := (markedSpineToFullCube q).onV (markedSpineBase q)
abbrev fullCubeMarkCover := uCover (orderCx (QCube (cmpRel (GenusVertex q)))) (fullCubeMarkBase q)

def fullCubeBaseCapChain (x : Fin q × Bool) :=
  fullCubeCoverCapChain q x (UV.base _ (fullCubeMarkBase q)) rfl

end FiniteChains.Davis.Genus
