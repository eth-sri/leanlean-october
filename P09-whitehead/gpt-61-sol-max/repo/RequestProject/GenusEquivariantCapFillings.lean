import Mathlib.Tactic

import RequestProject.GenusFullCubeCoverFillings
import RequestProject.DeckChainTransport

/-! Equivariant cap fillings obtained by translating one actual filling per disk. -/
namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

noncomputable abbrev fullCubeMarkBase := (markedSpineToFullCube q).onV (markedSpineBase q)
noncomputable abbrev fullCubeMarkCover := uCover (orderCx (QCube (cmpRel (GenusVertex q)))) (fullCubeMarkBase q)

noncomputable def fullCubeBaseCapChain (x : Fin q × Bool)  :=
  fullCubeCoverCapChain q x (UV.base _ (fullCubeMarkBase q)) rfl

end FiniteChains.Davis.Genus
