import RequestProject.GenusFullCubeCoverFillings
import RequestProject.DeckChainTransport
noncomputable section


/-! Equivariant cap fillings obtained by translating one actual filling per disk. -/
namespace FiniteChains.Davis.Genus
open Comb
variable (q : ℕ) [NeZero q]

abbrev fullCubeMarkBase := (markedSpineToFullCube q).onV (markedSpineBase q)
abbrev fullCubeMarkCover := uCover _ (fullCubeMarkBase q)

def fullCubeBaseCapChain (x : Fin q × Bool) : (fullCubeMarkCover q).F →₀ ℤ :=
  fullCubeCoverCapChain q x (UV.base _ _) rfl
