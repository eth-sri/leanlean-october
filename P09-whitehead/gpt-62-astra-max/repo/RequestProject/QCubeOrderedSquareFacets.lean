module

public import RequestProject.QCubeCubicalTwoBoundary

@[expose] public section

/-! Actual edges of a square in any decreasing coordinate frame. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [LinearOrder V] {A : CommRel V}

variable (c : QSquare A) {a b : V} (h : b < a) (hs : c.1.spx = {a, b}) (s : ZMod 2)
include a b h hs

theorem qSquareSmallFacet_ordered :
    (qSquareSmallFacet c s).1 = qCubeFacet c.1 b s := by
  obtain ⟨_, hr⟩ := qSquare_frame_unique c h hs <;> aesop

theorem qSquareLargeFacet_ordered :
    (qSquareLargeFacet c s).1 = qCubeFacet c.1 a s := by
  obtain ⟨hl, _⟩ := qSquare_frame_unique c h hs <;> aesop

end FiniteChains.Davis
