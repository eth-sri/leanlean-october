import RequestProject.QCubeCubicalTwoBoundary


/-! Actual edges of a square in any decreasing coordinate frame. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [LinearOrder V] {A : CommRel V}

theorem qSquareSmallFacet_ordered (c : QSquare A) {a b}
    (h : b < a) (hs : c.1.spx = {a, b}) s :
    (qSquareSmallFacet c s).1 = qCubeFacet c.1 b s := by
  cases' qSquare_frame_unique c h hs with _ hr
  aesop

theorem qSquareLargeFacet_ordered (c : QSquare A) {a b}
    (h : b < a) (hs : c.1.spx = {a, b}) s :
    (qSquareLargeFacet c s).1 = qCubeFacet c.1 a s := by
  cases' qSquare_frame_unique c h hs with hl _
  aesop
