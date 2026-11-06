import RequestProject.QCubeCanonicalTwoCycles
import RequestProject.QCubeFacetIncidence


/-! Decreasing square frames agree with the actual ordered coordinate directions. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [LinearOrder V] {A : CommRel V}

theorem qSquare_frame_unique (c : QSquare A) {a b}
    (h : b < a) (hs : c.1.spx = {a, b}) : qSquareLeft c = a ∧ qSquareRight c = b := by
  have hl : qSquareLeft c ∈ ({a, b} : Finset V) := by
    rw [← hs, qSquare_free_directions]
    simp
  have hr : qSquareRight c ∈ ({a, b} : Finset V) := by
    rw [← hs, qSquare_free_directions]
    simp
  have horder := qSquare_directions_decreasing c
  grind

theorem qSquare_subdivision_ordered (c : QSquare A) {a b}
    (h : b < a) hs :
    cubeSquareSubdivision c.1 (qSquareLeft c) (qSquareRight c)
      (qSquare_directions_ne c) (qSquare_free_directions c) =
      cubeSquareSubdivision c.1 a b (Ne.symm h.ne) hs := by
  cases' qSquare_frame_unique c h hs with hl hr
  simp_all

theorem qSquare_subdivision_single (c : QSquare A) n {a b}
    (h : b < a) hs :
    qSquareChainSubdivision (Finsupp.single c n) =
      n • cubeSquareSubdivision c.1 a b (Ne.symm h.ne) hs := by
  rw [qSquareChainSubdivision, squareChainSubdivision, Finsupp.linearCombination_single,
    qSquare_subdivision_ordered c h hs]
