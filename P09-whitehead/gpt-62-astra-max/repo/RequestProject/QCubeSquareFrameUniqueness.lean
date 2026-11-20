module

public import RequestProject.QCubeCanonicalTwoCycles
public import RequestProject.QCubeFacetIncidence

@[expose] public section

/-! Decreasing square frames agree with the actual ordered coordinate directions. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [LinearOrder V] {A : CommRel V}

variable (c : QSquare A)

section

variable {a b : V} (h : b < a) (hs : c.1.spx = {a, b})
include h hs

theorem qSquare_frame_unique : qSquareLeft c = a ∧ qSquareRight c = b := by
  have hl : qSquareLeft c ∈ ({a, b} : Finset V) := by
    rw [← hs, qSquare_free_directions]
    simp
  have hr : qSquareRight c ∈ ({a, b} : Finset V) := by
    rw [← hs, qSquare_free_directions]
    simp
  grind [qSquare_directions_decreasing]

theorem qSquare_subdivision_ordered :
    cubeSquareSubdivision c.1 _ _
      (qSquare_directions_ne c) (qSquare_free_directions c) =
      cubeSquareSubdivision c.1 a b (Ne.symm h.ne) hs := by
  grind [qSquare_frame_unique]

end

theorem qSquare_subdivision_single (n : ℤ) {a b : V}
    (h : b < a) (hs : c.1.spx = {a, b}) :
    qSquareChainSubdivision (Finsupp.single c n) =
      n • cubeSquareSubdivision c.1 a b (Ne.symm h.ne) hs := by
  grind [qSquareChainSubdivision, squareChainSubdivision, Finsupp.linearCombination_single, qSquare_subdivision_ordered]

end FiniteChains.Davis
