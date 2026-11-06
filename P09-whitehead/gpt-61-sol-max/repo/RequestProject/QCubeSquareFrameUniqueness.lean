import Mathlib.Tactic

import RequestProject.QCubeCanonicalTwoCycles
import RequestProject.QCubeFacetIncidence

/-! Decreasing square frames agree with the actual ordered coordinate directions. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [LinearOrder V] {A : CommRel V}

  (c : QSquare A)
theorem qSquare_frame_unique  {a b : V}
    (h : b < a) (hs : c.1.spx = {a, b}) : qSquareLeft c = a ∧ qSquareRight c = b := by
  have hl : qSquareLeft c ∈ ({a, b} : Finset V) := by
    rw [← hs, qSquare_free_directions]
    simp
  have hr : qSquareRight c ∈ ({a, b} : Finset V) := by
    rw [← hs, qSquare_free_directions]
    simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hl hr
  have horder := qSquare_directions_decreasing c
  rcases hl with hl | hl <;> rcases hr with hr | hr
  · simp_all
  · exact ⟨hl, hr⟩
  · grind
  · simp_all

theorem qSquare_subdivision_ordered  {a b : V}
    (h : b < a) (hs : c.1.spx = {a, b}) :
    cubeSquareSubdivision c.1 (qSquareLeft c) (qSquareRight c)
      (qSquare_directions_ne c) (qSquare_free_directions c) =
      cubeSquareSubdivision c.1 a b (Ne.symm h.ne) hs := by
  grind [qSquare_frame_unique]

theorem qSquare_subdivision_single  (n : ℤ) {a b : V}
    (h : b < a) (hs : c.1.spx = {a, b}) :
    qSquareChainSubdivision (Finsupp.single c n) =
      n • cubeSquareSubdivision c.1 a b (Ne.symm h.ne) hs := by
  rw [qSquareChainSubdivision, squareChainSubdivision, Finsupp.linearCombination_single,
    qSquare_subdivision_ordered c h hs]

end FiniteChains.Davis
