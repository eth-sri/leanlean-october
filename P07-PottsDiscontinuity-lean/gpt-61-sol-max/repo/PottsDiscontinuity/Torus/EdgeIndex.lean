module
public import Mathlib

public import PottsDiscontinuity.Torus.Darts

/-!
# Directed darts enumerate each indexed torus edge once

The edge index is its left/lower endpoint and a horizontal/vertical Boolean.
This keeps parallel edges distinct. The equivalence below proves that the cycles of
`directedStep` really partition the edge set, not merely a collection of edge slots.
-/

@[expose] public section

open PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

abbrev MedialEdge (N M : ℕ) := (Fin N × Fin M) × Bool

variable {N M : ℕ}

/-- Forget the choice of direction of a dart. -/
def dartEdge : Dart N M → MedialEdge N M
  | ((i, j), .west) => ((prv i, j), false)
  | ((i, j), .east) => ((i, j), false)
  | ((i, j), .south) => ((i, prv j), true)
  | ((i, j), .north) => ((i, j), true)

@[simp] theorem dartEdge_edgeReverse (d : Dart N M) :
    dartEdge (edgeReverse d) = dartEdge d := by
  rcases d with ⟨⟨i, j⟩, p⟩
  cases p <;> simp only [dartEdge, edgeReverse, Equiv.symm_apply_apply]

/-- The dart on an indexed edge that follows its arrow. -/
def arrowDart (ω : ArrowConfig N M) : MedialEdge N M → Dart N M
  | ((i, j), false) => if ω.horiz (i, j) then ((i, j), .east) else ((nxt i, j), .west)
  | ((i, j), true) => if ω.vert (i, j) then ((i, j), .north) else ((i, nxt j), .south)

section

variable (ω : ArrowConfig N M)


theorem dartOut_arrowDart  (e : MedialEdge N M) :
    dartOut ω (arrowDart ω e) = true := by
  rcases e with ⟨⟨i, j⟩, b⟩
  cases b <;>
    simp only [arrowDart] <;> split_ifs with h <;>
    simp only [dartOut, localOut, ArrowConfig.left, ArrowConfig.right, ArrowConfig.below, ArrowConfig.above, Equiv.symm_apply_apply, h, Bool.not_false]

theorem dartEdge_arrowDart  (e : MedialEdge N M) :
    dartEdge (arrowDart ω e) = e := by
  rcases e with ⟨⟨i, j⟩, b⟩
  cases b <;> simp only [arrowDart] <;> split_ifs <;>
    simp only [dartEdge, Equiv.symm_apply_apply]

theorem arrowDart_dartEdge  (d : DirectedDart ω) :
    arrowDart ω (dartEdge d.val) = d.val := by
  rcases d with ⟨⟨⟨i, j⟩, p⟩, hd⟩
  cases p <;>
    simp only [dartOut, localOut, ArrowConfig.left, ArrowConfig.right,
      ArrowConfig.below, ArrowConfig.above, Bool.not_eq_true'] at hd <;>
    simp only [dartEdge, arrowDart, hd, Bool.false_eq_true, ↓reduceIte, Equiv.apply_symm_apply]

end

/-- The arrow field selects exactly one directed dart for each indexed edge. -/
def edgeDirectedEquiv (ω : ArrowConfig N M) : MedialEdge N M ≃ DirectedDart ω where
  toFun e := ⟨arrowDart ω e, dartOut_arrowDart ω e⟩
  invFun d := dartEdge d.val
  left_inv := dartEdge_arrowDart ω
  right_inv d := Subtype.ext (arrowDart_dartEdge ω d)

end PottsDiscontinuity.Torus
