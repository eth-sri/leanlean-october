module

public import RequestProject.SquareComplexWalls
public import RequestProject.WallSpaceDualConnected

@[expose] public section

/-!
# From the walls of a square complex to a wall space

`RequestProject/SquareComplexWalls.lean` produces, for a connected and simply connected square
complex carrying a system of walls, halfspace coordinates `σ i : Vx → ZMod 2`: each wall cuts
the vertex set into two sides, an edge changes exactly one coordinate, and only finitely many
walls separate two given vertices.  `RequestProject/WallSpaceDual.lean` shows that a *wall
space* has a median dual cube complex.

This file joins the two halves.  The single missing ingredient is the *separation* property —
distinct vertices are separated by some wall — which is exactly the part of Sageev's theorem
that is not proved in the project; it is therefore carried here as an explicit hypothesis.
Granting it:

* `FiniteChains.SquareComplex.wallSpaceOf` — the vertices, with the walls, form a
  `FiniteChains.WallSpace`;
* `FiniteChains.SquareComplex.wallSpaceOf_coord_injective` — the vertices embed into the
  median dual complex;
* `FiniteChains.SquareComplex.wallSpaceOf_dsym_adj` — an edge of the complex becomes an edge
  of the dual: the halfspace coordinates of its endpoints differ in exactly one wall.

Thus, granting separation, the one-skeleton of such a complex maps injectively and
edge-preservingly into a median (CAT(0) cube complex) graph.
-/

namespace FiniteChains

open RollerBridge

universe u

namespace SquareComplex

variable {Vx : Type u}

section WallSpace

variable {ι : Type*} {σ : ι → Vx → ZMod 2} {x₀ : Vx}

theorem decide_ne_of_ne {a b : ZMod 2} (h : a ≠ b) : decide (a = 1) ≠ decide (b = 1) := by
  revert h; revert a b; decide

theorem ne_of_decide_ne {a b : ZMod 2} (h : decide (a = 1) ≠ decide (b = 1)) : a ≠ b := by
  revert h; revert a b; decide

/-- **The vertices of a square complex with separating walls form a wall space.**  The
coordinates `σ` are those produced by `FiniteChains.SquareComplex.exists_rollerCoordinates`;
`hsep` is the separation property, the one step of Sageev's theorem that is not proved in the
project. -/
def wallSpaceOf (hfin : ∀ v : Vx, {i : ι | σ i v ≠ σ i x₀}.Finite)
    (hsep : ∀ u v : Vx, u ≠ v → ∃ i, σ i u ≠ σ i v) : WallSpace Vx ι where
  side i v := decide (σ i v = 1)
  sep := by
    intro u v huv
    obtain ⟨i, hi⟩ := hsep u v huv
    exact ⟨i, decide_ne_of_ne hi⟩
  fin := by
    intro u v
    refine Set.Finite.subset (separating_finite hfin u v) ?_
    intro i hi
    exact ne_of_decide_ne hi

@[simp] theorem wallSpaceOf_side (hfin : ∀ v : Vx, {i : ι | σ i v ≠ σ i x₀}.Finite)
    (hsep : ∀ u v : Vx, u ≠ v → ∃ i, σ i u ≠ σ i v) (i : ι) (v : Vx) :
    (wallSpaceOf hfin hsep).side i v = decide (σ i v = 1) := rfl

end WallSpace

end SquareComplex

end FiniteChains
