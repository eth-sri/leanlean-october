module

public import RequestProject.SlideMor
public import RequestProject.TietzeElimination
public import RequestProject.BlockSubstitutionMor

@[expose] public section

/-!
# Lemma 3.9: the structural operation `T`

Lemma 3.9 of the paper states, for the replacement operation `T` of Section 3.4 and for every
presentation `P` containing the fixed core `D`,

  `π₂(T(P)) = ℤ[G(T(P))] · η_{P*} π₂(P)`,                                        (3.3)

and draws from it the two consequences: `T` preserves the Cockcroft property, and `T`
preserves the vanishing of the maps induced on `π₂` by the labelled inclusions.

The operation `T` is a *finite sequence of elementary moves*: for every extra generator `z`
rule 1 performs three moves (freely adjoin `b_z`; adjoin the stable letter `a_z` with the
relator `a_z b_z a_z⁻¹ = z b_z`; eliminate `z` by `z = [a_z,b_z]`), rule 2 slides an extra
relator over retained core relators, and rule 3 substitutes a block for an extra relator.
The proof of the lemma treats each move separately and ends with the words "Composing
proves (3.3)".

This file carries out exactly that scheme.

* `FiniteChains.PresPoint` — a finite presentation, bundled with its finiteness data;
* `FiniteChains.TMove` — **one elementary move of the operation `T`**: the moves of rule 1,
  the slide of rule 2, and the block substitution of rule 3.  The block move carries
  the generation property (B2) of the block as data: (B2) is the one input of Lemma 3.9 which
  the paper takes from Theorem 3.2 (its proof is the cubical geometry of Section 3.3), and it
  is the only hypothesis left in this file.  All the other moves carry no hypothesis beyond
  the elementary facts checked in the paper itself;
* `FiniteChains.TMove.generates` — **equation (3.3) for one move**;
* `FiniteChains.TPath` — a finite sequence of moves, that is, the operation `T` itself, and
  `FiniteChains.TPath.mor` its structural map `η_P`;
* `FiniteChains.TPath.generates` — **equation (3.3) for `T`** ("composing proves (3.3)");
* `FiniteChains.TPath.isCockcroft` — **`T` preserves the Cockcroft property**;
* `FiniteChains.TPath.cells_eq_zero` — **the last paragraph of Lemma 3.9**: for a labelled
  inclusion `j : P ⊂ P'` with `T(j) ∘ η_P = η_{P'} ∘ j`, if `j` is zero on `π₂` then `T(j)`
  is zero on the whole of `π₂(T(P))`.
-/

namespace FiniteChains

open MonoidAlgebra


/-- A finite presentation, bundled with the finiteness data used by the Fox calculus. -/
structure PresPoint : Type (u + 1) where
  /-- The generators. -/
  gens : Type u
  /-- The two-cells, i.e. the relator labels. -/
  cells : Type u
  [fintypeGens : Fintype gens]
  [decEqGens : DecidableEq gens]
  [fintypeCells : Fintype cells]
  [decEqCells : DecidableEq cells]
  /-- The relators. -/
  rel : cells → FreeGroup gens

attribute [instance] PresPoint.fintypeGens PresPoint.decEqGens PresPoint.fintypeCells
  PresPoint.decEqCells

namespace PresPoint

/-- Adjoining one generator together with one relator. -/
def ext (P : PresPoint.{u}) (w₀ : FreeGroup (Option P.gens)) : PresPoint.{u} where
  gens := Option P.gens
  cells := Option P.cells
  rel := extRel P.rel w₀

end PresPoint

namespace TMove

end TMove

namespace TPath

end TPath

end FiniteChains
