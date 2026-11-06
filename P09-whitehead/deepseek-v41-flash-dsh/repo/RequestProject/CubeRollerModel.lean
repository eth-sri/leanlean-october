module

public import RequestProject.CubeCartanHadamard

@[expose] public section

/-!
# CAT(0) cube complexes in their combinatorial (Roller) form, and `H₂ = 0`

`RequestProject/CubeCartanHadamard.lean` proves the vanishing of the second homology of an at
most three-dimensional cube complex from the *descending-cube* axioms collected in
`FiniteChains.DescCubeStr` (heights, descending neighbours, and the squares and cubes that
descending edges span).  Those axioms were stated there as an explicit combinatorial shadow
of the CAT(0) input of the paper.

This file replaces them by the standard combinatorial description of a CAT(0) cube complex,
namely its *Roller (halfspace) model*: the vertices of a CAT(0) cube complex are the
consistent orientations of its system of hyperplanes, two vertices are joined by an edge when
they differ in exactly one hyperplane, and the vertex set is closed under the *median*
(majority) operation.  Fixing a base vertex and recording each vertex by the finite set of
hyperplanes on which it differs from the base vertex, this becomes:

* a set `W` of finite subsets of a type `ι` of hyperplanes,
* containing the base vertex `∅`,
* closed under the majority operation `medFinset A B C = (A ∩ B) ∪ (B ∩ C) ∪ (A ∩ C)`.

This is the structure `FiniteChains.RollerModel`.  Together with the dimension bound (a
vertex has at most three descending neighbours, i.e. the complex is at most three
dimensional) it *implies* all the descending-cube axioms:
`FiniteChains.RollerModel.toDescCubeStr`.  Consequently

* `FiniteChains.RollerModel.exists_d₃_eq` and
* `FiniteChains.RollerModel.ker_d₂_eq_range_d₃`

hold: in the cellular chain complex of such a complex every two-cycle bounds.

Combinatorially the point is elementary, and it is exactly the geometric content used by the
paper: with the base vertex at `∅`, a descending neighbour of a vertex `A` is `A.erase p`,
the square spanned by two descending neighbours `A.erase p`, `A.erase q` has fourth vertex
their intersection `A \ {p, q}` (which is again a vertex, by median-closedness), and three
descending neighbours span the three-cube with bottom vertex `A \ {p, q, r}`.
-/

namespace FiniteChains


variable {ι : Type u} [DecidableEq ι]

/-- The majority vote (median) of three finite sets: an element belongs to it when it belongs
to at least two of them. -/
def medFinset (A B C : Finset ι) : Finset ι := (A ∩ B) ∪ (B ∩ C) ∪ (A ∩ C)

/-- The **Roller model** of a CAT(0) cube complex based at one of its vertices: the vertices
are recorded as the finite sets of hyperplanes separating them from the base vertex, so that
the base vertex is `∅`, edges connect sets differing in one element, and the vertex set is
closed under the median (majority) operation.  The last field is the hypothesis that the
complex is at most three dimensional: a vertex has at most three descending neighbours. -/
structure RollerModel (ι : Type u) [DecidableEq ι] where
  /-- The vertex set, each vertex recorded by the set of hyperplanes separating it from the
  base vertex. -/
  W : Set (Finset ι)
  /-- The base vertex belongs to the complex. -/
  base_mem : (∅ : Finset ι) ∈ W
  /-- The vertex set is closed under the median operation. -/
  med_mem : ∀ {A B C : Finset ι}, A ∈ W → B ∈ W → C ∈ W → medFinset A B C ∈ W
  /-- The complex is at most three dimensional: a vertex has at most three descending
  neighbours. -/
  dim_le : ∀ A ∈ W, ∀ s : Finset (Finset ι),
    (∀ B ∈ s, B ∈ W ∧ B ⊆ A ∧ B.card + 1 = A.card) → s.card ≤ 3

namespace RollerModel

variable (M : RollerModel ι)

/-- The vertices of the complex. -/
def Vtx : Type u := {A : Finset ι // A ∈ M.W}

/-- A linear order on the vertices, used only to orient the cells. -/
noncomputable instance : LinearOrder M.Vtx := IsWellOrder.linearOrder WellOrderingRel

variable {M}

end RollerModel

namespace RollerModel

variable (M : RollerModel ι)

end RollerModel

end FiniteChains
