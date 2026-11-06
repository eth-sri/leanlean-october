import RequestProject.CubeCartanHadamard


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
