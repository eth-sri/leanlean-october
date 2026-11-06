import RequestProject.CubeRollerModel


/-!
# Wall spaces and their dual cube complex

`RequestProject/SquareComplexWalls.lean` produces, out of a simply connected square complex,
a system of walls and the associated halfspace (Roller) coordinates of its vertices.  What is
still missing there is the *median-closedness* of the resulting set of coordinates, i.e. the
fact that the coordinates describe a CAT(0) cube complex.

This file proves that median-closedness for the **dual** object, which is Sageev's
construction: starting from a *wall space* — a set `X` together with a family of two-sided
partitions of `X` (walls), such that distinct points are separated by a wall and any two
points are separated by only finitely many walls — one forms the set of *consistent
orientations* of the walls (choices of one side of each wall, any two of which meet inside
`X`) that differ from a base point in finitely many walls.  The main results are:

* `FiniteChains.WallSpace.Consistent.maj` — consistency is preserved by the majority
  (median) operation;
* `FiniteChains.WallSpace.dualW_medFinset_mem` — in the halfspace coordinates based at a
  point `x₀`, the dual vertex set is closed under `FiniteChains.medFinset`;
* `FiniteChains.WallSpace.dualModel` — hence, once the dimension is at most three, the dual
  is a `FiniteChains.RollerModel`, so
  `FiniteChains.WallSpace.dual_ker_d₂_eq_range_d₃`: `ker d₂ = im d₃` for its cellular chain
  complex;
* `FiniteChains.WallSpace.coord_injective` — the points of `X` embed in the dual.

Nothing here is assumed finite or locally finite: `X` and the index type of walls are
arbitrary.
-/
