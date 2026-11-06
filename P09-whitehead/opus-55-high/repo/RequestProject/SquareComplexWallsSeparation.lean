import RequestProject.SquareComplexWallsExample
import RequestProject.SquareComplexWallsSphere


/-!
# A criterion for the separation property

`RequestProject/SquareComplexWallsSphere.lean` shows that the separation property — distinct
vertices lie on opposite sides of some wall — does not follow from connectedness and simple
connectivity alone.  This file isolates what has to be added: the standard geometric statement
*a shortest walk crosses each wall at most once*, which in the literature is proved from
nonpositive curvature by van Kampen (disk) diagrams.

* `FiniteChains.SquareComplex.crossCount` — the *number* (in `ℕ`, not modulo two) of edges of a
  walk crossing a given wall, and `FiniteChains.SquareComplex.crossCount_cast` relating it to the
  modulo-two crossing number of `RequestProject/SquareComplexWalls.lean`;
* `FiniteChains.SquareComplex.crossings_eq_side` — along any walk, the modulo-two crossing number
  of a two-sided wall is the difference of the two sides of its endpoints;
* `FiniteChains.SquareComplex.IsGeodesic` and `FiniteChains.SquareComplex.exists_geodesic` —
  shortest walks exist in a connected complex;
* `FiniteChains.SquareComplex.separation_of_geodesic_crossings` — **if every shortest walk crosses
  every wall at most once, then distinct vertices are separated by a wall**, i.e. the hypothesis
  `hsep` of `FiniteChains.SquareComplex.wallSpaceOf` holds, and
  `FiniteChains.SquareComplex.wallSpaceOf_of_geodesic_crossings` feeds it into the median dual
  complex;
* `FiniteChains.SquareComplex.exists_sepWalls_card`,
  `FiniteChains.SquareComplex.sepWalls_card_le_length` and
  `FiniteChains.SquareComplex.geodesic_crossings_of_metric` — the walls always give a lower bound
  for the distance, and the criterion is *equivalent* to the metric statement "the number of walls
  separating two vertices is their distance";
* `FiniteChains.SquareComplex.dsym_coord_eq_geodesic` — under the criterion the embedding into the
  median dual complex is isometric.

The criterion is sharp in the following sense: for the sphere of the previous file it fails in the
smallest possible way — the shortest walk `a, x, b` crosses the unique wall twice
(`FiniteChains.sphere_geodesic_crosses_twice`).
-/
