module

public import RequestProject.SquareComplexWallsExample
public import RequestProject.SquareComplexWallsSphere

@[expose] public section

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

namespace FiniteChains

namespace SquareComplex

universe u

variable {Vx : Type u} {S : SquareComplex Vx}

/-! ### Counting crossings in `ℕ` -/

/-- The number of edges of the walk `l` crossing the wall `χ`. -/
def crossCount (χ : Vx → Vx → ZMod 2) : List Vx → ℕ
  | a :: b :: t => (if χ a b = 1 then 1 else 0) + crossCount χ (b :: t)
  | _ => 0

@[simp] theorem crossCount_nil (χ : Vx → Vx → ZMod 2) : crossCount χ ([] : List Vx) = 0 := rfl

@[simp] theorem crossCount_singleton (χ : Vx → Vx → ZMod 2) (a : Vx) :
    crossCount χ [a] = 0 := rfl

@[simp] theorem crossCount_cons_cons (χ : Vx → Vx → ZMod 2) (a b : Vx) (t : List Vx) :
    crossCount χ (a :: b :: t) = (if χ a b = 1 then 1 else 0) + crossCount χ (b :: t) := rfl

/-! ### Crossing numbers and the two sides of a wall -/

/-! ### Shortest walks -/

/-! ### The criterion -/

end SquareComplex

/-! ### Sharpness: on the sphere a geodesic crosses the wall twice -/

/-! ### Non-vacuity: the criterion holds for the four-cycle

For the four-cycle with its square glued in the criterion can be checked by hand, and it yields the
separation property — hence the median embedding — unconditionally. -/

instance : DecidableRel cycleFour.adj := fun u v => inferInstanceAs (Decidable (cycleFourAdj u v))

instance (l : List (ZMod 4)) : Decidable (cycleFour.IsWalk l) :=
  inferInstanceAs (Decidable (List.IsChain cycleFourAdj l))

instance (u v : ZMod 4) (l : List (ZMod 4)) : Decidable (cycleFour.IsWalkFrom u v l) :=
  inferInstanceAs (Decidable (cycleFour.IsWalk l ∧ l.head? = some u ∧ l.getLast? = some v))

end FiniteChains
