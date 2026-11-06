module

public import RequestProject.CubeRollerModel

@[expose] public section

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

namespace FiniteChains

universe u v

/-- The majority vote of three booleans. -/
def maj3 (a b c : Bool) : Bool := (a && b) || (b && c) || (a && c)

@[simp] theorem maj3_self (a : Bool) : maj3 a a a = a := by cases a <;> rfl

/-- A **wall space**: a family of walls on `X`, each wall `i` splitting `X` into the two
sides `side i x = true` and `side i x = false`; distinct points are separated by some wall,
and any two points are separated by only finitely many walls. -/
structure WallSpace (X : Type u) (ι : Type v) where
  /-- The side of the wall `i` on which the point `x` lies. -/
  side : ι → X → Bool
  /-- Distinct points are separated by a wall. -/
  sep : ∀ {x y : X}, x ≠ y → ∃ i, side i x ≠ side i y
  /-- Only finitely many walls separate two given points. -/
  fin : ∀ x y : X, {i | side i x ≠ side i y}.Finite

namespace WallSpace

variable {X : Type u} {ι : Type v} (S : WallSpace X ι)

variable {S}

variable (S)

variable {S}

/-! ## Halfspace coordinates

Recording a dual vertex by the set of walls on which it differs from the base point turns the
dual into the shape required by `FiniteChains.RollerModel`.
-/

section Coordinates

variable [DecidableEq ι]

variable (S) in
/-- The orientation obtained from the base orientation of `x₀` by flipping the walls in `A`. -/
def flipOn (x₀ : X) (A : Finset ι) : ι → Bool :=
  fun i => if i ∈ A then !S.side i x₀ else S.side i x₀

@[simp] theorem flipOn_empty (x₀ : X) : S.flipOn x₀ (∅ : Finset ι) = fun i => S.side i x₀ := by
  funext i; simp [flipOn]

/-- Distinct coordinates give distinct orientations. -/
theorem flipOn_injective (x₀ : X) : Function.Injective (S.flipOn x₀) := by
  intro A B h
  ext i
  have hi := congrFun h i
  simp only [flipOn] at hi
  constructor
  · intro hA
    by_contra hB
    rw [if_pos hA, if_neg hB] at hi
    simp at hi
  · intro hB
    by_contra hA
    rw [if_neg hA, if_pos hB] at hi
    simp at hi

variable (S) in
/-- The halfspace coordinates of a point of `X`: the (finite) set of walls separating it from
the base point. -/
noncomputable def coord (x₀ x : X) : Finset ι := (S.fin x x₀).toFinset

theorem flipOn_coord (x₀ x : X) : S.flipOn x₀ (S.coord x₀ x) = fun i => S.side i x := by
  funext i
  by_cases h : S.side i x = S.side i x₀
  · simp [flipOn, coord, Set.Finite.mem_toFinset, h]
  · simp only [flipOn, coord, Set.Finite.mem_toFinset, Set.mem_setOf_eq, if_pos h]
    cases hb : S.side i x <;> simp_all

@[simp] theorem coord_self (x₀ : X) : S.coord x₀ x₀ = (∅ : Finset ι) := by
  apply flipOn_injective x₀
  rw [flipOn_coord, flipOn_empty]

end Coordinates

end WallSpace

end FiniteChains
