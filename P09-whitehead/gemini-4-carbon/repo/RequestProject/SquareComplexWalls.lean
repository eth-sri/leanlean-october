module

public import Mathlib

@[expose] public section

/-!
# Walls (hyperplanes) of a simply connected square complex

The remaining geometric input of the paper, in the branch developed in
`RequestProject/CubeCartanHadamard.lean`, `RequestProject/CubeRollerModel.lean` and
`RequestProject/CubeMedianGraph.lean`, is the criterion

> a simply connected cube complex with flag links has median one–skeleton

(Gromov's link condition together with Chepoi's theorem).  Its first half — the half that is
responsible for *hyperplanes*, i.e. for the halfspace (Roller) coordinates used in
`FiniteChains.RollerModel` — is purely combinatorial and is proved here from scratch, with no
finiteness, local finiteness or dimension assumption:

*in a simply connected square complex every square-closed family of edges (in particular every
hyperplane) is two-sided: it is the set of edges joining the two sides of a partition of the
vertex set.*

Everything is elementary and self-contained:

* `FiniteChains.SquareComplex` — a graph together with a set of squares (two-cells), closed under
  rotating and reversing the cyclic order of the four vertices;
* walks are lists of vertices (`List.IsChain S.adj`), and `FiniteChains.SquareComplex.Move` is the
  elementary combinatorial homotopy: cancelling a backtrack `x, y, x ↝ x`, and pushing a path
  across a square `a, b, c ↝ a, d, c`;
* `FiniteChains.SquareComplex.SimplyConnected` says that every closed walk is homotopic to the
  constant walk.

The main results are

* `FiniteChains.SquareComplex.crossings_homotopic` — the number of edges of a walk lying in a
  square-closed family is a homotopy invariant modulo two;
* `FiniteChains.SquareComplex.crossings_eq_zero_of_closed` — hence it vanishes on closed walks of a
  simply connected complex;
* `FiniteChains.SquareComplex.exists_side` — hence, over a connected complex, every square-closed
  family `χ` of edges is the set of edges separating the two sides of a two-colouring `σ` of the
  vertices: `σ u + σ v = χ u v` for every edge `u v`;
* `FiniteChains.SquareComplex.exists_bipartition` — with the family of *all* edges: the
  one-skeleton of a connected simply connected square complex is bipartite (as the one-skeleton of a
  median graph must be);
* `FiniteChains.SquareComplex.closed_walk_length_odd` — equivalently, all closed walks have even
  length;
* `FiniteChains.SquareComplex.exists_side_edge` — an edge lying in no square separates the complex;
* `FiniteChains.SquareComplex.triangle_side_in_square` — hence every triangle has a side lying in a
  square; with the flag/dimension conditions of the cube complexes considered in the paper this is
  the absence of triangles.

Non-vacuity is checked on two explicit complexes: the complex with two vertices and one edge
(`FiniteChains.edgeComplex`) and the four-cycle with its square glued in
(`FiniteChains.cycleFour`, `FiniteChains.cycleFour_simplyConnected`), the latter containing a
genuine two-cell.  That the square is really needed is also checked: the four-cycle *without* the
square is not simply connected (`FiniteChains.cycleFourNoSquare_not_simplyConnected`).
-/

namespace FiniteChains

universe u

/-- A **square complex**, recorded combinatorially: a simple graph (`adj`) together with a
predicate `sq a b c d` saying that `a, b, c, d` are, in this cyclic order, the vertices of a
two-cell.  The last two axioms say that the set of squares does not depend on where the cyclic
order is started nor on its orientation. -/
structure SquareComplex (Vx : Type u) where
  /-- Adjacency of the one-skeleton. -/
  adj : Vx → Vx → Prop
  /-- Adjacency is symmetric. -/
  adj_symm : ∀ {a b : Vx}, adj a b → adj b a
  /-- There are no loops. -/
  adj_irrefl : ∀ a : Vx, ¬ adj a a
  /-- `sq a b c d` : the four vertices span a two-cell, in this cyclic order. -/
  sq : Vx → Vx → Vx → Vx → Prop
  /-- The four sides of a square are edges. -/
  sq_adj : ∀ {a b c d : Vx}, sq a b c d → adj a b ∧ adj b c ∧ adj c d ∧ adj d a
  /-- Squares may be read starting at any of their vertices. -/
  sq_rotate : ∀ {a b c d : Vx}, sq a b c d → sq b c d a
  /-- Squares may be read in either orientation. -/
  sq_reverse : ∀ {a b c d : Vx}, sq a b c d → sq d c b a

namespace SquareComplex

variable {Vx : Type u} {S : SquareComplex Vx}

/-- A walk is a list of vertices in which consecutive vertices are adjacent. -/
def IsWalk (S : SquareComplex Vx) (l : List Vx) : Prop := List.IsChain S.adj l

/-- A walk from `x` to `y`. -/
def IsWalkFrom (S : SquareComplex Vx) (x y : Vx) (l : List Vx) : Prop :=
  S.IsWalk l ∧ l.head? = some x ∧ l.getLast? = some y

/-- The elementary homotopies of walks: cancelling a backtrack, pushing across a square, and
performing either of these after a common initial vertex. -/
inductive Move (S : SquareComplex Vx) : List Vx → List Vx → Prop
  /-- Cancel the backtrack `x, y, x`. -/
  | backtrack (x y : Vx) (q : List Vx) : Move S (x :: y :: x :: q) (x :: q)
  /-- Push the path `a, b, c` across the square `a, b, c, d` to the path `a, d, c`. -/
  | square {a b c d : Vx} (h : S.sq a b c d) (q : List Vx) :
      Move S (a :: b :: c :: q) (a :: d :: c :: q)
  /-- Perform a move after a common initial vertex. -/
  | cons (x : Vx) {l l' : List Vx} : Move S l l' → Move S (x :: l) (x :: l')

/-- Combinatorial homotopy of walks: the equivalence relation generated by the elementary
moves. -/
def Homotopic (S : SquareComplex Vx) (l l' : List Vx) : Prop :=
  Relation.ReflTransGen (fun p q => S.Move p q ∨ S.Move q p) l l'

theorem Homotopic.refl (l : List Vx) : S.Homotopic l l := Relation.ReflTransGen.refl

theorem Homotopic.trans {l l' l'' : List Vx} (h : S.Homotopic l l') (h' : S.Homotopic l' l'') :
    S.Homotopic l l'' := Relation.ReflTransGen.trans h h'

/-! ### Moves preserve walks and their endpoints -/

theorem Move.head?_eq {l l' : List Vx} (h : S.Move l l') : l.head? = l'.head? := by
  induction h with
  | backtrack x y q => rfl
  | square h q => rfl
  | cons x _ _ => rfl

theorem Move.ne_nil {l l' : List Vx} (h : S.Move l l') : l ≠ [] ∧ l' ≠ [] := by
  induction h with
  | backtrack x y q => exact ⟨by simp, by simp⟩
  | square h q => exact ⟨by simp, by simp⟩
  | cons x _ ih => exact ⟨by simp, by simp⟩

theorem Move.getLast?_eq {l l' : List Vx} (h : S.Move l l') : l.getLast? = l'.getLast? := by
  induction h with
  | backtrack x y q => simp
  | square h q => simp
  | cons x hm ih =>
      rcases hm.ne_nil with ⟨h1, h2⟩
      rcases List.exists_cons_of_ne_nil h1 with ⟨a, t, rfl⟩
      rcases List.exists_cons_of_ne_nil h2 with ⟨b, t', rfl⟩
      simpa using ih

theorem Move.isWalk {l l' : List Vx} (h : S.Move l l') (hl : S.IsWalk l) : S.IsWalk l' := by
  induction h with
  | backtrack x y q =>
      rw [IsWalk, List.isChain_cons_cons] at hl
      exact hl.2.tail
  | square h q =>
      obtain ⟨hab, hbc, hcd, hda⟩ := S.sq_adj h
      rw [IsWalk, List.isChain_cons_cons] at hl ⊢
      refine ⟨S.adj_symm hda, ?_⟩
      rw [List.isChain_cons_cons] at hl ⊢
      exact ⟨S.adj_symm hcd, hl.2.2⟩
  | cons x hm ih =>
      rcases hm.ne_nil with ⟨h1, h2⟩
      rcases List.exists_cons_of_ne_nil h1 with ⟨a, t, rfl⟩
      rcases List.exists_cons_of_ne_nil h2 with ⟨b, t', rfl⟩
      rw [IsWalk, List.isChain_cons_cons] at hl ⊢
      have hhead := hm.head?_eq
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst hhead
      exact ⟨hl.1, ih hl.2⟩

theorem Homotopic.head?_eq {l l' : List Vx} (h : S.Homotopic l l') : l.head? = l'.head? := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => rcases hstep with hm | hm
                       · exact ih.trans hm.head?_eq
                       · exact ih.trans hm.head?_eq.symm

theorem Homotopic.getLast?_eq {l l' : List Vx} (h : S.Homotopic l l') :
    l.getLast? = l'.getLast? := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => rcases hstep with hm | hm
                       · exact ih.trans hm.getLast?_eq
                       · exact ih.trans hm.getLast?_eq.symm

/-! ### Crossing numbers -/

/-- The number, modulo two, of edges of the walk `l` carrying the label `χ`. -/
def crossings (χ : Vx → Vx → ZMod 2) : List Vx → ZMod 2
  | a :: b :: t => χ a b + crossings χ (b :: t)
  | _ => 0

@[simp] theorem crossings_nil (χ : Vx → Vx → ZMod 2) : crossings χ [] = 0 := rfl

@[simp] theorem crossings_singleton (χ : Vx → Vx → ZMod 2) (a : Vx) : crossings χ [a] = 0 := rfl

@[simp] theorem crossings_cons_cons (χ : Vx → Vx → ZMod 2) (a b : Vx) (t : List Vx) :
    crossings χ (a :: b :: t) = χ a b + crossings χ (b :: t) := rfl

/-- A **wall label**: a symmetric labelling of the edges by `ZMod 2` taking the same value on
opposite sides of every square.  The characteristic function of a hyperplane — a family of edges
closed under the relation "opposite sides of a square" — is such a labelling. -/
structure IsWallLabel (S : SquareComplex Vx) (χ : Vx → Vx → ZMod 2) : Prop where
  /-- The labelling does not depend on the direction of the edge. -/
  symm : ∀ a b : Vx, χ a b = χ b a
  /-- Opposite sides of a square carry the same label. -/
  square : ∀ {a b c d : Vx}, S.sq a b c d → χ a b = χ c d

/-! ### Simple connectivity -/

/-! ### Two walks with the same endpoints have the same crossing numbers -/

theorem isWalk_reverse {l : List Vx} (h : S.IsWalk l) : S.IsWalk l.reverse := by
  rw [IsWalk, List.isChain_reverse]
  exact h.imp (by intro a b hab; exact S.adj_symm hab)

theorem isWalk_junction {y z : Vx} {r : List Vx} (h : S.IsWalk (y :: r))
    (hz : r.head? = some z) : S.adj y z := by
  cases r with
  | nil => simp at hz
  | cons c r' =>
      simp only [List.head?_cons, Option.some.injEq] at hz
      subst hz
      exact (List.isChain_cons_cons.mp h).1

/-! ### Walls are two-sided -/

/-! ### Edges lying in no square -/

/-! ### Wall systems and halfspace (Roller) coordinates

A *wall system* records the hyperplanes of the complex: a family of square-closed edge labels such
that every edge crosses exactly one of them.  In a connected, simply connected complex each wall is
two-sided by `SquareComplex.exists_side`, so every vertex `v` acquires the set of walls separating
it from the base vertex; it is finite, it is empty at the base vertex, and along an edge it changes
by exactly one wall.  These are precisely the coordinates on which `FiniteChains.RollerModel` is
built. -/

/-- A **wall system** on a square complex: a family `χ i` of square-closed edge labels (the
hyperplanes) such that each edge crosses exactly one of them. -/
structure WallSystem (S : SquareComplex Vx) (ι : Type*) where
  /-- The characteristic function of the `i`-th wall. -/
  χ : ι → Vx → Vx → ZMod 2
  /-- Each member of the family is square-closed and symmetric. -/
  isWall : ∀ i, S.IsWallLabel (χ i)
  /-- Every edge crosses exactly one wall. -/
  edge_unique : ∀ u v : Vx, S.adj u v → ∃! i : ι, χ i u v = 1

/-- The set of walls separating any two vertices is finite: the wall pseudometric of a connected,
simply connected square complex with a wall system is well defined. -/
theorem separating_finite {ι : Type*} {σ : ι → Vx → ZMod 2} {x₀ : Vx}
    (hfin : ∀ v : Vx, {i : ι | σ i v ≠ σ i x₀}.Finite) (u v : Vx) :
    {i : ι | σ i u ≠ σ i v}.Finite := by
  refine Set.Finite.subset ((hfin u).union (hfin v)) ?_
  intro i hi
  by_contra hcon
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hcon
  exact hi (by rw [hcon.1, hcon.2])

end SquareComplex

end FiniteChains
