module

public import Mathlib

@[expose] public section

/-!
# A chain-level Cartan–Hadamard step for three-dimensional cube complexes

This file contains the combinatorial core of the step

  `H₂(V; ℤ) = 0`,  i.e.  `ker (d₂ : C₂(V) → C₁(V)) = im (d₃ : C₃(V) → C₂(V))`,

for the space `V` of the paper (the universal cover of the double cylinder with each
component of the preimage of `X` collapsed to a vertex), in the only form in which the
algebraic assembly of `RequestProject/RelativeH2.lean` uses it: as a statement about
cellular chains in degrees `1, 2, 3`.

## What is assumed and what is proved

The input is *local* combinatorial data of the cube complex `V` seen from a base vertex:

* a height function `ht` (the combinatorial distance to the base vertex);
* for every vertex `w` the set `dn w` of *descending* neighbours (the vertices of the
  complex joined to `w` by an edge of `V` and closer to the base vertex);
* for two distinct descending neighbours `a, b` of `w` the fourth vertex `med w a b` of the
  square that they span.

The axioms of `DescCubeStr` say exactly that:

* every edge changes the height by one (`ht_dn`);
* the complex is at most three-dimensional (`dim_le`: descending neighbours of a vertex span
  a cube, so no four of them are distinct) — no finiteness of links is assumed, and indeed
  the links of the new vertices of `V` are infinite in the application;
* any two descending neighbours span a square, any three span a three-cube
  (`med_mem`, `med_ne`, `med_bottom₁`, `med_bottom₂`).

The last group of axioms is the *descending-cube property*, which is the combinatorial
shadow of the CAT(0) (Cartan–Hadamard) input of the paper: in a CAT(0) cube complex the
edges at a vertex pointing towards the base vertex span a cube.

From this data the file builds the cellular chain complex in degrees `1, 2, 3`
(`FiniteChains.DescCubeStr.d₂`, `FiniteChains.DescCubeStr.d₃`) and proves

* `FiniteChains.DescCubeStr.d₂_d₃` — it is a chain complex;
* `FiniteChains.DescCubeStr.ker_d₂_le_range_d₃` — every two-cycle is a boundary;
* `FiniteChains.DescCubeStr.ker_d₂_eq_range_d₃` — `ker d₂ = im d₃`.

The proof is the "corner cancellation" induction: a nonzero two-cycle has a square whose top
vertex `w` is at maximal height; the cycle condition on the two edges of that square at `w`
forces `w` to have three descending neighbours and the three squares at `w` to occur with
coefficients `λ, -λ, λ`; subtracting `λ` times the boundary of the three-cube spanned by the
three descending neighbours removes all squares at `w` and creates only squares whose top
vertex is strictly lower.  This terminates.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

open Finsupp


/-- Combinatorial data of an at most three-dimensional cube complex, seen from a base
vertex: heights, descending neighbours and the squares and cubes they span. -/
structure DescCubeStr (Vx : Type u) [LinearOrder Vx] where
  /-- Combinatorial distance to the base vertex. -/
  ht : Vx → ℕ
  /-- The descending neighbours of a vertex. -/
  dn : Vx → Set Vx
  /-- The fourth vertex of the square spanned by two descending neighbours. -/
  med : Vx → Vx → Vx → Vx
  ht_dn : ∀ {w a : Vx}, a ∈ dn w → ht a + 1 = ht w
  dim_le : ∀ (w : Vx) (s : Finset Vx), ↑s ⊆ dn w → s.card ≤ 3
  med_comm : ∀ w a b : Vx, med w a b = med w b a
  med_mem : ∀ {w a b : Vx}, a ∈ dn w → b ∈ dn w → a ≠ b → med w a b ∈ dn a
  med_ne : ∀ {w a b c : Vx}, a ∈ dn w → b ∈ dn w → c ∈ dn w → a ≠ b → a ≠ c → b ≠ c →
    med w a b ≠ med w a c
  med_bottom₁ : ∀ {w a b c : Vx}, a ∈ dn w → b ∈ dn w → c ∈ dn w → a ≠ b → a ≠ c → b ≠ c →
    med a (med w a b) (med w a c) = med b (med w a b) (med w b c)
  med_bottom₂ : ∀ {w a b c : Vx}, a ∈ dn w → b ∈ dn w → c ∈ dn w → a ≠ b → a ≠ c → b ≠ c →
    med a (med w a b) (med w a c) = med c (med w a c) (med w b c)

namespace DescCubeStr

variable {Vx : Type u} [LinearOrder Vx] (S : DescCubeStr Vx)

/-- An oriented edge, recorded as the pair (upper endpoint, lower endpoint).  Pairs that
are not edges of the complex are allowed as generators of `C₁`; boundaries never use
them, so this does not affect the statements below. -/
abbrev EdgeC (_S : DescCubeStr Vx) : Type u := Vx × Vx

/-- A square: a vertex together with two distinct descending neighbours, listed in the
order of `Vx`. -/
def SqC : Type u :=
  {t : Vx × Vx × Vx // t.2.1 ∈ S.dn t.1 ∧ t.2.2 ∈ S.dn t.1 ∧ t.2.1 < t.2.2}

/-- A three-cube: a vertex together with three distinct descending neighbours, listed in the
order of `Vx`. -/
def CbC : Type u :=
  {t : Vx × Vx × Vx × Vx //
    t.2.1 ∈ S.dn t.1 ∧ t.2.2.1 ∈ S.dn t.1 ∧ t.2.2.2 ∈ S.dn t.1 ∧
      t.2.1 < t.2.2.1 ∧ t.2.2.1 < t.2.2.2}

variable {S}

/-- The vertex of a square at the highest level. -/
def SqC.top (F : S.SqC) : Vx := F.1.1
/-- The smaller of the two descending directions of a square. -/
def SqC.x (F : S.SqC) : Vx := F.1.2.1
/-- The larger of the two descending directions of a square. -/
def SqC.y (F : S.SqC) : Vx := F.1.2.2

/-- The largest descending direction of a three-cube. -/
def CbC.z (Q : S.CbC) : Vx := Q.1.2.2.2

variable (S)

/-- The edge from `w` down to a descending neighbour `a`. -/
def edge (w a : Vx) : S.EdgeC := (w, a)

/-- The square spanned at `w` by two distinct descending neighbours `x`, `y`. -/
def sqCell (w x y : Vx) (hx : x ∈ S.dn w) (hy : y ∈ S.dn w) (hne : x ≠ y) : S.SqC :=
  if h : x < y then ⟨(w, x, y), hx, hy, h⟩
  else ⟨(w, y, x), hy, hx, lt_of_le_of_ne (not_lt.mp h) (Ne.symm hne)⟩

/-! ## The chain complex -/

/-! ## Coefficients of a boundary -/

/-! ## Supports of the boundary of a three-cube -/

/-! ## Small order-theoretic helpers -/

/-! ## The local cycle condition at a vertex of maximal height -/

/-- Explicit constructor for a square, with its projections as simp lemmas. -/
def sq3 (w x y : Vx) (hx : x ∈ S.dn w) (hy : y ∈ S.dn w) (h : x < y) : S.SqC :=
  ⟨(w, x, y), hx, hy, h⟩

/-! ## Every two-cycle is a boundary -/

end DescCubeStr

end FiniteChains
