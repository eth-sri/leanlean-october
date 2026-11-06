import Mathlib
import RequestProject.Tac


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

bwd
