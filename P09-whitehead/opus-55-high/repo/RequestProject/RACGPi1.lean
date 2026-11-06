import RequestProject.RACGSquareComplex
import RequestProject.SquareComplexMonodromy
import RequestProject.SquareComplexCoverExists


/-!
# The fundamental group of `C(L)` is the kernel of the parity map

The paper computes the fundamental group of the real moment-angle complex `C(L)`: it is the
kernel of the abelianisation `W_L → (ℤ/2)^{L⁰}` of the right-angled Coxeter group.  This file
proves that statement in the combinatorial category, for the edge-path group
`FiniteChains.SquareComplex.Pi1` of the square complex `C(L)`:

* `FiniteChains.RACG.kerPhi` — the kernel of the parity map, as a subgroup of `W_L`;
* `FiniteChains.RACG.liftEnd_deck` — the lift of a walk of `C(L)` is equivariant for the deck
  transformations, that is for left multiplication by elements of the kernel;
* `FiniteChains.RACG.pi1Equiv` — **the monodromy is a group isomorphism**
  `π₁(C(L)) ≃* ker(W_L → (ℤ/2)^{L⁰})`, and `FiniteChains.RACG.pi1_cubeCx_equiv` is the same
  statement with the base point written as the zero sign vector.

The proof uses the combinatorial covering theory of
`RequestProject/SquareComplexCovering.lean` (the parity map is a covering of square complexes,
`FiniteChains.RACG.isCovering_phi`), the simple connectivity of the Cayley complex and the
monodromy bijection of `RequestProject/SquareComplexMonodromy.lean`.
-/
