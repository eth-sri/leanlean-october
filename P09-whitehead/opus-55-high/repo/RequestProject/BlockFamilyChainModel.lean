import RequestProject.BlockFamilySubst
import RequestProject.BlockRelativeQuotient


/-!
# The chain model of the double mapping cylinder of a whole family of blocks

`RequestProject/BlockFamilySubst.lean` builds the structural map of the article's
simultaneous substitution (3.4): a family `(s : Sx)` of labelled relator entries of

  `ρ : Jr ⊕ Sx → FreeGroup α`

is replaced at the same time, the entry `s` by its own block with its own internal generators
`Zt s` and its own relator entries `Mt s`.

This file instantiates the (B2) route of `RequestProject/BlockRelativeQuotient.lean` — the one
that goes through the *relative* complex of the pair `(W̃, U)` and the article's homological
input `H₂(W̃, U) = 0` — **at that concrete substitution**.  All the data that the general
statement `FiniteChains.BlockFox.generates_of_quotient_relative` takes as parameters are
*constructed* here from the substitution itself, and all its structural hypotheses are
*proved* here:

* `FiniteChains.BlockFamily.oneChainIncl` (`f₁`) — the one-chains of the preimage of `X` are
  the one-chains on the old generators, included into the one-chains on all generators by
  extension by zero.  Its injectivity is `oneChainIncl_injective`;
* `FiniteChains.BlockFamily.polyBdry` (`bq`) — the module `Sx → ℤ[G']` of the two-chains
  carried by the replaced polygons, with the boundary of the polygon at `s` equal to the
  base-changed Fox row of the replaced relator `ρ (Sum.inr s)`;
* `FiniteChains.BlockFamily.cylChain` (`a₃`) and the negation isomorphism (`b₃`) — the
  three-cells of the double mapping cylinder, one per replaced entry: the boundary of the
  three-cell at `s` is the filling chain `c s` of the block at `s` minus the replaced polygon.
  This is the cancelling pair of cells of the article ("in the double mapping cylinder of
  `a_s` the polygon-cylinder three-cell cancels that old two-cell; for distinct `s` these
  cancelling pairs are disjoint");
* `FiniteChains.BlockFamily.chainMap_incl` (`hchainF₂`) — the inclusion of the preimage of
  `X` is a chain map, i.e. the boundary of the cover restricts to the base-changed Fox
  boundary of `ρ`;
* `FiniteChains.BlockFamily.bdry_bdry_eq_zero` (`hdd`) — the boundary of the boundary of a
  three-cell vanishes.

The outcome is

  `FiniteChains.BlockFamily.generates_familySubst_of_relative_vanishing`,

property (B2) — equation (3.3) — for the article's simultaneous substitution, with exactly
two remaining inputs, both of them the geometric ones of the article's proof:

* `hinj`: the substitution is injective on fundamental groups (Step 1 of the article's
  "Generation in the pushout of a family", the radial retraction in the CAT(0) universal
  cover).  By `FiniteChains.BlockSubst.baseHom_not_injective` this cannot be replaced by any
  argument using presentations alone;
* `hrel`: `H₂(W̃, U) = 0` for this concrete relative complex (Steps 2 and 3, the collapsed
  space `V` and its cube structure).

No further dictionary, no cell-by-cell identification with a cube complex and no hypothesis
about `H₂(W̃)` (which is false for a nonaspherical `X`, see
`RequestProject/BlockSphereRegression.lean`) is used.

As everywhere in the project's Fox calculus, the presentations are finite, so the family `Sx`
of simultaneously replaced entries is a finite (but otherwise arbitrary) set of labelled
entries.
-/
