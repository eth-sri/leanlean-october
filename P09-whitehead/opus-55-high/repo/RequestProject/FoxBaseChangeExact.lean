import RequestProject.BlockRelativeVanishing
import RequestProject.UniversalCoverPi2
import RequestProject.CoverHomologyOne
import RequestProject.Tac


/-!
# Exactness of the Fox complex in degree one, and its base change

The (B2) half of the block argument needs, besides the CAT(0) input `H₂(W̃) = 0`, the injectivity
of `H₁(U) → H₁(W̃)`, where `U` is the full preimage of `X` in the universal cover of the double
mapping cylinder (`hU` in `RequestProject/BlockRelativeVanishing.lean`).  Geometrically `U` is a
disjoint union of copies of the universal cover `X̃`, so its first homology vanishes outright.

This file proves that, algebraically and with no hypotheses beyond the `π₁`-injectivity of the
substitution:

* `FiniteChains.univCover_exact_one` — **`H₁(X̃) = 0`**: a one-chain of the universal cover of a
  presentation complex killed by `∂₁` is the Fox boundary of a two-chain.  (From the Crowell
  sequence of `RequestProject/CoverHomologyOne.lean`: the cycles are the Fox vectors of the
  relator subgroup, and those are exactly the boundaries.)
* `FiniteChains.exists_preimage_base_change` — **base change along a subgroup preserves this
  kind of exactness**: if a matrix and a "boundary" matrix have their entries in `ℤ[H]`, and
  over `ℤ[H]` every cycle is a boundary, then the same holds over `ℤ[G]`.  The proof is the
  coset decomposition of `RequestProject/BaseChangeCycles.lean`: `ℤ[G]` is free over `ℤ[H]` on
  the cosets, and a cycle splits into its coset pieces, each of which is a cycle over `ℤ[H]`.
* `FiniteChains.BlockFox.foxBdryPush_exact_one` — **`H₁(U) = 0`**: every one-chain of the
  preimage killed by the boundary is the base-changed Fox boundary of a two-chain of the
  preimage.
* `FiniteChains.BlockFox.hU_of_chainMap` — the hypothesis `hU` of
  `FiniteChains.BlockFox.generates_of_absolute_model` follows, given that the inclusion of the
  preimage is a chain map in degree one which is injective on zero-chains and that the boundary
  of a boundary vanishes.
## Scope of this route (applicability warning)

The implication proved here is correct, but its hypothesis `habs` is **stronger than what the
article's Lemma "Generation in the pushout" supplies**.  That lemma allows an arbitrary
connected two-complex `X`, and its own Step 1 (the radial retraction) shows that `π₂(X)` injects
into `π₂(W)`; for a nonaspherical `X` this makes `H₂(W̃) = π₂(W) ≠ 0`, so `habs` is false.  A
concrete instance is `RequestProject/BlockSphereRegression.lean`.  The article's geometric input
is the *relative* vanishing `H₂(W̃, U) ≅ H₂(V, V₀) = H₂(V) = 0`, obtained from the space `V` in
which each component of `U` is collapsed to a vertex; property (B2) in that form is
`FiniteChains.BlockFox.generates_of_quotient_relative`
(`RequestProject/BlockRelativeQuotient.lean`), and the input is discharged from a cube-complex
model of `V` in `RequestProject/BlockCubeV.lean`.  The statements of this file should therefore
be read as an auxiliary implication, not as the article's argument.
-/

bwd
