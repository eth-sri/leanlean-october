import RequestProject.BlockGeneration
import RequestProject.GenerationStep


/-!
# From the homology of the double mapping cylinder to equation (3.3)

`RequestProject/BlockGeneration.lean` proves, for the equivariant chain model of the double
mapping cylinder, that the two-cycles of the cancelled two-complex are spanned over
`ℤ[π₁(W)]` by the cancelled images of the two-cycles of the chosen copy of `X`.  Property
(B2) is stated in the language of presentations: for the structural map `f : E → E'` of the
substitution (3.4),

  `π₂(E') = ℤ[G(E')] · f_* π₂(E)`,

i.e. every **Fox cycle** of `E'` is a `ℤ[G(E')]`-combination of images of Fox cycles of `E`
(`FiniteChains.Generates`).  This file proves that the two statements agree: the surjectivity
obtained from the relative homology *is* the generation of all Fox cycles by the images of
the old ones.

* `FiniteChains.foxBdry` — the Fox boundary of a presentation as a map of `ℤ[G]`-modules, and
  `FiniteChains.isFoxCycle_iff_foxBdry_eq_zero`: Fox cycles are exactly its kernel, so the
  two-chains of the universal cover of a presentation complex form a chain complex in the
  sense used by the homological lemmas;
* `FiniteChains.generates_of_block_chain_model` — **the passage to presentations**: given the
  chain model of the double mapping cylinder for the substitution, the vanishing of
  `H₂(W̃, U)`, the transitive deck action on the components of `U` and the identification of
  the cancelled images with the images of the structural map, equation (3.3) holds for that
  structural map.

As everywhere in this part of the development, the single geometric input that is not proved
is the vanishing `H₂(W̃, U) = 0`, which the paper obtains from the cubical curvature criterion
for the collapsed space `V`.
-/
