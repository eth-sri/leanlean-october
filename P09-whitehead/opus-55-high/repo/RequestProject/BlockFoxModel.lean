import RequestProject.BlockGenerates
import RequestProject.BaseChangeCycles
import RequestProject.Tac


/-!
# The chain model of the block substitution, built over the Fox complex

This is the (B2) half of the last link of the block argument.  `RequestProject/BlockGenerates.lean`
derives equation (3.3) — property (B2) — from the equivariant chain model of the double
mapping cylinder `W`, but through two hypotheses of dictionary type: that the boundary of the
cancelled two-complex *is* the Fox boundary of the substituted presentation (`hbdry`), and
that the cycles of the chosen copy of `X` *are* the images of the Fox cycles of `ρ`
(`himage`).

Here those two are built in instead of assumed.

* the two-chains of `W̃` are `(J' → ℤ[G']) × Q`, the first factor being the two-chains of the
  universal cover of the presentation complex of `ρ'` in the Fox coordinates, and the
  boundary is by construction the Fox boundary of `ρ'` on that factor
  (`FiniteChains.BlockFox.bdry₂`);
* the chains of the full preimage `U` of `X` are the free `ℤ[G']`-module on the two-cells of
  `X`, that is the base change `ℤ[G'] ⊗_{ℤ[G]} C₂(X̃)`, and its boundary is the base-changed
  Fox boundary of `ρ` (`FiniteChains.BlockFox.foxBdryPush`); the inclusion of the chosen copy
  of `X̃` is the base change `FiniteChains.PresMor.cellsBase` of the chain map of the
  structural map, which restricts to that map on the image of `C₂(X̃)`
  (`FiniteChains.PresMor.cellsBase_pushChain`);
* the chosen component is the `ℤ[G']`-span of the images of the Fox cycles of `ρ`, and the
  hypothesis "every cycle of `U` decomposes over the components" is a theorem
  (`FiniteChains.BlockFox.cycle_mem_span_pushCycles`): when the structural map is injective on
  fundamental groups — which is the `π₁`-injectivity of the substitution — the base-changed
  Fox matrix has its entries in the subring `ℤ[f(G)]`, so
  `FiniteChains.cycle_mem_span_subgroup_cycles` applies.

The result is `FiniteChains.BlockFox.generates_of_fox_chain_model`: **property (B2) with the
dictionary discharged**, its remaining hypotheses being the geometric ones — the exactness of
the pair `(W̃, U)` in the degrees used, and the vanishing `H₂(W̃, U) = 0` which the paper gets
from the curvature criterion.
-/

bwd
