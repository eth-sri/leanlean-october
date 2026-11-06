import RequestProject.FoxNaturality
import RequestProject.PresentationDictionary
import RequestProject.NecessityAlgebraicMod
import RequestProject.CycleLifting
import RequestProject.Pi2Dictionary
import RequestProject.PresentationNecessity
import RequestProject.Tac


/-!
# Chains of presentation complexes

Condition (1) of Theorem A speaks of a chain `K = X₀ ⊂ X₁ ⊂ ⋯ ⊂ Xₙ` of two-complexes whose
inclusions are zero on `π₂`.  For complexes given by presentations, "`X_r ⊂ X_{r+1}`" means
concretely: the generators and the two-cells of `X_r` are generators and two-cells of
`X_{r+1}`, and an old two-cell is attached along the same word.  This is the structure
`FiniteChains.PresChain`.

From such a chain the cell-level data `ChainInput` used throughout Section 2 is *derived*
(`FiniteChains.PresChain.toChainInput`): the fundamental groups `π₁(X_r)` are the presented
groups, the maps between them are induced by the inclusions of the generating sets, and the
Fox boundary matrices restrict correctly — this last point is the naturality of the Fox
derivative proved in `RequestProject/FoxNaturality.lean`.  The only data that is not
derived but assumed is the topological content itself: the inclusion is zero on
`π₂ = ker ∂₂` (field `zero_pi2`).  The lifting of cycles modulo `m`, quoted in the paper
from Hatcher, is here a theorem (`RequestProject/CycleLifting.lean`).

Combining this with `RequestProject/PresentationNecessity.lean` gives
`FiniteChains.presComplex_hasAcyclicRegularCover_of_presChains`: if chains of nested
presentation complexes of every length exist over `K`, then `K` has a connected acyclic
regular cover, constructed as a two-complex.
-/

bwd
