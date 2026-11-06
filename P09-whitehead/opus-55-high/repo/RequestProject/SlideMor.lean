import RequestProject.SlideGeneration
import RequestProject.RuleOneMor
import RequestProject.Tac


/-!
# Rule 2 as a structural map with the generation property

Rule 2 of the operation `T` of Lemma 3.9 replaces an extra relator `r*` by
`r⁰ = r* ∏_j r_j^{c_j}`, a product of `r*` with retained core relators.  The paper justifies
the generation equation (3.3) for this rule by the remark that the move is a finite sequence
of slides of the relator disk over core disks, hence a homotopy equivalence relative to `D`.

`RequestProject/SlideGeneration.lean` proves the combinatorial content of that remark: the
slide does not change the normal closure of the relators, and on two-cycles it acts as the
`ℤ[G]`-linear isomorphism `y ↦ (j ↦ y j - y_{j₀} λ j)`.  This file packages the move as a
**structural map** `PresMor` of `RequestProject/GenerationStep.lean` and proves that it
satisfies `FiniteChains.Generates`, so that rule 2 composes with rules 1 and 3.

* `FiniteChains.slideGroupHom` — the (iso)morphism of fundamental groups induced by the
  slide, together with its inverse and the induced isomorphism of group rings;
* `FiniteChains.slideMor` — rule 2 as a structural map;
* `FiniteChains.generates_slideMor` — **equation (3.3) for rule 2**, with no hypothesis
  beyond the defining property of the correcting word and its coefficient vector.
-/

bwd
