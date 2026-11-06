import RequestProject.GenerationStep
import RequestProject.CockcroftExtStep
import RequestProject.Tac


/-!
# The composite operation: finitely many moves of rule 1

The operation `T` of Section 3.4 is a *finite sequence* of elementary moves, and the paper
finishes the proof of the generation equation (3.3) with the words "Composing proves (3.3)".
This file carries that out for the moves of rule 1 (one new generator together with one new
relator at a time), on top of the formal layer of `RequestProject/GenerationStep.lean`.

* `FiniteChains.extMor` — one elementary move, packaged as a structural map `PresMor`: the
  induced map of fundamental groups is `η_P`, and the induced map on two-chains pads a chain
  of the old presentation with `0` on the new two-cell.
* `FiniteChains.generates_extMor` — equation (3.3) for one move, under the two hypotheses of
  the paper (right regularity of the Fox derivative of the new relator with respect to the
  new generator, and injectivity of `η_{P*}` on fundamental groups).
* `FiniteChains.iterPres` — the presentation obtained after `n` moves, and
  `FiniteChains.iterMor` the composite structural map `P → T^n(P)`.
* `FiniteChains.generates_iterMor` — **equation (3.3) for the composite operation**.
* `FiniteChains.isCockcroft_iterPres` — the composite operation preserves Cockcroftness.
* `FiniteChains.cells_iterMor_eq_zero` — and it preserves zero maps on `π₂`: for a commuting
  square over the composite, a map which is zero on `π₂` upstairs induces zero on the whole
  of `π₂` of the transformed complex.
-/

bwd
