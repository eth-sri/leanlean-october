import RequestProject.Pi2Generation
import RequestProject.HNNEmbedding
import RequestProject.Tac


/-!
# The two extension steps of rule 1 really do contain the old group

`RequestProject/Pi2Generation.lean` proves the generation statement (3.3) for a
one-generator, one-relator extension from two hypotheses: right-regularity of the Fox
derivative of the new relator, and injectivity of the induced map of fundamental groups.
This file discharges the second hypothesis for the two extensions used in rule 1 of
Section 3.4.

* `FiniteChains.extHom_tietze_injective` — for the defining relator `z = s` the map of
  fundamental groups is injective (it is in fact an isomorphism, with the explicit retraction
  `FiniteChains.tietzeRetract`);
* `FiniteChains.extHom_hnn_injective` — for the stable-letter relator `z u z^{-1} = v` the map
  is injective whenever the images of `u` and `v` have infinite order, because the enlarged
  presentation maps onto the HNN extension identifying the two infinite cyclic subgroups,
  and the base group of an HNN extension embeds into it (Serre's normal form theorem, see
  `RequestProject/HNNEmbedding.lean`).

Consequently the two generation statements
`FiniteChains.extCycle_tietze_span_of` and `FiniteChains.extCycle_hnn_span_of` hold with no
hypothesis on the fundamental groups at all.
-/

bwd
