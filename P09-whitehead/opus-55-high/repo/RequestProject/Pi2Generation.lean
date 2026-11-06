import RequestProject.Pi2Extension
import RequestProject.BaseChangeCycles
import RequestProject.Tac


/-!
# Generation of `π₂` over the enlarged group ring (equation (3.3) for one extension step)

Lemma 3.9 of the paper rests on the generation statement

  `π₂(T(P)) = ℤ[G(T(P))] · η_{P*} π₂(P)`,                                        (3.3)

and Proposition 3.11 repeats the same argument downstairs.  In the combinatorial model `π₂`
is the module of Fox cycles, and this file proves (3.3) for one step of the construction —
adjoining a single generator together with a single relator — from the two ingredients
established separately:

* `RequestProject/Pi2Extension.lean`: a Fox cycle of the enlarged presentation is zero on the
  new two-cell and is a Fox cycle of the *old* Fox matrix, read in the enlarged group ring;
* `RequestProject/BaseChangeCycles.lean`: cycles of a matrix with entries in the group ring of
  a subgroup are generated, over the big group ring, by cycles over the subgroup ring.

The subgroup in question is the image of the old fundamental group, so the second ingredient
applies as soon as that image is a faithful copy of the old group — exactly the HNN normal
form statement quoted in the paper (`RequestProject/HNNEmbedding.lean`) in the case of the
stable-letter extension, and a triviality for the Tietze step.

The main results are `FiniteChains.extCycle_mem_span` (the general step) and its two
instances `FiniteChains.extCycle_tietze_span`, `FiniteChains.extCycle_hnn_span`.
-/

bwd
