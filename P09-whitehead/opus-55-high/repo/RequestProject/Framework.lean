import RequestProject.Pigeonhole
import RequestProject.SubgroupCompactness


/-!
# Theorem A: the formal skeleton

Theorem A of the paper reads: for a connected two-complex `K` the following are
equivalent.

1. For every `n ≥ 1` there is a chain `K = K₀ ⊊ K₁ ⊊ ⋯ ⊊ Kₙ` of two-complexes
   in which every inclusion induces zero on `π₂`.
2. `K` has a connected acyclic regular cover.

Homotopy theory of two-complexes (`π₁`, `π₂`, Hurewicz, covering spaces, the
CAT(0) cube complexes behind the blocks `B_q`) is far outside what can be built
here, so the notions occurring in Theorem A are packaged in the interface
`TwoComplexData`, and the geometric statements proved in the paper are recorded
as explicit hypotheses:

* `RelativeInputs` records Lemma 3.1 (the initial Cockcroft pair `D ⊂ Y_D`)
  together with the properties of the replacement operation `T` and its
  terminal extension `Q` established in Lemmas 3.9 and 3.10;
* `SufficiencyInputs` adds the descent step, Proposition 3.11;
* `NecessityInputs` records the Fox-boundary input of Section 2, namely
  formula (2.3) relating a chain to normal subgroups of `G = π₁(K)`, the finite
  determinacy of the requirements, their stability under intersections of
  chains, Lemma 2.1 in the form "the commutator subgroup inherits the
  requirements", and the identification of an acyclic regular cover with a
  perfect normal subgroup satisfying them.

What *is* proved here is the entire bookkeeping of the paper's two inductions:
the construction of relative chains of arbitrary length from the operations `T`
and `Q` (Proposition 3.7), the descent to `K` (so `(2) ⇒ (1)`), and the
pigeonhole/compactness/minimality derivation of a perfect normal subgroup from
chains of every finite length (so `(1) ⇒ (2)`).
-/

namespace FiniteChains

universe u


variable (W : TwoComplexData)




/-!
## Input from Section 3: the replacement operation and its terminal extension
-/


variable {W}

variable (W)


variable {W}

/-!
## Input from Section 2: Fox boundaries and the requirements (2.2)
-/
