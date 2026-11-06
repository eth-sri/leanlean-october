import RequestProject.TreeChainTopological


/-!
# Condition (1) of Theorem A, as stated by the interface, implies condition (2)

`RequestProject/CombData.lean` instantiates the interface `FiniteChains.TwoComplexData` of
Theorem A by honest combinatorial two-complexes: `combData`.  Condition (1) of Theorem A is
then `FiniteChains.HasZeroChains combData K`, that is, the existence for every `n` of a chain

  `K = c 0 ⊊ c 1 ⊊ ⋯ ⊊ c n`

of two-complexes, each inclusion being an inclusion of subcomplexes inducing zero on `π₂`.

`RequestProject/TreeChainTopological.lean` proves `(1) ⇒ (2)` for chains packaged as
`FiniteChains.Comb.TopChain`.  This file feeds the interface-level condition into that theorem;
the only extra hypotheses are that the stages of the chains are connected and finite, which is
what the collapse to a finite presentation needs.

* `FiniteChains.Comb.Hom.congr` — transport of a cellular map along equalities of complexes,
  used to pad a finite chain to a family indexed by all of `ℕ`;
* `FiniteChains.Comb.hasAcyclicRegularCover_of_hasZeroChains_comb` — **condition (1) of
  Theorem A, in the form carried by the interface `combData`, implies condition (2)** for a
  finite connected two-complex whose chains have finite connected stages.
-/
