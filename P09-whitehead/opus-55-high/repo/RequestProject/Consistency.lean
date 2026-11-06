import RequestProject.Framework


/-!
# The hypothesis bundles are consistent

`theoremA` is proved *relative* to the hypotheses collected in
`SufficiencyInputs` and `NecessityInputs`.  A relative theorem is worthless if
its hypotheses are contradictory, since then anything at all would follow.
This file rules that out by exhibiting a model: a `TwoComplexData` for which
both bundles are inhabited.

The model is of course not the geometry of two-complexes; it only witnesses
that the axioms recorded from the paper are mutually consistent, so that
`theoremA` is a genuine implication and not a vacuous one.
-/
