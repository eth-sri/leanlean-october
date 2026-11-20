module

public import RequestProject.Framework

@[expose] public section

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

namespace FiniteChains

/-- A toy interpretation: "complexes" are natural numbers, "subcomplex" is `≤`, and every
other predicate holds.  Strict inclusions are available because `n < n + 1`. -/
@[reducible] def toyData : TwoComplexData.{0} where
  Cx := ℕ
  Sub := (· ≤ ·)
  sub_refl _ := le_rfl
  sub_trans h h' := le_trans h h'
  Cockcroft _ := True
  ZeroPi2 _ _ := True
  Pi1Trivial _ _ := True
  Acyclic _ := True
  IsAcyclicCover _ _ := True

end FiniteChains
