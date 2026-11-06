module

public import Erdos821.Blueprint.Candidate
public import Erdos821.Blueprint.Shift

@[expose] public section

noncomputable section
open scoped BigOperators ContDiff
open Filter
attribute [local instance] Classical.propDecidable
