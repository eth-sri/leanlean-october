module

public import Erdos821.Blueprint.Graph
public import Erdos821.Blueprint.Analytic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

open scoped BigOperators
open MeasureTheory intervalIntegral

attribute [local instance] Classical.propDecidable

