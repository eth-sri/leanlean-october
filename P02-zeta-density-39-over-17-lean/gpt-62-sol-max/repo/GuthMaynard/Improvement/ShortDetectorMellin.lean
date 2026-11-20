module
/-
Right-contour extension reusing the audited DetectorMellin proof, whose termwise
Mellin argument is adapted from McColm TypeIICoverage, commit
2ace9e7c09a69fdcd1edae1ab6deb7cb3b4df1be, MIT. Original sources unchanged.
-/
public import MathCollab.Density.DetectorMellin

@[expose] public section
open Complex MeasureTheory Set Filter MathCollab.Density
open scoped ArithmeticFunction.Moebius BigOperators Topology
set_option autoImplicit false
noncomputable section
