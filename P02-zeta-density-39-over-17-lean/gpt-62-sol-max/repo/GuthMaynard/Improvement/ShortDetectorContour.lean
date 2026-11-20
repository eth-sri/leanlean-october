module
/-
Finite contour proof generalized from audited Density.DetectorContour.
The inherited analytic residue argument is adapted there from McColm's MIT
TypeIICoverage (pin2ace9e7c09a69fdcd1edae1ab6deb7cb3b4df1be).
No original density sources are changed. Numerator, kernel and residue are the
same literal definitions; only the unnecessarily strong lower bound is relaxed.
-/
public import MathCollab.Density.DetectorContour

@[expose] public section
open Complex MeasureTheory Set Filter MathCollab.Density MathCollab.Density.ZetaGrowth MathCollab.Density.Contour
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section
