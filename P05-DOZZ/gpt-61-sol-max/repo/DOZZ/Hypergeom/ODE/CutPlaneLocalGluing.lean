/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.CutPlaneEndpoint

public import DOZZ.Hypergeom.ODE.LocalGluingCore

/-! The path-independent cut-plane endpoint state locally agrees with a Picard disk solution. -/

@[expose] public section

open Set unitInterval

namespace DOZZ.Proofs

/-- Around every point of the principal cut plane, the selected endpoint state agrees with one
holomorphic local solution of the Gauss first-order system. -/
abbrev gaussCutPlaneContinuationState_locally_eq_picard
    (a b c : ℂ) (z : gaussCutPlane) :=
  independent_path_continuation_locally_eq_picard gaussCutPlane_isOpen
    (gaussSystemOperator a b c)
    ((gaussSystemOperator_differentiableOn a b c).mono gaussCutPlane_subset_regularPlane)
    (ordinaryHypergeometricState a b c (1 / 2 : ℂ))
    (gaussCutPlaneContinuationState a b c)
    (fun w => ⟨gaussCutPlaneCanonicalPath w,
      gaussCutPlaneCanonicalContinuationLift a b c w, rfl⟩)
    (gauss_cut_plane_continuation_path_endpoint_eq a b c) z

end DOZZ.Proofs
