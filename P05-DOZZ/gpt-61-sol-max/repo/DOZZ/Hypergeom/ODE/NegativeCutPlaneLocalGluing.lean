/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.NegativeCutPlaneContinuation

public import DOZZ.Hypergeom.ODE.LocalGluingCore

/-! The negative-cut endpoint state locally agrees with a Picard disk solution. -/

@[expose] public section

open Set unitInterval

namespace DOZZ.Proofs

/-- Around every point of the negative cut plane, the selected endpoint state agrees with one
holomorphic local solution of the Gauss first-order system. -/
abbrev gaussNegativeCutPlaneContinuationState_locally_eq_picard
    (a b c : ℂ) (z : gaussNegativeCutPlane) :=
  independent_path_continuation_locally_eq_picard gaussNegativeCutPlane_isOpen
    (gaussSystemOperator a b c)
    ((gaussSystemOperator_differentiableOn a b c).mono gaussNegativeCutPlane_subset_regularPlane)
    (ordinaryHypergeometricState a b c (-1 / 2 : ℂ))
    (gaussNegativeCutPlaneContinuationState a b c)
    (fun w => ⟨gaussNegativeCutPlaneCanonicalPath w,
      gaussNegativeCutPlaneCanonicalContinuationLift a b c w, rfl⟩)
    (gauss_negative_cut_plane_continuation_path_endpoint_eq a b c) z

end DOZZ.Proofs
