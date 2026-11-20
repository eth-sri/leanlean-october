/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.SeriesBranch
public import DOZZ.Hypergeom.ODE.NegativeCutPlaneTopology
public import Mathlib.Analysis.Complex.Convex

/-! The two regular branches agree on their upper and lower half-plane overlaps. -/

@[expose] public section

open Filter Set Topology

namespace DOZZ.Proofs

noncomputable def gaussCutPlaneMidpoint : gaussCutPlane :=
  ⟨1 / 2, by norm_num [gaussCutPlane]⟩

noncomputable def gaussNegativeCutPlaneBasepoint : gaussNegativeCutPlane :=
  ⟨-1 / 2, by norm_num [gaussNegativeCutPlane]⟩

noncomputable def gaussCutPlaneScalarState := gaussSeriesBranchScalar
  gaussCutPlane_subset_regularPlane gaussCutPlaneMidpoint gaussCutPlane_starConvex

noncomputable def gaussNegativeCutPlaneScalarState := gaussSeriesBranchScalar
  gaussNegativeCutPlane_subset_regularPlane gaussNegativeCutPlaneBasepoint gaussNegativeCutPlane_starConvex

section
variable (a b c : ℂ) (hc : ∀ n : ℕ, c ≠ -(n : ℂ))

theorem gaussCutPlaneScalarState_differentiableOn :
    DifferentiableOn ℂ (gaussCutPlaneScalarState a b c) gaussCutPlane :=
  gaussSeriesBranchScalar_differentiableOn _ _ _ gaussCutPlane_isOpen a b c

theorem gaussNegativeCutPlaneScalarState_differentiableOn :
    DifferentiableOn ℂ (gaussNegativeCutPlaneScalarState a b c) gaussNegativeCutPlane :=
  gaussSeriesBranchScalar_differentiableOn _ _ _ gaussNegativeCutPlane_isOpen a b c

include hc

theorem gaussCutPlaneScalarState_eq_ordinary_on_unitDisk {z : ℂ}
    (hz : z ∈ gaussCutPlane) (hnorm : ‖z‖ < 1) :
    gaussCutPlaneScalarState a b c z = ordinaryHypergeometric a b c z :=
  gaussSeriesBranchScalar_eq_ordinary _ _ _ a b c hc (by norm_num [gaussCutPlaneMidpoint]) hz hnorm

theorem gaussNegativeCutPlaneScalarState_eq_ordinary_on_unitDisk {z : ℂ}
    (hz : z ∈ gaussNegativeCutPlane) (hnorm : ‖z‖ < 1) :
    gaussNegativeCutPlaneScalarState a b c z = ordinaryHypergeometric a b c z :=
  gaussSeriesBranchScalar_eq_ordinary _ _ _ a b c hc (by norm_num [gaussNegativeCutPlaneBasepoint]) hz hnorm

private theorem gaussBranches_eqOn {U : Set ℂ} (hU : IsOpen U) (hconv : Convex ℝ U)
    (hnonreal : ∀ z ∈ U, z.im ≠ 0) {z₀ : ℂ} (hz₀ : z₀ ∈ U) (hnorm : ‖z₀‖ < 1) :
    EqOn (gaussCutPlaneScalarState a b c) (gaussNegativeCutPlaneScalarState a b c) U := by
  refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    (((gaussCutPlaneScalarState_differentiableOn a b c).analyticOnNhd gaussCutPlane_isOpen).mono
      (fun z hz => Or.inl (hnonreal z hz)))
    (((gaussNegativeCutPlaneScalarState_differentiableOn a b c).analyticOnNhd
      gaussNegativeCutPlane_isOpen).mono (fun z hz => Or.inl (hnonreal z hz)))
    hconv.isPreconnected hz₀ ?_
  filter_upwards [hU.mem_nhds hz₀, (continuous_norm.continuousAt (x := z₀)).eventually_lt
    continuousAt_const hnorm] with w hw hwNorm
  exact (gaussCutPlaneScalarState_eq_ordinary_on_unitDisk a b c hc (Or.inl (hnonreal w hw)) hwNorm).trans
    (gaussNegativeCutPlaneScalarState_eq_ordinary_on_unitDisk a b c hc (Or.inl (hnonreal w hw)) hwNorm).symm

/-- The two continuations agree on each half-plane by the identity theorem. -/
theorem gaussBranches_eq_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) :
    gaussCutPlaneScalarState a b c z = gaussNegativeCutPlaneScalarState a b c z := by
  rcases lt_or_gt_of_ne hz with hneg | hpos
  · exact gaussBranches_eqOn a b c hc (isOpen_Iio.preimage Complex.continuous_im)
      (convex_halfSpace_im_lt 0) (fun _ hw => ne_of_lt hw)
      (z₀ := -Complex.I / 2) (by norm_num [div_eq_mul_inv, Complex.mul_im]) (by norm_num) hneg
  · exact gaussBranches_eqOn a b c hc (isOpen_Ioi.preimage Complex.continuous_im)
      (convex_halfSpace_im_gt 0) (fun _ hw => ne_of_gt hw)
      (z₀ := Complex.I / 2) (by norm_num [div_eq_mul_inv, Complex.mul_im]) (by norm_num) hpos

end

end DOZZ.Proofs
