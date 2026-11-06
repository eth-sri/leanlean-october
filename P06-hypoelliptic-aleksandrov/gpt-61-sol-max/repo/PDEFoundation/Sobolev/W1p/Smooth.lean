module

public import PDEFoundation.Sobolev.ClassicalGradient
public import PDEFoundation.Sobolev.W1p.Basic

/-!
# Smooth functions on bounded Sobolev domains

This file packages globally `C¹` scalar functions as representative-level
`W^{1,p}` functions on bounded measurable domains. Compact support is not
required: continuity on the compact closure of the domain supplies uniform
bounds for the function and each coordinate of its classical gradient.

The stored weak gradient is exactly `classicalGradient`, so later smooth
approximation arguments can use the same gradient API as the quantitative
regularity estimates.
-/

@[expose] public section

open scoped ENNReal

namespace PDE

namespace W1pFunction

/-- Package a globally `C¹` function as a `W^{1,p}` representative on a
bounded measurable domain. -/
noncomputable def ofContDiffOnIsSobolevRegularDomain
    {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
    (hU : IsSobolevRegularDomain U) {f : Vec d → ℝ}
    (hf : ContDiff ℝ 1 f) : W1pFunction U p where
  toFun := f
  grad := classicalGradient f
  memLp := by
    have  :=
      hU.isFiniteMeasure_volumeOn
    have hfContinuous : Continuous f :=
      (hf.differentiable (by simp)).continuous
    have hclosureCompact  :=
      hU.isBoundedDomain.isBounded.isCompact_closure
    let C : ℝ :=
      Classical.choose
        (hclosureCompact.exists_bound_of_continuousOn
          hfContinuous.continuousOn)
    have hC  :=
      Classical.choose_spec
        (hclosureCompact.exists_bound_of_continuousOn
          hfContinuous.continuousOn)
    refine MeasureTheory.MemLp.of_bound
      (μ := volumeOn U) hfContinuous.aestronglyMeasurable C ?_
    rw [MeasureTheory.ae_restrict_iff' hU.measurableSet]
    exact Filter.Eventually.of_forall fun x hx =>
      hC x (subset_closure hx)
  gradMemLp := by
    have  :=
      hU.isFiniteMeasure_volumeOn
    have hclosureCompact  :=
      hU.isBoundedDomain.isBounded.isCompact_closure
    intro i
    have hgradContinuous :
        Continuous (fun x => classicalGradient f x i) := by
      simpa only [classicalGradient_apply] using
        (hf.continuous_fderiv (by simp)).clm_apply continuous_const
    let C : ℝ :=
      Classical.choose
        (hclosureCompact.exists_bound_of_continuousOn
          hgradContinuous.continuousOn)
    have hC  :=
      Classical.choose_spec
        (hclosureCompact.exists_bound_of_continuousOn
          hgradContinuous.continuousOn)
    refine MeasureTheory.MemLp.of_bound
      (μ := volumeOn U) hgradContinuous.aestronglyMeasurable C ?_
    rw [MeasureTheory.ae_restrict_iff' hU.measurableSet]
    exact Filter.Eventually.of_forall fun x hx =>
      hC x (subset_closure hx)
  hasWeakGradient :=
    HasWeakGradientOn.of_contDiff hf

variable {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}




variable (hU : IsOpenBoundedConvexDomain U) {f : Vec d → ℝ} (hf : ContDiff ℝ 1 f)

/-- Bounded open convex domains provide the bounded-domain smooth
`W^{1,p}` constructor. -/
noncomputable def ofContDiffOnIsOpenBoundedConvexDomain

     : W1pFunction U p :=
  ofContDiffOnIsSobolevRegularDomain
    hU.isSobolevRegularDomain hf

@[simp]
theorem ofContDiffOnIsOpenBoundedConvexDomain_toFun

     :
    (ofContDiffOnIsOpenBoundedConvexDomain
      (p := p) hU hf).toFun = f :=
  rfl



end W1pFunction

end PDE
