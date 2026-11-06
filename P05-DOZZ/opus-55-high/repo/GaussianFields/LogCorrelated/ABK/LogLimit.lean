/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import GaussianFields.LogCorrelated.ABK.MAlpha

/-!
# GaussianFields.LogCorrelated/ABK/LogLimit

Port of the corresponding GaussianFields source module.
-/

public section

open Filter MeasureTheory
open scoped ENNReal Topology

namespace GaussianFields

/-- The logarithmic covariance kernel appearing in Appendix A. -/
@[expose]
noncomputable def abkLogCovarianceKernel {d : Nat} (x y : Vec d) : ℝ :=
  -Real.log (euclideanNorm (x - y))

/-- Pointwise Riesz-kernel-to-log limit away from the diagonal. -/
theorem tendsto_euclideanNorm_rpow_neg_sub_one_div_nhdsGT_zero {d : Nat}
    {x y : Vec d} (hxy : x ≠ y) :
    Tendsto
      (fun α : ℝ => ((euclideanNorm (x - y)) ^ (-α) - 1) / α)
      (𝓝[>] (0 : ℝ)) (𝓝 (abkLogCovarianceKernel x y)) := by
  have hdiff : x - y ≠ 0 := by
    positivity
  simpa [abkLogCovarianceKernel] using
    tendsto_rpow_neg_sub_one_div_nhdsGT_zero
      (abkEuclideanNorm_pos_of_ne_zero hdiff)

end GaussianFields

end
