/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Construction.GMCRootedIdentity
public import DOZZ.GFFStructure.CircleCovariance
public import DOZZ.GMC.CirclePotential

/-! Point-root covariance is the small-radius limit of the circle-root covariance. -/

@[expose] public section

open MeasureTheory Filter Topology
open scoped Distributions

namespace DOZZ.Proofs

/-- As the circle shrinks to its center, its covariance with a smooth test converges to the
point-root covariance used in the rooted GMC identity. -/
theorem circleCross_tendsto_gffRootCovariance
    u f :
    Tendsto (fun r : ℝ => circleCross u r f) atTop
      (𝓝 (gffRootCovariance u f)) := by
  let k : ℂ → ℝ := fun z => gffRootCovariance z f
  have hk := gffRootCovariance_continuous f
  have hcross r : circleCross u r f =
      ∫ z, k z ∂circleMeasure u r := by
    rw [circleCross_eq_integral_testKernel]
    apply integral_congr_ae
    filter_upwards with z
    rfl
  have haverage (r : ℝ) := CirclePotential.integral_circleMeasure_eq_circleAverage hk.measurable u r
  simpa [k, hcross, haverage, (show Real.circleAverage k u 0 = k u by simp [k])] using (show Tendsto (fun r => Real.circleAverage k u (Real.exp (-r))) atTop (𝓝 (Real.circleAverage k u 0)) by exact (Real.Continuous.circleAverage hk).continuousAt.tendsto.comp (by simpa using Real.tendsto_exp_neg_atTop_nhds_zero))


end DOZZ.Proofs
