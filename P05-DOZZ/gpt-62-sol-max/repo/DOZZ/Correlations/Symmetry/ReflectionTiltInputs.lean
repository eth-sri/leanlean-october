/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Correlations.Symmetry.ReflectionChaosIdentification
public import DOZZ.Statements.GMC.EquatorGFFGMCTilt
@[expose] public section
open MeasureTheory Filter
open scoped Distributions Topology ENNReal
namespace DOZZ.Proofs

/-- The bounded correlation potential for the scaled normalization. -/
noncomputable def symmetryTiltPotential (t : ℝ) : BoundedContinuousFunction ℂ ℝ :=
  t • (symmetryReflectionPotentialBCF - BoundedContinuousFunction.const ℂ symmetryReflectionKappa)

theorem symmetryTiltPotential_apply (t : ℝ) (x : ℂ) :
    symmetryTiltPotential t x = t * (symmetryReflectionPotential x - symmetryReflectionKappa) := rfl

/-- All scaled correlated normalizations supply the literal uniform covariance premise of tilt. -/
theorem symmetryTiltPotential_uniform
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (t : ℝ) :
    TendstoUniformly (fun r x => gaussianCovariance P
      (fun ω => Xc ω (1 - x) r - Xc ω 1 0) (fun ω => t * Xc ω 1 0))
      (symmetryTiltPotential t) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have he : Tendsto (fun r : ℝ => |t| * (2 * Real.exp (-r))) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).const_mul 2 |>.const_mul |t|
  filter_upwards [he.eventually (gt_mem_nhds hε)] with r hr x
  rw [gaussianCovariance_const_mul_right, repinned_circle_normalization_covariance P X hX Xc hXc,
    symmetryTiltPotential_apply, Real.dist_eq, ← mul_sub, abs_mul]
  exact (mul_le_mul_of_nonneg_left (by
    rw [sub_sub_sub_cancel_right, abs_sub_comm]
    exact symmetryReflection_circle_potential_error x r) (abs_nonneg t)).trans_lt hr
end DOZZ.Proofs
