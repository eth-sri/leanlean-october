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

/-- Scalar multiplication preserves the Gaussian closure on the same field. -/
theorem IsGaussianL2Limit_const_mul_symmetry
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    L (hL : IsGaussianL2Limit P X L) t :
    IsGaussianL2Limit P X (fun ω => t * L ω) := by
  obtain ⟨hmem, f, hf⟩ := hL
  refine ⟨hmem.const_mul t, (fun n => t • f n), ?_⟩
  have he n : (fun ω => t * L ω - X ω (t • f n)) =
      t • (fun ω => L ω - X ω (f n)) := by
    funext ω
    rw [map_smul]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hnorm n : eLpNorm (fun ω => t * L ω - X ω (t • f n)) 2 P =
      ‖t‖ₑ * eLpNorm (fun ω => L ω - X ω (f n)) 2 P := by
    rw [he, eLpNorm_const_smul]
  simp only [hnorm]
  simpa only [mul_zero] using ENNReal.Tendsto.const_mul hf (Or.inr enorm_ne_top)


theorem symmetry_gaussianVariance_mul
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (L : Ω → ℝ) t :
    gaussianVariance P (fun ω => t * L ω) = t ^ 2 * gaussianVariance P L := by
  unfold gaussianVariance gaussianCovariance
  rw [(show (fun ω => (t * L ω) * (t * L ω)) = fun ω => t ^ 2 * (L ω * L ω) by funext ω; ring), integral_const_mul]

/-- The bounded correlation potential for the scaled normalization. -/
noncomputable def symmetryTiltPotential (t : ℝ) : BoundedContinuousFunction ℂ ℝ :=
  t • (symmetryReflectionPotentialBCF - BoundedContinuousFunction.const ℂ symmetryReflectionKappa)

theorem symmetryTiltPotential_apply t x :
    symmetryTiltPotential t x = t * (symmetryReflectionPotential x - symmetryReflectionKappa) := rfl

/-- All scaled correlated normalizations supply the literal uniform covariance premise of tilt. -/
theorem symmetryTiltPotential_uniform
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) X
    (hX : IsEquatorGFF P X) Xc (hXc : IsCircleAverage P X Xc) t :
    TendstoUniformly (fun r x => gaussianCovariance P
      (fun ω => Xc ω (1 - x) r - Xc ω 1 0) (fun ω => t * Xc ω 1 0))
      (symmetryTiltPotential t) atTop := by
  have symmetry_gaussianCovariance_mul_right (P : Measure Ω) (A : Ω → ℝ) (L : Ω → ℝ) t : gaussianCovariance P A (fun ω => t * L ω) = t * gaussianCovariance P A L := by
    unfold gaussianCovariance
    rw [(show (fun ω => A ω * (t * L ω)) = fun ω => t * (A ω * L ω) by funext ω; ring), integral_const_mul]
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [(show Tendsto (fun r => |t| * (2 * Real.exp (-r))) atTop (𝓝 0) by simpa only [mul_zero, Function.comp_def] using (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).const_mul 2 |>.const_mul |t|).eventually (gt_mem_nhds hε)] with r hr x
  rw [symmetry_gaussianCovariance_mul_right, repinned_circle_normalization_covariance P X hX Xc hXc,
    symmetryTiltPotential_apply, Real.dist_eq, ← mul_sub, abs_mul]
  exact (mul_le_mul_of_nonneg_left (by rw [sub_sub_sub_cancel_right, abs_sub_comm]; exact symmetryReflection_circle_potential_error x r) (abs_nonneg t)).trans_lt hr
end DOZZ.Proofs
