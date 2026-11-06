module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.ReferenceGeometryPathBounds
import Mathlib.Tactic
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.LeakageGeometry
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.ReferenceGeometryBasic

/-! # Every local stack comparison region lies in the same buffered reference box -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth

open Set

/- All subcylinder comparison boxes share the same reference region. -/
theorem sampling_comparison_image_subset {d } (m : ℕ) (P : KineticPoint d) {r }
    (hr : 0 < r) (hsub : backwardCylinder P r ⊆ samplingCylinder d m) :
    kineticAffine P r '' stackComparisonRegion d m ⊆ referenceRegion d m (referenceBound m) := by
  obtain ⟨hr1, htlo, htup, hx, hv⟩ : r ≤ 1 ∧ -((m : ℝ) + 3) ≤ P.time ∧ P.time ≤ -((m : ℝ) + 2) ∧
      PDE.vecEuclideanNorm P.position ≤ 1 ∧ PDE.vecEuclideanNorm P.velocity ≤ 1 := by
    have hc := closure_mono hsub
      (Covering.top_mem_closure_cylinder P hr (PDE.center_mem_euclideanBall _ hr))
    have hb := sampling_closure_bounds d m P hc
    have _h_xinl_0 : (⟨P.time - r ^ 2, P.position + (-r ^ 2) • P.velocity, P.velocity⟩ : KineticPoint d) ∈ closure (backwardCylinder P r) := by
      let f : ℝ → KineticPoint d := fun t =>
        ⟨t, P.position + (t - P.time) • P.velocity, P.velocity⟩
      have hf : Continuous f := KineticPoint.continuous_mk continuous_id
        (continuous_const.add ((continuous_id.sub continuous_const).smul continuous_const))
        continuous_const
      have hsub : f '' Ioo (P.time - r ^ 2) P.time ⊆ backwardCylinder P r := by
        rintro _ ⟨t, ht, rfl⟩
        refine ⟨ht.1, ht.2, PDE.center_mem_euclideanBall _ hr, ?_⟩
        have heq : relativePosition P (f t) = 0 := by
          ext i
          simp only [relativePosition, f, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
            Pi.zero_apply, smul_eq_mul]
          ring
        rw [heq]
        exact PDE.center_mem_euclideanBall 0 (pow_pos hr 3)
      have ht : P.time - r ^ 2 ∈ closure (Ioo (P.time - r ^ 2) P.time) := by
        rw [closure_Ioo (sub_lt_self _ (sq_pos_of_pos hr)).ne]
        exact ⟨le_rfl, sub_le_self _ (sq_nonneg r)⟩
      simpa only [f, sub_sub_cancel_left] using (closure_mono hsub (hf.continuousOn.image_closure (mem_image_of_mem f ht)))
    have hbottom := (sampling_closure_bounds d m _
      (closure_mono hsub _h_xinl_0)).1
    have hr2 : r ^ 2 ≤ 1 := by linarith only [hbottom, hb.2.1]
    exact ⟨by nlinarith only [hr2, hr], hb⟩
  have hr2 : r ^ 2 ≤ 1 := by nlinarith only [hr, hr1]
  have hr3 : r ^ 3 ≤ 1 := by
    have he := mul_le_mul hr2 hr1 hr.le (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith only [he]
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have hB : 0 ≤ stackPathBound m := by unfold stackPathBound; positivity
  rintro _ ⟨Y, hY, rfl⟩
  obtain ⟨hytlo, hytup, hyx, hyv⟩ := hY
  have hytime : |Y.time| ≤ (m : ℝ) + 3 := by
    exact abs_le.mpr ⟨by linarith only [hytlo, hm], by linarith only [hytup]⟩
  have htxlo := mul_lt_mul_of_pos_left hytlo (sq_pos_of_pos hr)
  have htxup := mul_le_mul_of_nonneg_left hytup.le (sq_nonneg r)
  have htm := mul_le_mul_of_nonneg_right hr2 (show 0 ≤ (m : ℝ) + 1 by positivity)
  have hyxscaled : r ^ 3 * PDE.vecEuclideanNorm Y.position ≤ stackPathBound m + 1 := by
    have he := mul_le_mul hr3 hyx.le (PDE.vecEuclideanNorm_nonneg _) (by norm_num)
    simpa only [one_mul] using he
  have hyvscaled : r * PDE.vecEuclideanNorm Y.velocity ≤ stackPathBound m + 1 := by
    have he := mul_le_mul hr1 hyv.le (PDE.vecEuclideanNorm_nonneg _) (by norm_num)
    simpa only [one_mul] using he
  have htimescaled : r ^ 2 * |Y.time| ≤ (m : ℝ) + 3 := by
    have he := mul_le_mul hr2 hytime (abs_nonneg _) (by norm_num)
    simpa only [one_mul] using he
  have htransport : PDE.vecEuclideanNorm ((r ^ 2 * Y.time) • P.velocity) ≤ (m : ℝ) + 3 := by
    rw [PDE.vecEuclideanNorm_smul, abs_mul, abs_of_nonneg (sq_nonneg r)]
    have he := mul_le_mul_of_nonneg_left hv (mul_nonneg (sq_nonneg r) (abs_nonneg Y.time))
    simpa only [mul_one] using he.trans (by simpa only [mul_one] using htimescaled)
  refine ⟨?_, ?_, ?_, ?_⟩
  · change -((m : ℝ) + 5) < P.time + r ^ 2 * Y.time
    linarith only [htxlo, hr2, htlo]
  · change P.time + r ^ 2 * Y.time < 0
    linarith only [htup, htxup, htm]
  · change PDE.vecEuclideanNorm
        (P.position + r ^ 3 • Y.position + (r ^ 2 * Y.time) • P.velocity) < referenceBound m
    have he := PDE.vecEuclideanNorm_add_le
      (P.position + r ^ 3 • Y.position) ((r ^ 2 * Y.time) • P.velocity)
    have he' := PDE.vecEuclideanNorm_add_le P.position (r ^ 3 • Y.position)
    rw [PDE.vecEuclideanNorm_smul, abs_of_pos (pow_pos hr 3)] at he'
    dsimp only [referenceBound]
    linarith only [he, he', hx, hyxscaled, htransport, hB]
  · change PDE.vecEuclideanNorm (P.velocity + r • Y.velocity) < referenceBound m
    have he := PDE.vecEuclideanNorm_add_le P.velocity (r • Y.velocity)
    rw [PDE.vecEuclideanNorm_smul, abs_of_pos hr] at he
    dsimp only [referenceBound]
    linarith only [he, hv, hyvscaled, hB, hm]

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth
