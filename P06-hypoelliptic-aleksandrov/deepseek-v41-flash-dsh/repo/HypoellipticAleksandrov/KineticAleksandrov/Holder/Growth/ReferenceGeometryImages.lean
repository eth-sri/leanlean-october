module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.ReferenceGeometryPathBounds
import Mathlib.Tactic

/-! # Every local stack comparison region lies in the same buffered reference box -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth

open Set

/-- All subcylinder comparison boxes share the same reference region. -/
theorem sampling_comparison_image_subset {d : ℕ} (m : ℕ) (P : KineticPoint d) {r : ℝ}
    (hr : 0 < r) (hsub : backwardCylinder P r ⊆ samplingCylinder d m) :
    kineticAffine P r '' stackComparisonRegion d m ⊆ referenceRegion d m (referenceBound m) := by
  obtain ⟨hr1, htlo, htup, hx, hv⟩ := sampling_subcylinder_bounds m P hr hsub
  have hr2 : r ^ 2 ≤ 1 := by nlinarith
  have hr3 : r ^ 3 ≤ 1 := by
    have he := mul_le_mul hr2 hr1 hr.le (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have hB : 0 ≤ stackPathBound m := by unfold stackPathBound; positivity
  rintro _ ⟨Y, hY, rfl⟩
  obtain ⟨hytlo, hytup, hyx, hyv⟩ := hY
  have hytime : |Y.time| ≤ (m : ℝ) + 3 := by
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have htxlo := mul_lt_mul_of_pos_left hytlo (sq_pos_of_pos hr)
  have htxup := mul_le_mul_of_nonneg_left hytup.le (sq_nonneg r)
  have htm := mul_le_mul_of_nonneg_right hr2 (show 0 ≤ (m : ℝ) + 1 by positivity)
  have hyxscaled : r ^ 3 * PDE.vecEuclideanNorm Y.position ≤ stackPathBound m + 1 := by
    have he := mul_le_mul hr3 hyx.le (PDE.vecEuclideanNorm_nonneg _) (by norm_num)
    simpa using he
  have hyvscaled : r * PDE.vecEuclideanNorm Y.velocity ≤ stackPathBound m + 1 := by
    have he := mul_le_mul hr1 hyv.le (PDE.vecEuclideanNorm_nonneg _) (by norm_num)
    simpa using he
  have htimescaled : r ^ 2 * |Y.time| ≤ (m : ℝ) + 3 := by
    have he := mul_le_mul hr2 hytime (abs_nonneg _) (by norm_num)
    simpa using he
  have htransport : PDE.vecEuclideanNorm ((r ^ 2 * Y.time) • P.velocity) ≤ (m : ℝ) + 3 := by
    rw [PDE.vecEuclideanNorm_smul, abs_mul, abs_of_nonneg (sq_nonneg r)]
    have he := mul_le_mul_of_nonneg_left hv (mul_nonneg (sq_nonneg r) (abs_nonneg Y.time))
    simpa using he.trans (by simpa using htimescaled)
  refine ⟨?_, ?_, ?_, ?_⟩
  · change -((m : ℝ) + 5) < P.time + r ^ 2 * Y.time
    linarith
  · change P.time + r ^ 2 * Y.time < 0
    linarith
  · change PDE.vecEuclideanNorm
        (P.position + r ^ 3 • Y.position + (r ^ 2 * Y.time) • P.velocity) < referenceBound m
    have he := PDE.vecEuclideanNorm_add_le
      (P.position + r ^ 3 • Y.position) ((r ^ 2 * Y.time) • P.velocity)
    have he' := PDE.vecEuclideanNorm_add_le P.position (r ^ 3 • Y.position)
    rw [PDE.vecEuclideanNorm_smul, abs_of_pos (pow_pos hr 3)] at he'
    dsimp only [referenceBound]
    linarith
  · change PDE.vecEuclideanNorm (P.velocity + r • Y.velocity) < referenceBound m
    have he := PDE.vecEuclideanNorm_add_le P.velocity (r • Y.velocity)
    rw [PDE.vecEuclideanNorm_smul, abs_of_pos hr] at he
    dsimp only [referenceBound]
    linarith

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth
