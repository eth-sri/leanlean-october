module

public import DOZZ.Statements.Defs.GffKernel

/-! Deterministic inversion identities used by the infinity chart. -/

@[expose] public section

namespace DOZZ.Proofs
section
variable {u : ℂ}
section
variable (hu : u ≠ 0)
include hu

/-- `normPlus` has the expected inversion factor. -/
theorem normPlus_inv_identity :
    normPlus u⁻¹ = normPlus u / ‖u‖ := by
  have hρ := norm_pos_iff.mpr hu
  have hnorm := norm_inv u
  unfold normPlus
  by_cases h : ‖u‖ ≤ 1
  · rw [hnorm, max_eq_right ((one_le_inv₀ hρ).2 h), max_eq_left h]
    simp
  · have h' := le_of_not_ge h
    rw [hnorm, max_eq_left ((inv_le_one₀ hρ).2 h'), max_eq_right h']
    simp_all

/-- The compactifying reference density transforms with the planar inversion Jacobian. -/
theorem normPlus_inv_mul_jacobian :
    normPlus u⁻¹ ^ (-4 : ℝ) * ‖u‖ ^ (-4 : ℝ) = normPlus u ^ (-4 : ℝ) := by
  have hnpu : 0 < normPlus u := by
    unfold normPlus
    simp
  have hnpinv : 0 < normPlus u⁻¹ := by
    unfold normPlus
    simp
  rw [(normPlus_inv_identity hu), Real.div_rpow hnpu.le (norm_pos_iff.mpr hu).le (-4)]
  simp_all

end

end

/-- A finite root distance in the original chart becomes the corresponding linear factor after
inversion. -/
theorem inversion_distance {u z : ℂ} (hu : u ≠ 0) :
    ‖u⁻¹ - z‖ = ‖1 - z * u‖ / ‖u‖ := by
  have h : u⁻¹ - z = (1 - z * u) / u := by
    field_simp
  simp_all

/-- The logarithmic equator covariance kernel is invariant under inversion away from its poles. -/
theorem gffKernel_inv {u v : ℂ} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) :
    gffKernel u⁻¹ v⁻¹ = gffKernel u v := by
  have hρu := norm_pos_iff.mpr hu
  have hρv := norm_pos_iff.mpr hv
  have hdiff : u⁻¹ - v⁻¹ = (v - u) / (u * v) := by
    field_simp
  have hdist : ‖u⁻¹ - v⁻¹‖ = ‖u - v‖ / (‖u‖ * ‖v‖) := by
    rw [hdiff, norm_div, norm_mul, norm_sub_rev]
  have hlogdist : Real.log (‖u - v‖ / (‖u‖ * ‖v‖)) =
      Real.log ‖u - v‖ - Real.log ‖u‖ - Real.log ‖v‖ := by
    rw [Real.log_div (ne_of_gt (norm_pos_iff.mpr (sub_ne_zero.mpr huv))) (ne_of_gt (mul_pos hρu hρv)), Real.log_mul
      (ne_of_gt hρu) (ne_of_gt hρv)]
    ring
  have hlogu : Real.log (normPlus u / ‖u‖) =
      Real.log (normPlus u) - Real.log ‖u‖ :=
    Real.log_div (ne_of_gt (by unfold normPlus; positivity)) (ne_of_gt hρu)
  have hlogv : Real.log (normPlus v / ‖v‖) =
      Real.log (normPlus v) - Real.log ‖v‖ :=
    Real.log_div (ne_of_gt (by unfold normPlus; positivity)) (ne_of_gt hρv)
  rw [gffKernel, gffKernel, hdist, normPlus_inv_identity hu, normPlus_inv_identity hv,
    hlogdist, hlogu, hlogv]
  ring

end DOZZ.Proofs
