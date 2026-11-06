module

public import DOZZ.Statements.Defs.GffKernel

/-! Deterministic inversion identities used by the infinity chart. -/

@[expose] public section

namespace DOZZ.Proofs

/-- `normPlus` has the expected inversion factor. -/
theorem normPlus_inv_identity {u} (hu : u ≠ 0) :
    normPlus u⁻¹ = normPlus u / ‖u‖ := by
  have hρ := norm_pos_iff.mpr hu
  have hnorm := norm_inv u
  unfold normPlus
  by_cases h : ‖u‖ ≤ 1
  · rw [hnorm, max_eq_right ((one_le_inv₀ hρ).2 h), max_eq_left h]
    simp [one_div]
  · have h' : 1 ≤ ‖u‖ := le_of_not_ge h
    rw [hnorm, max_eq_left ((inv_le_one₀ hρ).2 h'), max_eq_right h']
    simp [hρ.ne']

/-- The compactifying reference density transforms with the planar inversion Jacobian. -/
theorem normPlus_inv_mul_jacobian {u} (hu : u ≠ 0) :
    normPlus u⁻¹ ^ (-4 : ℝ) * ‖u‖ ^ (-4 : ℝ) = normPlus u ^ (-4 : ℝ) := by
  have hρ := norm_pos_iff.mpr hu
  rw [(normPlus_inv_identity hu), Real.div_rpow (show 0 < normPlus u by unfold normPlus; exact lt_of_lt_of_le zero_lt_one (le_max_left 1 ‖u‖)).le hρ.le (-4)]
  exact div_mul_cancel₀ _ (ne_of_gt (Real.rpow_pos_of_pos hρ (-4)))

/-- A finite root distance in the original chart becomes the corresponding linear factor after
inversion. -/
theorem inversion_distance {u z : ℂ} (hu : u ≠ 0) :
    ‖u⁻¹ - z‖ = ‖1 - z * u‖ / ‖u‖ := by
  rw [(show u⁻¹ - z = (1 - z * u) / u by field_simp [hu]), norm_div]

/-- The logarithmic equator covariance kernel is invariant under inversion away from its poles. -/
theorem gffKernel_inv {u v} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) :
    gffKernel u⁻¹ v⁻¹ = gffKernel u v := by
  have hρu := norm_pos_iff.mpr hu
  have hρv := norm_pos_iff.mpr hv
  rw [gffKernel, gffKernel, (show ‖u⁻¹ - v⁻¹‖ = ‖u - v‖ / (‖u‖ * ‖v‖) by rw [(show u⁻¹ - v⁻¹ = (v - u) / (u * v) by field_simp [hu, hv]), norm_div, norm_mul, norm_sub_rev]), normPlus_inv_identity hu, normPlus_inv_identity hv,
    (show Real.log (‖u - v‖ / (‖u‖ * ‖v‖)) = Real.log ‖u - v‖ - Real.log ‖u‖ - Real.log ‖v‖ by rw [Real.log_div (ne_of_gt (norm_pos_iff.mpr (sub_ne_zero.mpr huv))) (ne_of_gt (mul_pos hρu hρv)), Real.log_mul (ne_of_gt hρu) (ne_of_gt hρv)]; ring), (Real.log_div (ne_of_gt (by unfold normPlus; positivity)) (ne_of_gt hρu)), (Real.log_div (ne_of_gt (by unfold normPlus; positivity)) (ne_of_gt hρv))]
  ring

end DOZZ.Proofs
