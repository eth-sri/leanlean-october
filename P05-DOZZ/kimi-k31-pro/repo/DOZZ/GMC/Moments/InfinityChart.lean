
import DOZZ.Statements.Defs.GffKernel

/-! Deterministic inversion identities used by the infinity chart. -/


namespace DOZZ.Proofs

/-- `normPlus` has the expected inversion factor. -/
theorem normPlus_inv_identity {u : ℂ} (hu : u ≠ 0) :
    normPlus u⁻¹ = normPlus u / ‖u‖ := by
  have hρ : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hnorm : ‖u⁻¹‖ = ‖u‖⁻¹ := norm_inv u
  unfold normPlus
  by_cases h : ‖u‖ ≤ 1
  · rw [hnorm, max_eq_right ((one_le_inv₀ hρ).2 h), max_eq_left h]
    simp [one_div]
  · have h' : 1 ≤ ‖u‖ := le_of_not_ge h
    rw [hnorm, max_eq_left ((inv_le_one₀ hρ).2 h'), max_eq_right h']
    simp [hρ.ne']

/-- The compactifying reference density transforms with the planar inversion Jacobian. -/
theorem normPlus_inv_mul_jacobian {u : ℂ} (hu : u ≠ 0) :
    normPlus u⁻¹ ^ (-4 : ℝ) * ‖u‖ ^ (-4 : ℝ) = normPlus u ^ (-4 : ℝ) := by
  have hρ : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hnpu : 0 < normPlus u := by
    unfold normPlus
    exact lt_of_lt_of_le zero_lt_one (le_max_left 1 ‖u‖)
  have hinv : normPlus u⁻¹ = normPlus u / ‖u‖ := normPlus_inv_identity hu
  rw [hinv, Real.div_rpow hnpu.le hρ.le (-4)]
  exact div_mul_cancel₀ _ (ne_of_gt (Real.rpow_pos_of_pos hρ (-4)))

/-- A finite root distance in the original chart becomes the corresponding linear factor after
inversion. -/
theorem inversion_distance {u z : ℂ} (hu : u ≠ 0) :
    ‖u⁻¹ - z‖ = ‖1 - z * u‖ / ‖u‖ := by
  have h : u⁻¹ - z = (1 - z * u) / u := by
    field_simp [hu]
  rw [h, norm_div]

/-- The logarithmic equator covariance kernel is invariant under inversion away from its poles. -/
theorem gffKernel_inv {u v : ℂ} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) :
    gffKernel u⁻¹ v⁻¹ = gffKernel u v := by
  have hρu : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hρv : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hd : 0 < ‖u - v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr huv)
  have hρ : 0 < ‖u‖ * ‖v‖ := mul_pos hρu hρv
  have hdiff : u⁻¹ - v⁻¹ = (v - u) / (u * v) := by
    field_simp [hu, hv]
  have hdist : ‖u⁻¹ - v⁻¹‖ = ‖u - v‖ / (‖u‖ * ‖v‖) := by
    rw [hdiff, norm_div, norm_mul, norm_sub_rev]
  have hlogdist : Real.log (‖u - v‖ / (‖u‖ * ‖v‖)) =
      Real.log ‖u - v‖ - Real.log ‖u‖ - Real.log ‖v‖ := by
    rw [Real.log_div (ne_of_gt hd) (ne_of_gt hρ), Real.log_mul
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
