module
public import Mathlib

public import PottsDiscontinuity.Bethe.Prop21Positivity
public import PottsDiscontinuity.Bethe.Prop21Regularity

/-! # Compact derivative estimates for the offset argument

All bounds here are for a fixed `Δ < -1`, which is the parameter scope of
Theorem 2.9. They follow from the already proved analyticity statements.
-/

@[expose] public section

open Set

namespace PottsDiscontinuity.Bethe

section

variable {Δ : ℝ} (hΔ : Δ < -1)
include hΔ

theorem exists_lipschitzOnWith_inv_rho  :
    ∃ K, LipschitzOnWith K (fun x => (rho Δ x)⁻¹) (Icc (-Real.pi) Real.pi) := ContDiffOn.exists_lipschitzOnWith
                                                                                (ContDiff.contDiffOn
                                                                                  (contDiff_iff_contDiffAt.mpr fun x =>
                                                                                    AnalyticAt.contDiffAt ((fun x => AnalyticAt.inv (analyticAt_rho hΔ x) (LT.lt.ne' (rho_pos hΔ x))) x)))
                                                                                one_ne_zero (convex_Icc (-Real.pi) Real.pi) isCompact_Icc

/-- The derivative of the two-variable phase is Lipschitz on the physical
square. This supplies a uniform quadratic Taylor remainder. -/
theorem exists_lipschitzOnWith_fderiv_theta  :
    ∃ K, LipschitzOnWith K (fderiv ℝ  fun z : ℝ × ℝ => theta Δ z.1 z.2 )
      ( Icc (-Real.pi) Real.pi  ×ˢ  Icc (-Real.pi) Real.pi ) := by
  have h : ContDiff ℝ 2  fun z : ℝ × ℝ => theta Δ z.1 z.2  :=
    contDiff_iff_contDiffAt.mpr  fun z => (analyticAt_theta_xy hΔ z.1 z.2).contDiffAt 
  
  exact (h.fderiv_right (by norm_num)).contDiffOn.exists_lipschitzOnWith one_ne_zero
    ((convex_Icc _ _).prod (convex_Icc _ _)) (isCompact_Icc.prod isCompact_Icc)

/-- A single constant bounds all second-order remainders on the physical
square; it depends only on the fixed phase parameter. -/
theorem theta_quadratic_remainder  :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈   Icc (-Real.pi) Real.pi  ×ˢ  Icc (-Real.pi) Real.pi  ,
      ∀ y ∈   Icc (-Real.pi) Real.pi  ×ˢ  Icc (-Real.pi) Real.pi  ,
      |theta Δ y.1 y.2 - theta Δ x.1 x.2 -
        fderiv ℝ (fun z : ℝ × ℝ => theta Δ z.1 z.2) x (y - x)| ≤ K * ‖y - x‖ ^ 2 := by
  obtain ⟨K, hK⟩ := exists_lipschitzOnWith_fderiv_theta hΔ
  refine ⟨K, K.coe_nonneg, ?_⟩
  intro x hx y hy
  
  have hconv : Convex ℝ ( Icc (-Real.pi) Real.pi  ×ˢ  Icc (-Real.pi) Real.pi ) :=
    (convex_Icc _ _).prod (convex_Icc _ _)
  
  have hd (z : ℝ × ℝ) (_hz : z ∈ segment ℝ x y)  :=
    (analyticAt_theta_xy hΔ z.1 z.2).differentiableAt
  
  have hb := (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le' hd  fun z hz => by
                                                                             have hb := hK.dist_le_mul z ((hconv.segment_subset hx hy) hz) x hx
                                                                             rw [dist_eq_norm] at hb
                                                                             exact hb.trans (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hz) K.coe_nonneg) 
    (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  simpa only [Real.norm_eq_abs, pow_two, mul_assoc] using hb

end

end PottsDiscontinuity.Bethe
