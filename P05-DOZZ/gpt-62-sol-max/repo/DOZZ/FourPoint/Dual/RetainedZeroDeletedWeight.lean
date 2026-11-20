/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.RetainedZeroRootedInverse
public import DOZZ.FourPoint.Dual.DeletedDisk
import Mathlib.Tactic
public import DOZZ.FourPoint.TaylorOneRootIdentity
/-! # The deleted-disk bound weighted by the retained zero mass -/
public section
open MeasureTheory Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- The zero retained inverse weight has the deleted-disk power, uniformly at all
small radii, by the literal rooted identity and actual spatial integral. -/
theorem dual_retainedZero_deleted_weight_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ q : ℝ) (hq : 0 ≤ q) (hβ : γ * α₁ < 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → r ≤ 1 / 2 →
      (∫⁻ ω, (∫⁻ x in Metric.ball (0 : ℂ) r,
        ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ 0 x) ∂M ω) *
          dualRetainedZeroMass γ α₁ α₂ α₃ r (M ω) ^ (-q) ∂P) ≤
            ENNReal.ofReal (C * r ^ (4 - γ * α₁)) := by
  obtain ⟨C₁, hC₁, hb⟩ := dual_rooted_retainedZero_inverse_moment_uniform
    P X hX γ hγ hγ₂ M hM α₁ α₂ α₃ q hq
  obtain ⟨C₂, hC₂, hs⟩ := dual_deleted_disk_spatial_bound γ α₁ α₂ α₃ hβ
  refine ⟨C₁ * C₂, mul_pos hC₁ hC₂, ?_⟩
  intro r hr hr₁
  have hG := (retainedZeroMass_measurable γ (-2 / γ) α₁ α₂ α₃ r).pow_const (-q)
  refine (rooted_set_weight_le P X hX γ hγ hγ₂ M hM measurableSet_ball
    (dual_kernel_measurable γ α₁ α₂ α₃ 0) hG
    (C := ENNReal.ofReal C₁) (fun u _ => hb u r (by linarith))).trans ?_
  exact (mul_le_mul' le_rfl (hs r hr hr₁)).trans_eq (by
    rw [← ENNReal.ofReal_mul hC₁.le, mul_assoc])

end DOZZ.Proofs
