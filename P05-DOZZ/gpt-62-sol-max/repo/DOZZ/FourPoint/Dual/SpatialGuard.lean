/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.SpatialKernel
public import DOZZ.FourPoint.Dual.OuterInverseGuard
public import DOZZ.FourPoint.Fusion.RetainedInverseMass
/-! The compact guard used in spatial cutoff removal has actual GMC inverse moments. -/
@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- A closed disk about three retains the same lower mass as the fixed exterior open disk. -/
theorem dual_spatial_guard_lower (γ α₁ α₂ α₃ : ℝ) (μ : Measure ℂ)
    (hγ : γ ≠ 0) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ENNReal.ofReal ((2 : ℝ)^(-∑ i : Fin 3, |γ*(![-2/γ, α₁, α₂] : Fin 3 → ℝ) i|)*
      (4 : ℝ)^(-|γ*α₃|))*μ (Metric.ball (3 : ℂ) (1/8)) ≤
      ∫⁻ x in Metric.closedBall (3 : ℂ) (1/8),
        ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x) ∂μ := by
  have he := dual_kernel_integral_eq_coulombMass γ α₁ α₂ α₃ hγ z (μ.restrict _)
    (fixed_guard_restrict_singleton μ hz) (fixed_guard_restrict_singleton μ (by simp))
    (fixed_guard_restrict_singleton μ (by simp))
  have h := coulombMass_fixed_disk_lower_restrict γ μ ![-2 / γ, α₁, α₂] ![z, 0, 1] α₃
    (three_roots_in_unit_disk hz) Metric.ball_subset_closedBall
  exact he.symm ▸ h

section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
  (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (α₁ α₂ α₃ q : ℝ)
  (hq : 0 ≤ q)
include Ω X hX hγ hγ₂ hM hq

/-- The compact guard inverse moment is finite for every nonnegative order, uniformly for
moving roots in the unit disk, directly from the ball moment bound. -/
theorem dual_spatial_guard_inverse_uniform
    : ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, ‖z‖ ≤ 1 →
    (∫⁻ ω, (∫⁻ x in Metric.closedBall (3 : ℂ) (1/8),
      ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x) ∂M ω)^(-q) ∂P) ≤ ENNReal.ofReal C := by
  obtain ⟨C, hC, h⟩ := inverse_fixed_disk_uniform P X hX γ hγ hγ₂ M hM _ q
    (outerGuardWeight_pos γ (-2 / γ) α₁ α₂ α₃) hq
  exact ⟨C, hC, fun z hz => h _ fun ω => dual_spatial_guard_lower γ α₁ α₂ α₃ (M ω) hγ.ne' z hz⟩

/-- The compact guard inverse moment is finite for every nonnegative order, uniformly for
moving roots in the unit disk, directly from the ball moment bound. -/
theorem dual_spatial_guard_inverse_finite
    (z : ℂ) (hz : ‖z‖ ≤ 1) :
    (∫⁻ ω, (∫⁻ x in Metric.closedBall (3 : ℂ) (1/8),
      ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x) ∂M ω)^(-q) ∂P) < ⊤ := by
  obtain ⟨C, _, hb⟩ := dual_spatial_guard_inverse_uniform P X hX γ hγ hγ₂ M hM
    α₁ α₂ α₃ q hq
  exact (hb z hz).trans_lt ENNReal.ofReal_lt_top

end

end DOZZ.Proofs
