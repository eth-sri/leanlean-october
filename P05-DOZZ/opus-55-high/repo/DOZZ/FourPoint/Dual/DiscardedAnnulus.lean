/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.DeletedDiskRooted
public import DOZZ.FourPoint.Dual.MassComparison
import Mathlib.Tactic
/-! The actual intermediate annulus is dominated by the rooted deleted zero-kernel disk. -/
@[expose] public section
open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace DOZZ.Proofs

/-- Away from a disk proportional to the moving root, the dual density is at most a fixed
multiple of the zero density, with no condition on the other charges. -/
theorem dual_kernel_relative_upper (γ α₁ α₂ α₃ R : ℝ) (_hR : 0 ≤ R) (z x : ℂ)
    (hsep : ‖z‖ ≤ R*‖x‖) :
    dualFusionKernel γ α₁ α₂ α₃ z x ≤
      (1+R)^2*dualFusionKernel γ α₁ α₂ α₃ 0 x := by
  have hn : ‖x-z‖ ≤ (1+R)*‖x‖ := by
    calc
      _ ≤ ‖x‖+‖z‖ := norm_sub_le ..
      _ ≤ ‖x‖+R*‖x‖ := add_le_add le_rfl hsep
      _ = _ := by ring
  have hs :=
    pow_le_pow_left₀ (norm_nonneg _) hn 2
  let W := normPlus x^(γ*(α₁+α₂+α₃-2/γ)) /
    (‖x‖^(γ*α₁)*‖x-1‖^(γ*α₂))
  have hp : 0 ≤ normPlus x := (zero_lt_one.trans_le (le_max_left ..)).le
  have hW : 0 ≤ W := by positivity
  have hm := mul_le_mul_of_nonneg_right hs hW
  unfold dualFusionKernel
  simp
  grind

/-- The literal intermediate annular mass is bounded by a multiple of the deleted zero disk
for any measure, before averaging. -/
theorem dual_discarded_annulus_mass_bound (γ α₁ α₂ α₃ h r : ℝ)
    (z : ℂ) (μ : Measure ℂ) :
    (∫⁻ x in {x : ℂ | Real.exp (-h)*‖z‖ ≤ ‖x‖ ∧ ‖x‖ < r},
      ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x) ∂μ) ≤
      ENNReal.ofReal ((1+Real.exp h)^2)*
        ∫⁻ x in Metric.ball (0 : ℂ) r, ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ 0 x) ∂μ := by
  let D := {x : ℂ | Real.exp (-h)*‖z‖ ≤ ‖x‖ ∧ ‖x‖ < r}
  have hD : MeasurableSet D :=
    by measurability
  have hsub : D ⊆ Metric.ball 0 r := by
    intro x hx
    aesop
  calc
    _ ≤ ∫⁻ x in D, ENNReal.ofReal _*
        ENNReal.ofReal _ ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hD] with x hx
      have hsep : ‖z‖ ≤ Real.exp h*‖x‖ := by
        have hb := mul_le_mul_of_nonneg_left hx.1 (Real.exp_pos h).le
        rwa [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul] at hb
      rw [← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal (dual_kernel_relative_upper γ α₁ α₂ α₃
        (Real.exp h) (Real.exp_pos _).le z x hsep)
    _ = ENNReal.ofReal _*
        ∫⁻ x in D, ENNReal.ofReal _ ∂μ :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := mul_le_mul' le_rfl (lintegral_mono_set hsub)

/-- Rooted inverse weighting makes the intermediate annulus negligible at the dual scale. -/
theorem dual_discarded_annulus_rooted_littleO
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ q ξ κ h : ℝ) (hq : 0 ≤ q) (hβ : γ*α₁ < 4) (hξ1 : ξ < 1)
    (hslack : κ < (1-ξ)*(4-γ*α₁)) :
    Tendsto (fun z : ℂ =>
      (∫⁻ ω, (∫⁻ x in {x : ℂ | Real.exp (-h)*‖z‖ ≤ ‖x‖ ∧ ‖x‖ < ‖z‖^(1-ξ)},
        ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x) ∂M ω)*
          dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^(-q) ∂P).toReal / ‖z‖^κ)
      (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
  let C := (1+Real.exp h)^2
  let F := fun z => ∫⁻ ω, (∫⁻ x in Metric.ball (0 : ℂ) (‖z‖^(1-ξ)),
    ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ 0 x) ∂M ω)*
      dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^(-q) ∂P
  have ht := dual_deleted_disk_rooted_littleO P X hX γ hγ hγ₂ M hM
    α₁ α₂ α₃ q ξ κ hq hβ hξ1 hslack
  have hmajor := ht.const_mul C
  simp at hmajor
  apply squeeze_zero' (Eventually.of_forall fun z =>
    div_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg (norm_nonneg z) κ)) ?_ hmajor
  obtain ⟨C₀, _, hb⟩ := dual_deleted_disk_rooted_bound P X hX γ hγ hγ₂ M hM
    α₁ α₂ α₃ q hq hβ
  have hn : Tendsto (fun z => ‖z‖) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    simpa using (continuous_norm.tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds
  have hr : Tendsto (fun z => ‖z‖^(1-ξ)) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    simpa only [Function.comp_def, Real.zero_rpow (sub_pos.mpr hξ1).ne'] using
      ((Real.continuous_rpow_const (sub_nonneg.mpr hξ1.le)).tendsto (0 : ℝ)).comp hn
  filter_upwards [self_mem_nhdsWithin, hn.eventually (gt_mem_nhds zero_lt_one),
    hr.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2))] with z hz0 hz hcut
  have hfin : F z ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (hb z ξ _ hz.le (by linarith)
      (Real.rpow_pos_of_pos (norm_pos_iff.mpr hz0) _) hcut.le)
  have he : (∫⁻ ω, (∫⁻ x in {x : ℂ | Real.exp (-h)*‖z‖ ≤ ‖x‖ ∧ ‖x‖ < ‖z‖^(1-ξ)},
      ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x) ∂M ω)*
        dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^(-q) ∂P) ≤ ENNReal.ofReal C*F z := by
    calc
      _ ≤ ∫⁻ ω, (ENNReal.ofReal C*(∫⁻ x in Metric.ball (0 : ℂ) _,
        ENNReal.ofReal _ ∂M ω))*
          dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^(-q) ∂P :=
        lintegral_mono fun ω => mul_le_mul' (dual_discarded_annulus_mass_bound
          γ α₁ α₂ α₃ h _ z (M ω)) le_rfl
      _ = _ := by simp_rw [mul_assoc]; exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hre := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) he
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at hre
  simpa only [mul_div_assoc] using (div_le_div_of_nonneg_right hre (Real.rpow_nonneg (norm_nonneg z) κ))

end DOZZ.Proofs
