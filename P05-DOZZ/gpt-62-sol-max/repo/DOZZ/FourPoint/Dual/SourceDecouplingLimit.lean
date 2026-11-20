/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.SourceDecouplingBound
public import DOZZ.FourPoint.Reflected.Remainder
import Mathlib.Tactic
public import DOZZ.GFFStructure.ContinuousCircleAverage
/-! Actual lateral decoupling is negligible at the prescribed dual fusion exponent. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
namespace DOZZ.Proofs

/-- The restarted inner radius divided by the retained exterior radius. -/
theorem dual_restart_radius_ratio (z : ℂ) (hz : z ≠ 0) (h ξ : ℝ) :
    (Real.exp (-h)*‖z‖)/‖z‖^(1-ξ) = Real.exp (-h)*‖z‖^ξ := by
  have hn := norm_pos_iff.mpr hz
  have hr := Real.rpow_pos_of_pos hn (1-ξ)
  have he : ‖z‖ = ‖z‖^(1-ξ)*‖z‖^ξ := by
    rw [← Real.rpow_add hn, sub_add_cancel, Real.rpow_one]
  have hratio : ‖z‖/‖z‖^(1-ξ) = ‖z‖^ξ := by
    calc
      _ = (‖z‖^(1-ξ)*‖z‖^ξ)/‖z‖^(1-ξ) := congrArg (fun y => y/‖z‖^(1-ξ)) he
      _ = _ := mul_div_cancel_left₀ _ hr.ne'
  rw [mul_div_assoc, hratio]

/-- The separated inverse moment differs from the independent-copy moment by little-o
at every exponent below `ξ`, for any version of the lateral carrier. -/
theorem dual_source_decoupling_littleO
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hcircle : IsContinuousCircleAverage P X Xc)
    (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (N : Ω → Measure ℂ) (hN : N =ᵐ[P] (fun ω =>
      (M ω).withDensity (lateralRadialWeight γ (originRadialPath Xc ω))))
    (α₁ α₂ α₃ q h ξ κ : ℝ) (hq : 0 < q) (hξ : 0 < ξ) (hξ1 : ξ < 1) (hκ : κ < ξ) :
    Tendsto (fun z : ℂ =>
      ((dualSeparatedInverseMoment P M γ α₁ α₂ α₃ q z
        (Real.exp (-h)*‖z‖) (‖z‖^(1-ξ))).toReal-
       (dualCopiedSeparatedInverseMoment P Xc N γ α₁ α₂ α₃ q z
        (Real.exp (-h)*‖z‖) (‖z‖^(1-ξ))).toReal)/‖z‖^κ)
      (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
  obtain ⟨C, _, hbound⟩ := dual_source_decoupling_bound P X Xc hX hcircle
    γ hγ hγ₂ M hM N hN α₁ α₂ α₃ q hq
  let s := fun z : ℂ => Real.exp (-h)*‖z‖
  let r := fun z : ℂ => ‖z‖^(1-ξ)
  let d := 3*γ^2/2*(q^2+q)
  have hn : Tendsto (fun z : ℂ => ‖z‖) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    simpa only [norm_zero] using (continuous_norm.tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds
  have hpow (v : ℝ) (hv : 0 < v) : Tendsto (fun z : ℂ => ‖z‖^v) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    simpa only [Function.comp_def, Real.zero_rpow hv.ne'] using
      ((Real.continuous_rpow_const hv.le).tendsto (0 : ℝ)).comp hn
  have hratio : Tendsto (fun z : ℂ => s z/r z) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    have ht := (hpow ξ hξ).const_mul (Real.exp (-h))
    simp only [mul_zero] at ht
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (dual_restart_radius_ratio z hz h ξ).symm
  have hdlim := hratio.const_mul d
  simp only [mul_zero] at hdlim
  let f := fun z : ℂ => (dualSeparatedInverseMoment P M γ α₁ α₂ α₃ q z (s z) (r z)).toReal-
    (dualCopiedSeparatedInverseMoment P Xc N γ α₁ α₂ α₃ q z (s z) (r z)).toReal
  refine (isComplexLittleOAtZero_ofReal_iff κ f).mp
    (isComplexLittleOAtZero_of_norm_le_power (C := C*Real.exp (-h)) hκ ?_)
  filter_upwards [self_mem_nhdsWithin, hn.eventually (gt_mem_nhds zero_lt_one),
    (hpow (1-ξ) (sub_pos.mpr hξ1)).eventually (gt_mem_nhds zero_lt_one),
    hratio.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2)),
    hdlim.eventually (gt_mem_nhds zero_lt_one)] with z hz hz1 hr1 hsep ht1
  have hnz := norm_pos_iff.mpr hz
  have hb := hbound z hz1.le (s z) (r z) (mul_pos (Real.exp_pos _) hnz)
    (Real.rpow_pos_of_pos hnz _) hr1.le hsep.le ht1.le
  rw [show s z/r z = Real.exp (-h)*‖z‖^ξ from dual_restart_radius_ratio z hz h ξ] at hb
  simpa only [Complex.norm_real, Real.norm_eq_abs, f, mul_assoc] using hb

end DOZZ.Proofs
