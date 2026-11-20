/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Fusion.ScaledLocalRooting
public import DOZZ.FourPoint.Fusion.ScaledTimeConvergence
public import DOZZ.FourPoint.Fusion.Parameters

/-! # Rescaling the local second variation through the time integral -/

@[expose] public section
open MeasureTheory Set Filter Topology
namespace DOZZ.Proofs

noncomputable abbrev fusionSecondCoeff (mixed : Bool) (γ p : ℝ) : ℝ :=
  if mixed then -2 * p * (γ ^ 2 / 4) ^ 2 else -p * (γ ^ 2 / 4) * (γ ^ 2 / 4 - 1)

noncomputable def fusionLocalSecond {Ω : Type*} [MeasurableSpace Ω] (mixed : Bool)
    (P : Measure Ω) (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ p : ℝ) (z : ℂ) : ℂ :=
  (fusionSecondCoeff mixed γ p : ℂ) * fusionSecondDenom mixed z *
    (∫ t in Icc (0 : ℝ) 1, (1 - t : ℝ) *
      fusionSecondSpatial mixed P M γ α₁ α₂ α₃ p (Metric.ball 0 (1 / 2)) ((t : ℂ) * z))

noncomputable abbrev fusionLocalR1 {Ω : Type*} [MeasurableSpace Ω] := fusionLocalSecond (Ω := Ω) false
noncomputable abbrev fusionLocalR2 {Ω : Type*} [MeasurableSpace Ω] := fusionLocalSecond (Ω := Ω) true

private theorem fusion_second_time_scaling (mixed : Bool) (κ t : ℝ) (ht : 0 < t)
    (z : ℂ) (hz : z ≠ 0) :
    fusionSecondDenom mixed z * (‖(t : ℂ) * z‖ ^ κ : ℝ) / fusionSecondDenom mixed ((t : ℂ) * z) =
      (‖z‖ ^ κ : ℝ) * (t ^ (κ - 2) : ℝ) := by
  have hn : ‖(t : ℂ) * z‖ = t * ‖z‖ := by simp [norm_mul, Real.norm_of_nonneg ht.le]
  have hd : fusionSecondDenom mixed ((t : ℂ) * z) = (t ^ 2 : ℝ) * fusionSecondDenom mixed z := by
    cases mixed <;> simp [fusionSecondDenom, hn, mul_pow]
  have hd₀ : fusionSecondDenom mixed z ≠ 0 := by
    rw [← norm_pos_iff, norm_fusionSecondDenom]
    exact pow_pos (norm_pos_iff.mpr hz) _
  have hp : t ^ κ = t ^ (κ - 2) * t ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add ht]
    congr 1
    ring
  rw [hn, Real.mul_rpow ht.le (norm_nonneg _), hp, hd]
  push_cast
  field_simp [hd₀, Complex.ofReal_ne_zero.mpr ht.ne']

/-- The spatial phase cancels against the Taylor prefactor, leaving the same time weight
for both second derivatives. -/
theorem fusionLocalSecond_scaled {Ω : Type*} [MeasurableSpace Ω] (mixed : Bool)
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ : ℝ) (hβ : γ ^ 2 / 2 < γ * α₁) (hα₁ : α₁ < 2 / γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (p : ℝ) (hp : 0 ≤ p)
    (z : ℂ) (hz : z ≠ 0) (hz4 : ‖z‖ ≤ 1 / 4) :
    fusionLocalSecond mixed P M γ α₁ α₂ α₃ p z =
      (fusionSecondCoeff mixed γ p : ℂ) * (‖z‖ ^ (γ * (Q γ - α₁)) : ℝ) *
        (∫ t in Icc (0 : ℝ) 1, ((1 - t) * t ^ (γ ^ 2 / 2 - γ * α₁) : ℝ) *
          (∫ y : ℂ, fusionPlanarSecond mixed (γ ^ 2 / 2) (γ * α₁) 1 y *
            (fusionScaledFactor P M γ α₁ α₂ α₃ (-p - 1) y ((t : ℂ) * z) : ℂ))) := by
  unfold fusionLocalSecond
  simp only [mul_assoc]
  apply congrArg ((fusionSecondCoeff mixed γ p : ℂ) * ·)
  rw [← integral_const_mul, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    ae_restrict_of_ae (Measure.ae_ne volume (0 : ℝ))] with t ht ht₀
  have htz := mul_ne_zero (Complex.ofReal_ne_zero.mpr ht₀) hz
  have htz4 : ‖(t : ℂ) * z‖ ≤ 1 / 4 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans hz4
  rw [fusion_local_second_spatial_scaled mixed P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hβ hα₁ hα₂ hα₃ p hp _ htz htz4]
  have hf := fusion_second_time_scaling mixed (γ * (Q γ - α₁)) t (lt_of_le_of_ne ht.1 ht₀.symm) z hz
  have he : γ * (Q γ - α₁) - 2 = γ ^ 2 / 2 - γ * α₁ := by
    rw [fusion_exponent_eq γ α₁ hγ.ne']; ring
  rw [he] at hf
  push_cast
  linear_combination (1 - (t : ℂ)) * (∫ y : ℂ, fusionPlanarSecond mixed (γ ^ 2 / 2) (γ * α₁) 1 y *
    (fusionScaledFactor P M γ α₁ α₂ α₃ (-p - 1) y ((t : ℂ) * z) : ℂ)) * hf

end DOZZ.Proofs
