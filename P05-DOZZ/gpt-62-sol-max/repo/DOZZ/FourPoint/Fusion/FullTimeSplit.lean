/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Fusion.SpatialFunctions
public import DOZZ.FourPoint.Fusion.SpatialSplit
public import DOZZ.FourPoint.Fusion.LocalSpatialBound
public import DOZZ.FourPoint.Fusion.TimeIntegrability
public import DOZZ.FourPoint.Fusion.LocalSecondScaling
public import DOZZ.Statements.FourPoint.GammaHalfRootedR2
/-! # Splitting the literal full Taylor contributions -/
@[expose] public section
open MeasureTheory Set Filter
namespace DOZZ.Proofs
/-- The weighted time integrand is integrable, and the split into local and exterior contributions
can be taken inside its integral. -/
theorem fusion_second_time {Ω : Type*} [MeasurableSpace Ω] (mixed : Bool)
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ : ℝ) (hlo : γ / 2 < α₁) (hsq : 2 < γ ^ 2) (hα₁ : α₁ < 2 / γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (p : ℝ) (hp : 0 ≤ p)
    (z : ℂ) (hz : z ≠ 0) (hz4 : ‖z‖ ≤ 1 / 4) :
    let S := fusionSecondSpatial mixed P M γ α₁ α₂ α₃ p
    let B := Metric.ball (0 : ℂ) (1 / 2)
    let T := fun D (t : ℝ) => (1 - t : ℝ) * S D ((t : ℂ) * z)
    IntegrableOn (T univ) (Icc 0 1) volume ∧
      (∫ t in Icc (0 : ℝ) 1, T univ t) = (∫ t in Icc (0 : ℝ) 1, T B t) + (∫ t in Icc (0 : ℝ) 1, T Bᶜ t) := by
  intro S B T
  obtain ⟨CL, _, hbL⟩ := fusion_local_second_expectation_bound mixed P X hX γ hγ hγ2 M hM
    α₁ α₂ α₃ hlo hα₁ hα₂ hα₃ p hp
  obtain ⟨CE, _, hbE⟩ := fusion_exterior_expectation_bound mixed P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hα₁ hα₂ hα₃ p hp
  obtain ⟨_, hβ, _, hβe, _, _⟩ := fusion_taylor_parameters γ α₁ hγ hlo hsq hα₁
  have hm D hD := fusionSecondSpatial_measurable mixed P X hX γ hγ hγ2 M hM α₁ α₂ α₃ p D hD
  have hL := fusion_time_integrable_of_power_bound (S B) (hm B Metric.isOpen_ball.measurableSet) CL
    (γ ^ 2 / 2 - γ * α₁) (1 / 4) (by linarith only [hβe]) hbL z hz hz4
  have hE := fusion_time_integrable_of_power_bound (S Bᶜ) (hm Bᶜ Metric.isOpen_ball.measurableSet.compl) CE
    0 (1 / 4) (by norm_num) (fun w hw hw4 => by
      simpa only [Real.rpow_zero, mul_one, S, B] using (hbE w hw hw4).2) z hz hz4
  have hsplit : ∀ᵐ t : ℝ ∂volume.restrict (Icc 0 1), S univ ((t : ℂ) * z) = S B ((t : ℂ) * z) + S Bᶜ ((t : ℂ) * z) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae (Measure.ae_ne volume (0 : ℝ))] with t ht ht0
    have htz := mul_ne_zero (Complex.ofReal_ne_zero.mpr ht0) hz
    exact fusion_secondSpatial_expectation_split mixed P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hβ hα₁ hα₂ hα₃ p hp _ htz (by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]
      exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans hz4)
  refine ⟨(hL.add hE).congr (hsplit.mono ?_), fusion_time_split (S univ) (S B) (S Bᶜ) z hL hE hsplit⟩
  intro t ht
  show _ * S B _ + _ * S Bᶜ _ = _ * S univ _
  rw [ht, mul_add]

section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
  (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (α₁ α₂ α₃ : ℝ)
  (hlo : γ / 2 < α₁) (hsq : 2 < γ ^ 2) (hα₁ : α₁ < 2 / γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (p : ℝ)
  (hp : 0 ≤ p) (z : ℂ) (hz : z ≠ 0) (hz4 : ‖z‖ ≤ 1 / 4)
include Ω X hX hγ hγ2 hM hlo hsq hα₁ hα₂ hα₃ hp hz hz4

/-- The full `r₁` term splits into the local term `fusionLocalR1` and a bounded exterior time
integral. -/
theorem fusionRootedR1_split :
    gammaHalfRootedR1 P M γ α₁ α₂ α₃ p z = fusionLocalR1 P M γ α₁ α₂ α₃ p z +
      ((-p * (γ ^ 2 / 4) * (γ ^ 2 / 4 - 1) : ℝ) : ℂ) * z ^ 2 *
        (∫ t in Icc (0 : ℝ) 1, (1 - t : ℝ) *
          fusionPureSpatial P M γ α₁ α₂ α₃ p (Metric.ball (0 : ℂ) (1 / 2))ᶜ ((t : ℂ) * z)) := by
  have h := congrArg (fun q => (((-p * (γ ^ 2 / 4) * (γ ^ 2 / 4 - 1) : ℝ) : ℂ) * z ^ 2) * q)
    (fusion_second_time false P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hlo hsq hα₁ hα₂ hα₃ p hp z hz hz4).2
  dsimp only at h
  rw [mul_add] at h
  simpa only [gammaHalfRootedR1, fusionLocalR1, fusionLocalSecond, fusionSecondCoeff, fusionPureSpatial, fusionMixedSpatial, fusionSecondSpatial,
    fusionSecondKernel, fusionSecondDenom, Bool.false_eq_true, ite_false, ite_true, Measure.restrict_univ,
    ENNReal.rpow_eq_pow, Complex.ofReal_pow] using h

/-- The full `r₂` term splits into the local term `fusionLocalR2` and a bounded exterior time
integral. -/
theorem fusionRootedR2_split :
    gammaHalfRootedR2 P M γ α₁ α₂ α₃ p z = fusionLocalR2 P M γ α₁ α₂ α₃ p z +
      ((-2 * p * (γ ^ 2 / 4) ^ 2 : ℝ) : ℂ) * z * star z *
        (∫ t in Icc (0 : ℝ) 1, (1 - t : ℝ) *
          fusionMixedSpatial P M γ α₁ α₂ α₃ p (Metric.ball (0 : ℂ) (1 / 2))ᶜ ((t : ℂ) * z)) := by
  have h := congrArg (fun q => (((-2 * p * (γ ^ 2 / 4) ^ 2 : ℝ) : ℂ) * z * star z) * q)
    (fusion_second_time true P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hlo hsq hα₁ hα₂ hα₃ p hp z hz hz4).2
  dsimp only at h
  rw [mul_add] at h
  have hpref : ((-2 * p * (γ ^ 2 / 4) ^ 2 : ℝ) : ℂ) * z * star z =
      ((-2 * p * (γ ^ 2 / 4) ^ 2 : ℝ) : ℂ) * (‖z‖ ^ 2 : ℝ) := by
    rw [mul_assoc]
    apply congrArg (_ * ·)
    simpa only [Complex.ofReal_pow, starRingEnd_apply] using Complex.mul_conj' z
  simpa only [gammaHalfRootedR2, fusionLocalR2, fusionLocalSecond, fusionSecondCoeff, fusionPureSpatial, fusionMixedSpatial, fusionSecondSpatial,
    fusionSecondKernel, fusionSecondDenom, Bool.false_eq_true, ite_false, ite_true, Measure.restrict_univ,
    ENNReal.rpow_eq_pow, hpref, Complex.ofReal_pow] using h

end

end DOZZ.Proofs
