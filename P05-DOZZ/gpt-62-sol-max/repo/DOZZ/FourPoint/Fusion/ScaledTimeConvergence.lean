/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Fusion.ScaledFactor
public import DOZZ.FourPoint.Fusion.InterpolatedTimeConvergence
public import DOZZ.FourPoint.TaylorTimeIntegration

/-! # Dominated time integration of the scaled rooted spatial observable -/

@[expose] public section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The time weight in the Taylor integral has its exact elementary value. -/
theorem fusion_time_weight_integral (e : ℝ) (he : -1 < e) :
    IntegrableOn (fun t : ℝ => (1 - t) * t ^ e) (Icc 0 1) volume ∧
      (∫ t in Icc (0 : ℝ) 1, (1 - t) * t ^ e) = 1 / ((e + 1) * (e + 2)) := by
  obtain ⟨h1, hv1⟩ := time_rpow_integral e he
  obtain ⟨h2, hv2⟩ := time_rpow_integral (e + 1) (by linarith)
  have heq : (fun t : ℝ => t ^ e - t ^ (e + 1)) =ᵐ[volume.restrict (Icc 0 1)]
      (fun t => (1 - t) * t ^ e) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae (Measure.ae_ne volume (0 : ℝ))] with t ht ht0
    have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    rw [Real.rpow_add htpos, Real.rpow_one]
    ring
  refine ⟨(h1.sub h2).congr heq, ?_⟩
  rw [← integral_congr_ae heq, integral_sub h1 h2, hv1, hv2]
  field_simp [show e + 1 ≠ 0 by linarith, show e + 1 + 1 ≠ 0 by linarith,
    show e + 2 ≠ 0 by linarith]
  ring

/-- The spatial domination is uniform in time, leaving the integrable weight `t^e`. -/
theorem fusionScaledTimeIntegral_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ : ℝ) (hα : γ / 2 ≤ α₁) (hα₁ : α₁ < 2 / γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (s : ℝ) (hs : s < 0)
    (K : ℂ → ℂ) (hKm : Measurable K) (hK : Integrable K volume)
    (e : ℝ) (he : -1 < e) :
    Tendsto (fun z : ℂ => ∫ t in Icc (0 : ℝ) 1, ((1 - t) * t ^ e : ℝ) *
      (∫ y : ℂ, K y * (fusionScaledFactor P M γ α₁ α₂ α₃ s y ((t : ℂ) * z) : ℂ)))
      (nhds 0) (nhds ((1 / ((e + 1) * (e + 2)) : ℝ) *
        ((∫ y : ℂ, K y) *
          ((∫⁻ ω, fusionMovingMass γ α₁ α₂ α₃ 1 0 (M ω) ^ s ∂P).toReal : ℂ)))) := by
  obtain ⟨hi, heq⟩ := fusion_time_weight_integral e he
  have h := fusionSpaceTimeIntegral_tendsto P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hα hα₁ hα₂ hα₃ s hs K hKm hK
    (fun _ => 1) measurable_const (fun _ _ => by simp) (fun t z => (t : ℂ) * z)
    (fun z => Complex.measurable_ofReal.mul_const z)
    (fun t ht z hz => by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]
      exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans hz)
    (fun t _ => by simpa using (show Continuous (fun z : ℂ => (t : ℂ) * z) from by fun_prop).tendsto 0) _ hi
  simpa only [fusionInterpolatedFactor_one, heq] using h

end DOZZ.Proofs
