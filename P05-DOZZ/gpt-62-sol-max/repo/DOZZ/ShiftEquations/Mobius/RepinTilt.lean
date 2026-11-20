/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Mobius.RepinPotential
public import DOZZ.GMC.CircleAverageLimits
import DOZZ.GMC.Construction.GMCGeneralTiltLimit

/-! The Cameron–Martin identity for a multiple of the repinning circle average. -/

@[expose] public section
open MeasureTheory Filter Topology
open scoped ENNReal

namespace DOZZ.Proofs

section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
include hX

/-- The variance of the repinning variable is the self-energy of its circle. -/
theorem gaussianVariance_repinCircle (Xc : Ω → ℂ → ℝ → ℝ)
    (hXc : IsCircleAverage P X Xc) (a b : ℂ) (ha : a ≠ 0) :
    gaussianVariance P (fun ω => Xc ω b (-Real.log ‖a‖)) = 2 * repinKappa a b := by
  rw [gaussianVariance, isCircleAverage_covariance P X hX Xc hXc, repin_selfEnergy a b ha]

/-- Tilt any measurable chaos functional by a scalar multiple of the repinning variable. -/
theorem lintegral_repin_circle_tilt (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (Xc : Ω → ℂ → ℝ → ℝ)
    (hXc : IsCircleAverage P X Xc) (a b : ℂ) (ha : a ≠ 0) (t : ℝ)
    (H : Measure ℂ → ℝ≥0∞) (hH : Measurable H) :
    let L := fun ω => Xc ω b (-Real.log ‖a‖)
    (∫⁻ ω, ENNReal.ofReal (Real.exp (t * L ω - t ^ 2 * gaussianVariance P L / 2)) * H (M ω) ∂P) =
      ∫⁻ ω, H ((M ω).withDensity (fun x => ENNReal.ofReal (Real.exp (γ * (t * repinPotential a b x))))) ∂P := by
  dsimp only
  let r₀ := -Real.log ‖a‖
  let L := fun ω => t * Xc ω b r₀
  have hL := IsGaussianL2Limit.const_mul (isCircleAverage_isGaussianL2Limit P X hX Xc hXc b r₀) t
  obtain ⟨B, hB⟩ := exists_abs_repinPotential_le a b ha
  let c := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => t * repinPotential a b x) (continuous_const.mul (continuous_repinPotential a b ha))
    (|t| * B) (fun x => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (hB x) (abs_nonneg _))
  have hcov (r : ℝ) (x : ℂ) : gaussianCovariance P (fun ω => Xc ω x r) L =
      t * (∫ u, repinPotential a b u ∂circleMeasure x r) := by
    rw [show L = (fun ω => t * Xc ω b r₀) by rfl, gaussianCovariance_const_mul_right,
      isCircleAverage_covariance P X hX Xc hXc]
    rfl
  simpa only [L, r₀, gaussianVariance_const_mul, show ∀ x, c x = t * repinPotential a b x from fun _ => rfl] using
    equatorGFF_GMC_tilt P X hX γ hγ hγ2 M hM Xc hXc L hL c (by
    simp_rw [hcov]
    exact Real.uniformContinuous_const_mul.comp_tendstoUniformly (tendstoUniformly_repinPotential a b ha))
      (fun _ μ => H μ) (hH.comp measurable_snd)

end

end DOZZ.Proofs
