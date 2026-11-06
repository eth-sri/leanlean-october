/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Moments.WeightedCutoffPositiveSubunit

/-! Expected cutoff scaling for every insertion charge at subunit positive orders. -/

@[expose] public section

open MeasureTheory
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

theorem cutoffWeightedGmcBallMoment_nonpos_subunit_scale_formula
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (γ α : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α ≤ 0)
    (z : ℂ) (R δ p : ℝ) (hR : 0 < R) (hR1 : R ≤ 1 / 2)
    (hδ : 0 < δ) (hδR : δ ≤ R) (hchart : ‖z‖ + 2 * R ≤ 1)
    (hp : 0 < p) (hp1 : p ≤ 1) :
    (∫⁻ ω, ENNReal.rpow
      (cutoffWeightedGmcBallMass P Xc γ α z R δ ω) p ∂P) ≤
        ENNReal.ofReal (2 ^ weightedCutoffMomentScaleExponent γ α p) *
          (1 + gmcReferenceMeasure (Metric.ball 0 (1 / 2))) *
          ENNReal.ofReal (R ^ weightedCutoffMomentScaleExponent γ α p) := by
  let ξ : ℝ := 2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2
  let η := weightedCutoffMomentScaleExponent γ α p
  let base : ℝ≥0∞ := 1 + gmcReferenceMeasure (Metric.ball 0 (1 / 2))
  let s : ℝ := 2 * R
  have hs : 0 < s := by positivity
  have hη : -γ * α * p + ξ = η := by
    dsimp [η, ξ, weightedCutoffMomentScaleExponent, Q]
    grind
  have hsub := cutoffWeightedGmcBallMoment_le_nonpos_subunit_chart
    P X hX γ hγ hγ2 Xc hXc α hα z R δ p hR hR1 hδ hδR hchart hp hp1
  have hcoef : ENNReal.rpow (ENNReal.ofReal (s ^ (-γ * α))) p =
      ENNReal.ofReal (s ^ (-γ * α * p)) := by
    calc
      _ = ENNReal.rpow (ENNReal.rpow (ENNReal.ofReal s) (-γ * α)) p := by
        rw [← DOZZ.Proofs.ennreal_ofReal_rpow_of_pos_cutoff hs]
      _ = ENNReal.rpow (ENNReal.ofReal s) _ :=
        (ENNReal.rpow_mul ..).symm
      _ = _ := DOZZ.Proofs.ennreal_ofReal_rpow_of_pos_cutoff hs
  have hpowProd : s ^ (-γ * α * p) * s ^ ξ = s ^ η := by
    rw [← Real.rpow_add hs]
    congr 1
  calc
    _ ≤ ENNReal.rpow (ENNReal.ofReal (s ^ (-γ * α))) p *
        (ENNReal.ofReal (s ^ ξ) * base) := by
      simpa [s, ξ, base] using hsub
    _ = ENNReal.ofReal (s ^ η) * base := by
      rw [hcoef]
      calc
        _ = (ENNReal.ofReal (s ^ (-γ * α * p)) * ENNReal.ofReal (s ^ ξ)) * base := by
          ac_rfl
        _ = ENNReal.ofReal (s ^ (-γ * α * p) * s ^ ξ) * base := by
          rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (le_of_lt hs) (-γ * α * p))]
        _ = _ := by simp_all
    _ = ENNReal.ofReal (2 ^ η) * base * ENNReal.ofReal (R ^ η) := by
      have h2R : s ^ η = 2 ^ η * R ^ η := by
        dsimp [s]
        rw [Real.mul_rpow (by norm_num) hR.le]
      rw [h2R]
      calc
        _ = (ENNReal.ofReal (2 ^ η) * ENNReal.ofReal (R ^ η)) * base := by
          rw [← ENNReal.ofReal_mul
            (Real.rpow_nonneg (by norm_num) η)]
        _ = _ := by ac_rfl
    _ = _ := by rfl

end DOZZ.Proofs
