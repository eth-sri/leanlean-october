/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Moments.WeightedDyadic
import Mathlib.MeasureTheory.Measure.GiryMonad
import DOZZ.GMC.Moments.WeightedCutoffPositiveSubunit

/-! Weighted local moment finiteness on the subunit range inside the exact logarithmic chart. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

/-! The rest of this module uses the a.e. measurable version supplied by the GMC predicate
`DOZZ.IsGMCOf`, so weighted moment integrals can be split without changing the chosen version. -/

theorem weightedGmcBallMass_le_inner_add_total
    (μ : Measure ℂ) (γ α : ℝ) (z : ℂ) (r ρ : ℝ)
    (hγα : 0 < γ * α) (hρ : 0 < ρ) :
    weightedGmcBallMass γ μ α z r ≤ weightedGmcBallMass γ μ α z ρ +
      ENNReal.ofReal (ρ ^ (-γ * α)) * μ (Metric.ball z r) := by
  let B := Metric.ball z r
  let D := Metric.ball z ρ
  let density : ℂ → ℝ≥0∞ := fun x =>
    ENNReal.rpow (ENNReal.ofReal ‖x - z‖) (-γ * α)
  let inner := D.indicator density
  let outer := B.indicator (fun _ => ENNReal.ofReal (ρ ^ (-γ * α)))
  have hq : -γ * α < 0 := by linarith
  have hdensity : Measurable density := by
    measurability
  have hinner : Measurable inner := hdensity.indicator Metric.isOpen_ball.measurableSet
  have houter : Measurable outer := measurable_const.indicator Metric.isOpen_ball.measurableSet
  have hpoint (x : ℂ) : B.indicator density x ≤ inner x + outer x := by
    by_cases hx : x ∈ B
    · by_cases hxρ : x ∈ D
      · aesop
      · have hdist : ρ ≤ ‖x - z‖ := by
          have hxρ' : ¬ ‖x - z‖ < ρ := by
            simpa [D, Metric.mem_ball, dist_eq_norm] using hxρ
          linarith
        have hpow :=
          Real.rpow_le_rpow_of_nonpos hρ hdist hq.le
        have hweight : density x ≤ ENNReal.ofReal (ρ ^ (-γ * α)) := by
          change ENNReal.rpow _ (-γ * α) ≤ _
          rw [DOZZ.Proofs.ennreal_ofReal_rpow_of_pos_cutoff (lt_of_lt_of_le hρ hdist)]
          bound
        aesop
    simp_all
  calc
    weightedGmcBallMass γ μ α z r = ∫⁻ x, B.indicator density x ∂μ := by
      rw [weightedGmcBallMass, ← lintegral_indicator Metric.isOpen_ball.measurableSet]
    _ ≤ ∫⁻ x, inner x + outer x ∂μ := lintegral_mono hpoint
    _ = ∫⁻ x, inner x ∂μ + ∫⁻ x, outer x ∂μ := lintegral_add_left hinner _
    _ = weightedGmcBallMass γ μ α z ρ +
          ENNReal.ofReal (ρ ^ (-γ * α)) * μ (Metric.ball z r) := by
      have hinnerInt : ∫⁻ x, inner x ∂μ = weightedGmcBallMass γ μ α z ρ := by
        dsimp [inner, D]
        rw [weightedGmcBallMass, ← lintegral_indicator Metric.isOpen_ball.measurableSet]
      have houterInt : ∫⁻ x, outer x ∂μ =
          ENNReal.ofReal (ρ ^ (-γ * α)) * μ (Metric.ball z r) := by
        dsimp [outer, B]
        rw [lintegral_indicator_const Metric.isOpen_ball.measurableSet]
      rw [hinnerInt, houterInt]

end DOZZ.Proofs
