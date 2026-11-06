/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import DOZZ.GMC.Moments.WeightedDyadic
import DOZZ.GMC.Moments.WeightedLpFiniteSum
import DOZZ.Statements.GMC.WeightedGmcBallMoment
import DOZZ.GMC.SharpMoments.WeightedDyadicSum

/-! Subunit weighted moments used by all-root construction.

This construction specialization uses the dyadic shell argument of
`SharpMoments/WeightedDyadicSum`, restricted to `0 < p ≤ 1`. It uses the existing subadditivity
lemma and avoids the higher-order Minkowski passage. The coefficient proof explicitly folds
`ENNReal.rpow` before applying the power multiplication rule.
-/
section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace DOZZ.Proofs
/-- For `0 < p ≤ 1`, a series of nonnegative terms whose `p`th moments are dominated by a finite
geometric sequence has a finite `p`th moment. -/
private theorem rooted_subunit_shell_sum
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (f : ℕ → Ω → ℝ≥0∞) (hf : ∀ n, AEMeasurable (f n) P) {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    {K q : ℝ≥0∞} (hK : K ≠ ⊤) (hq : q < 1)
    (hbound : ∀ n, ∫⁻ ω, f n ω ^ p ∂P ≤ K * q ^ n) :
    ∫⁻ ω, (∑' n, f n ω) ^ p ∂P < ⊤ :=
  weightedDyadicSum_lintegral_tsum_rpow_lt_top_of_le_one f hf hp hp1 hK hq hbound

/-- The `p`th power of the dyadic coefficient is an explicit real power. -/
private theorem rooted_shell_coefficient_power (γ α p R : ℝ) (hR : 0 < R) (n : ℕ) :
    (ENNReal.rpow (ENNReal.ofReal (R / (2 : ℝ) ^ (n + 1))) (-γ * α)) ^ p =
      ENNReal.ofReal ((R / (2 : ℝ) ^ (n + 1)) ^ (-γ * α * p)) :=
  weightedDyadicSum_coeff_rpow γ α p R hR n

/-- The `p`th moment of the `n`th shell term is bounded by the sharp ball bound evaluated at the
dyadic radius, times the `p`th power of the coefficient. -/
private theorem rooted_shell_moment_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (M : Ω → Measure ℂ)
    (hM : ∀ s : Set ℂ, MeasurableSet s → AEMeasurable (fun ω => M ω s) P)
    (γ α p ξ C R : ℝ) (z : ℂ) (hp : 0 < p) (hR : 0 < R) (n : ℕ)
    (hball : ∀ ρ : ℝ, 0 < ρ → ρ ≤ R →
      gmcMassMoment P M (Metric.ball z ρ) p ≤ ENNReal.ofReal (C * ρ ^ ξ)) :
    ∫⁻ ω, (ENNReal.rpow (ENNReal.ofReal (R / (2 : ℝ) ^ (n + 1))) (-γ * α) *
        M ω (Metric.ball z (R / (2 : ℝ) ^ n))) ^ p ∂P ≤
      ENNReal.ofReal ((R / (2 : ℝ) ^ (n + 1)) ^ (-γ * α * p) *
        (C * (R / (2 : ℝ) ^ n) ^ ξ)) := DOZZ.Proofs.weightedDyadicSum_shell_moment_le P M hM γ α p ξ C R z hp hR n hball

/-- Real-variable identity: the dyadic coefficient times the sharp bound at the dyadic radius is a
constant times the `n`th power of `(1/2) ^ (ξ - γ α p)`. -/
private theorem rooted_shell_geometric_factor (γ α p ξ C R : ℝ) (hR : 0 < R) (n : ℕ) :
    (R / (2 : ℝ) ^ (n + 1)) ^ (-γ * α * p) * (C * (R / (2 : ℝ) ^ n) ^ ξ) =
      (C * (R / 2) ^ (-γ * α * p) * R ^ ξ) * ((1 / 2 : ℝ) ^ (ξ - γ * α * p)) ^ n :=
  weightedDyadicSum_real_term γ α p ξ C R hR n

/-- Sharp ball upper bounds with positive insertion exponent give a finite subunit weighted moment. -/
theorem rooted_local_moment_of_ball_upper
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M : Ω → Measure ℂ)
    (hM : ∀ s : Set ℂ, MeasurableSet s → AEMeasurable (fun ω => M ω s) P)
    (γ α p ξ C R : ℝ) (z : ℂ) (hγ : 0 < γ) (hα : 0 < α) (hp : 0 < p) (hR : 0 < R)
    (hp1 : p ≤ 1) (hR1 : R ≤ 1) (he : 0 < ξ - γ * α * p)
    (hball : ∀ ρ : ℝ, 0 < ρ → ρ ≤ R →
      gmcMassMoment P M (Metric.ball z ρ) p ≤ ENNReal.ofReal (C * ρ ^ ξ)) :
    weightedGmcBallMoment P M γ α z R p < ⊤ := by
  let qReal : ℝ := (1 / 2 : ℝ) ^ (ξ - γ * α * p)
  let shell : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    ENNReal.rpow (ENNReal.ofReal (R / (2 : ℝ) ^ (n + 1))) (-γ * α) *
      M ω (Metric.ball z (R / (2 : ℝ) ^ n))
  have hqNonneg : 0 ≤ qReal := Real.rpow_nonneg (by norm_num) _
  have hqLt : qReal < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) he
  have hshellMeas (n : ℕ) : AEMeasurable (shell n) P :=
    aemeasurable_const.mul (hM _ Metric.isOpen_ball.measurableSet)
  have hshellBound (n : ℕ) : ∫⁻ ω, shell n ω ^ p ∂P ≤
      ENNReal.ofReal (C * (R / 2) ^ (-γ * α * p) * R ^ ξ) * ENNReal.ofReal qReal ^ n := by
    refine (rooted_shell_moment_bound P M hM γ α p ξ C R z hp hR n hball).trans ?_
    rw [rooted_shell_geometric_factor γ α p ξ C R hR n, ENNReal.ofReal_mul' (pow_nonneg hqNonneg n),
      ENNReal.ofReal_pow hqNonneg]
  have hsum : ∫⁻ ω, (∑' n, shell n ω) ^ p ∂P < ⊤ :=
    rooted_subunit_shell_sum shell hshellMeas hp hp1 ENNReal.ofReal_ne_top
      (ENNReal.ofReal_lt_one.2 hqLt) hshellBound
  calc
    weightedGmcBallMoment P M γ α z R p
        ≤ ∫⁻ ω, (∑' n, shell n ω) ^ p ∂P :=
      lintegral_mono fun ω => ENNReal.rpow_le_rpow
        (weightedGmcBallMass_le_dyadic_charge_center (M ω) γ α R z hγ hα hR hR1) hp.le
    _ < ⊤ := hsum

end DOZZ.Proofs
