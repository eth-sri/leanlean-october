/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Moments.WeightedDyadic
public import DOZZ.GMC.Moments.WeightedLpFiniteSum
public import DOZZ.Statements.GMC.WeightedGmcBallMoment
import DOZZ.GMC.SharpMoments.WeightedDyadicSum

/-! Subunit weighted moments used by all-root construction.

This construction specialization uses the dyadic shell argument of
`SharpMoments/WeightedDyadicSum`, restricted to `0 < p ≤ 1`. It uses the existing subadditivity
lemma and avoids the higher-order Minkowski passage. The coefficient proof explicitly folds
`ENNReal.rpow` before applying the power multiplication rule.
-/
@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace DOZZ.Proofs
theorem rooted_local_moment_of_ball_upper
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M : Ω → Measure ℂ)
    (hM : ∀ s : Set ℂ, MeasurableSet s → AEMeasurable (fun ω => M ω s) P)
    (γ α p ξ C R : ℝ) (z : ℂ) (hγ : 0 < γ) (hα : 0 < α) (hp : 0 < p) (hR : 0 < R)
    (hp1 : p ≤ 1) (hR1 : R ≤ 1) (he : 0 < ξ - γ * α * p)
    (hball : ∀ ρ : ℝ, 0 < ρ → ρ ≤ R →
      gmcMassMoment P M (Metric.ball z ρ) p ≤ ENNReal.ofReal (C * ρ ^ ξ)) :
    weightedGmcBallMoment P M γ α z R p < ⊤ := by
  let qReal : ℝ := (1 / 2) ^ (ξ - γ * α * p)
  let shell : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    ENNReal.rpow (ENNReal.ofReal (R / 2 ^ (n + 1))) (-γ * α) *
      M ω (Metric.ball z (R / 2 ^ n))
  have hqNonneg : 0 ≤ qReal := by positivity
  have hqLt : qReal < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) he
  have hshellMeas (n : ℕ) : AEMeasurable (shell n) P :=
    by measurability
  have hshellBound (n : ℕ) : ∫⁻ ω, shell n ω ^ p ∂P ≤
      ENNReal.ofReal (C * (R / 2) ^ (-γ * α * p) * R ^ ξ) * ENNReal.ofReal qReal ^ n := by
    refine (DOZZ.Proofs.weightedDyadicSum_shell_moment_le P M hM γ α p ξ C R z hp hR n hball).trans ?_
    rw [DOZZ.Proofs.weightedDyadicSum_real_term γ α p ξ C R hR n, ENNReal.ofReal_mul' (pow_nonneg hqNonneg n),
      ENNReal.ofReal_pow hqNonneg]
  have hsum :=
    DOZZ.Proofs.weightedDyadicSum_lintegral_tsum_rpow_lt_top_of_le_one shell hshellMeas hp hp1 ENNReal.ofReal_ne_top
      (ENNReal.ofReal_lt_one.2 hqLt) hshellBound
  calc
    weightedGmcBallMoment P M γ α z R p
        ≤ ∫⁻ ω, (∑' n, shell n ω) ^ p ∂P :=
      lintegral_mono fun ω => ENNReal.rpow_le_rpow
        (weightedGmcBallMass_le_dyadic_charge_center (M ω) γ α R z hγ hα hR hR1) hp.le
    _ < ⊤ := hsum

end DOZZ.Proofs
