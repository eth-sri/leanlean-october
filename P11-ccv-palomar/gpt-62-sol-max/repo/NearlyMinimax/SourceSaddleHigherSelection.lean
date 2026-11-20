module

public import NearlyMinimax.HigherBandFamily
public import NearlyMinimax.LowerActivityHierarchy


@[expose] public section

/-! The physical higher-family omission and fine-count guards follow
from the actual rounded canonical saddle, before any signed action is tested. -/
noncomputable section
open Filter
open scoped Topology
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem sourceSaddleHigherFamily_eventually_legal (d : ℕ)
    (s a b shift : ℝ) (hs : 1 < s) (hd : 4*s < (d : ℝ)) (ha : 0 < a) (hab : a < b) :
    let tau := densityIntervalExponent a b
    let m := lowerSaddleCoefficient s (d : ℝ) tau
    let theta := lowerSaddleTheta s (d : ℝ) tau
    ∀ᶠ x in atTop,
      let M := lowerSaddleM m x
      let N := lowerSaddleN s (d : ℝ) m theta shift (shrunkDensityExponent a b) x
      let mu := lowerSaddleMu (d : ℝ) m theta shift x
      let ell := lowerAliasCutoff s (d : ℝ) m theta shift (tau+1) (shrunkDensityExponent a b) x
      1 ≤ ell ∧ (∀ r : ℕ, 0 < higherBandTargetScale d r N mu) ∧
        (∀ r : ℕ, ell < higherBandTargetScale d r N mu → r ≤ M) := by
  dsimp only
  let tau := densityIntervalExponent a b
  let m := lowerSaddleCoefficient s (d : ℝ) tau
  let theta := lowerSaddleTheta s (d : ℝ) tau
  have hτ := densityIntervalExponent_pos ha hab
  have hm := lowerSaddleCoefficient_pos hs hd hτ
  have htheta := lowerSaddleTheta_pos hs hd hτ
  obtain ⟨Cτ, _, hcontrol⟩ := exists_actual_lowerExponentControl ha hab
  have hN := lowerSaddleN_tendsto_atTop hs hd hm htheta hcontrol shift
  filter_upwards [actual_lowerAlias_guards hs hd ha hab shift,
    hN.eventually (eventually_ge_atTop (1 : ℝ)), eventually_gt_atTop (0 : ℝ)] with x hx hNx hxp
  have hmu : 0 < lowerSaddleMu (d : ℝ) m theta shift x := by
    rw [lowerSaddleMu_eq_exp hxp]
    positivity
  have hH : 0 < 1+Real.log (lowerSaddleN s (d : ℝ) m theta shift (shrunkDensityExponent a b) x) := by
    linarith [Real.log_nonneg hNx]
  refine ⟨hx.cutoff.le, ?_, ?_⟩
  · intro r
    apply mul_pos <;> positivity
  · intro r hr
    exact (hx.active_le r hr).trans hx.target_le_M

end NearlyMinimax
