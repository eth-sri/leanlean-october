/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Moments.WeightedDyadic
public import DOZZ.GMC.Moments.WeightedLpFiniteSum
public import DOZZ.Statements.GMC.WeightedGmcBallMoment

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




/-- Sharp ball upper bounds with positive insertion exponent give a finite subunit weighted moment. -/
theorem rooted_local_moment_of_ball_upper
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M : Ω → Measure ℂ)
    (hM : ∀ s : Set ℂ, MeasurableSet s → AEMeasurable (fun ω => M ω s) P)
    (γ α p ξ C R : ℝ) z (hγ : 0 < γ) (hα : 0 < α) (hp : 0 < p) (hR : 0 < R)
    (hp1 : p ≤ 1) (hR1 : R ≤ 1) (he : 0 < ξ - γ * α * p)
    (hball : ∀ ρ : ℝ, 0 < ρ → ρ ≤ R →
      gmcMassMoment P M (Metric.ball z ρ) p ≤ ENNReal.ofReal (C * ρ ^ ξ)) :
    weightedGmcBallMoment P M γ α z R p < ⊤ := by
  have rooted_shell_geometric_factor n : (R / (2 : ℝ) ^ (n + 1)) ^ (-γ * α * p) * (C * (R / (2 : ℝ) ^ n) ^ ξ) = (C * (R / 2) ^ (-γ * α * p) * R ^ ξ) * ((1 / 2 : ℝ) ^ (ξ - γ * α * p)) ^ n := by
    have hhalf : (1 / 2 : ℝ) ^ n = ((2 : ℝ) ^ n)⁻¹ := by
      rw [div_pow, one_pow, one_div]
    have hpos : 0 < (1 / 2 : ℝ) ^ n := by positivity
    have hmerge : ((1 / 2 : ℝ) ^ n) ^ (-γ * α * p) * ((1 / 2 : ℝ) ^ n) ^ ξ =
        ((1 / 2 : ℝ) ^ (ξ - γ * α * p)) ^ n := by
      rw [← Real.rpow_add hpos, Real.rpow_pow_comm (by norm_num)]
      congr 1
      ring
    rw [(show R / (2 : ℝ) ^ (n + 1) = (R / 2) * (1 / 2 : ℝ) ^ n by rw [pow_succ, hhalf]; field_simp), (show R / (2 : ℝ) ^ n = R * (1 / 2 : ℝ) ^ n by rw [hhalf, div_eq_mul_inv]), Real.mul_rpow (by positivity) hpos.le, Real.mul_rpow hR.le hpos.le]
    calc
      _ = C * (R / 2) ^ (-γ * α * p) * R ^ ξ *
            (((1 / 2 : ℝ) ^ n) ^ (-γ * α * p) * ((1 / 2 : ℝ) ^ n) ^ ξ) := by ring
      _ = _ := by rw [hmerge]
  have rooted_shell_moment_bound n (hball : ∀ ρ : ℝ, 0 < ρ → ρ ≤ R → gmcMassMoment P M (Metric.ball z ρ) p ≤ ENNReal.ofReal (C * ρ ^ ξ)) : ∫⁻ ω, (ENNReal.rpow (ENNReal.ofReal (R / (2 : ℝ) ^ (n + 1))) (-γ * α) * M ω (Metric.ball z (R / (2 : ℝ) ^ n))) ^ p ∂P ≤ ENNReal.ofReal ((R / (2 : ℝ) ^ (n + 1)) ^ (-γ * α * p) * (C * (R / (2 : ℝ) ^ n) ^ ξ)) := by
    calc
      _ = ∫⁻ ω, (ENNReal.rpow (ENNReal.ofReal (R / (2 : ℝ) ^ (n + 1))) (-γ * α)) ^ p *
            ENNReal.rpow (M ω (Metric.ball z (R / (2 : ℝ) ^ n))) p ∂P :=
        lintegral_congr fun ω => ENNReal.mul_rpow_of_nonneg _ _ hp.le
      _ = (ENNReal.rpow (ENNReal.ofReal (R / (2 : ℝ) ^ (n + 1))) (-γ * α)) ^ p *
            gmcMassMoment P M (Metric.ball z (R / (2 : ℝ) ^ n)) p :=
        lintegral_const_mul'' _ (ENNReal.continuous_rpow_const.measurable.comp_aemeasurable (hM _ Metric.isOpen_ball.measurableSet))
      _ ≤ ENNReal.ofReal ((R / (2 : ℝ) ^ (n + 1)) ^ (-γ * α * p)) *
            ENNReal.ofReal (C * (R / (2 : ℝ) ^ n) ^ ξ) := by
        rw [(show (ENNReal.rpow (ENNReal.ofReal (R / (2 : ℝ) ^ (n + 1))) (-γ * α)) ^ p = ENNReal.ofReal ((R / (2 : ℝ) ^ (n + 1)) ^ (-γ * α * p)) by change (ENNReal.ofReal (R / (2 : ℝ) ^ (n + 1)) ^ (-γ * α)) ^ p = _; rw [← ENNReal.rpow_mul, ENNReal.ofReal_rpow_of_pos (show 0 < R / (2 : ℝ) ^ (n + 1) by positivity)])]
        exact mul_le_mul' le_rfl (hball _ (by positivity) (div_le_self hR.le (one_le_pow₀ (by norm_num))))
      _ = _ := (ENNReal.ofReal_mul (Real.rpow_nonneg (show 0 < R / (2 : ℝ) ^ (n + 1) by positivity).le _)).symm
  have rooted_subunit_shell_sum {P : Measure Ω} (f : ℕ → Ω → ℝ≥0∞) (hf : ∀ n, AEMeasurable (f n) P) {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {K : ℝ≥0∞} {q : ℝ≥0∞} (hK : K ≠ ⊤) (hq : q < 1) (hbound : ∀ n, ∫⁻ ω, f n ω ^ p ∂P ≤ K * q ^ n) : ∫⁻ ω, (∑' n, f n ω) ^ p ∂P < ⊤ := by
    calc
      ∫⁻ ω, (∑' n, f n ω) ^ p ∂P ≤ ∫⁻ ω, ∑' n, f n ω ^ p ∂P :=
        lintegral_mono fun ω => ennreal_rpow_tsum_le_tsum_rpow _ hp hp1
      _ = ∑' n, ∫⁻ ω, f n ω ^ p ∂P := lintegral_tsum (fun n => ENNReal.continuous_rpow_const.measurable.comp_aemeasurable (hf n))
      _ ≤ ∑' n : ℕ, K * q ^ n := ENNReal.tsum_le_tsum hbound
      _ = K * (1 - q)⁻¹ := by rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
      _ < ⊤ := ENNReal.mul_lt_top hK.lt_top (ENNReal.inv_lt_top.2 (tsub_pos_of_lt hq))
  let qReal := (1 / 2 : ℝ) ^ (ξ - γ * α * p)
  let shell : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    ENNReal.rpow (ENNReal.ofReal (R / (2 : ℝ) ^ (n + 1))) (-γ * α) *
      M ω (Metric.ball z (R / (2 : ℝ) ^ n))
  have hqNonneg : 0 ≤ qReal := Real.rpow_nonneg (by norm_num) _
  have hshellBound (n : ℕ) : ∫⁻ ω, shell n ω ^ p ∂P ≤
      ENNReal.ofReal (C * (R / 2) ^ (-γ * α * p) * R ^ ξ) * ENNReal.ofReal qReal ^ n := by
    refine (rooted_shell_moment_bound n hball).trans ?_
    rw [rooted_shell_geometric_factor n, ENNReal.ofReal_mul' (pow_nonneg hqNonneg n),
      ENNReal.ofReal_pow hqNonneg]
  calc
    weightedGmcBallMoment P M γ α z R p
        ≤ ∫⁻ ω, (∑' n, shell n ω) ^ p ∂P :=
      lintegral_mono fun ω => ENNReal.rpow_le_rpow
        (weightedGmcBallMass_le_dyadic_charge_center (M ω) γ α R z hγ hα hR hR1) hp.le
    _ < ⊤ := (rooted_subunit_shell_sum shell (fun n => aemeasurable_const.mul (hM _ Metric.isOpen_ball.measurableSet)) hp hp1 ENNReal.ofReal_ne_top (ENNReal.ofReal_lt_one.2 (Real.rpow_lt_one (by norm_num) (by norm_num) he)) hshellBound)

end DOZZ.Proofs
