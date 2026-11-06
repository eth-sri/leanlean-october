/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Moments.WeightedDyadic
public import DOZZ.GMC.Moments.WeightedLpFiniteSum
public import DOZZ.Statements.GMC.WeightedGmcBallMoment

/-! # Weighted moments from sharp ball bounds at the center

Sharp ball upper bounds `E M(B(z,ρ))^p ≤ C ρ^ξ` at a center `z`, with `ξ - γ α p > 0`, make the
weighted local moment at `z` finite. The proof sums the dyadic shell estimate for the singular
weight: each shell has `p`th moment bounded by a geometric sequence, and the series is controlled
by subadditivity of `x ↦ x ^ p` for `p ≤ 1` and by Minkowski's inequality for `p > 1`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-! ### Summation of terms with geometrically decaying moments -/


/-- The `r`th power of a natural power commutes with taking the natural power of the `r`th
power. -/
theorem weightedDyadicSum_pow_rpow_comm (q : ℝ≥0∞) (r : ℝ) (n : ℕ) :
    (q ^ n) ^ r = (q ^ r) ^ n := by
  calc
    (q ^ n) ^ r = (q ^ (n : ℝ)) ^ r := by rw [ENNReal.rpow_natCast]
    _ = q ^ ((n : ℝ) * r) := (ENNReal.rpow_mul _ _ _).symm
    _ = q ^ (r * (n : ℝ)) := by rw [mul_comm]
    _ = (q ^ r) ^ (n : ℝ) := ENNReal.rpow_mul _ _ _
    _ = (q ^ r) ^ n := ENNReal.rpow_natCast _ _



/-! ### The dyadic shell terms -/




/-! ### Main theorem -/

/-- Sharp ball upper bounds `E M(B(z,ρ))^p ≤ C ρ^ξ` at a center with positive insertion exponent
`ξ - γ α p > 0` make the weighted moment at that center finite. -/
theorem weightedGmcBallMoment_lt_top_of_ball_upper
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M : Ω → Measure ℂ)
    (hM : ∀ s : Set ℂ, MeasurableSet s → AEMeasurable (fun ω => M ω s) P)
    (γ α p ξ C R : ℝ) z (hγ : 0 < γ) (hα : 0 < α) (hp : 0 < p) (hR : 0 < R)
    (hR1 : R ≤ 1) (he : 0 < ξ - γ * α * p)
    (hball : ∀ ρ : ℝ, 0 < ρ → ρ ≤ R →
      gmcMassMoment P M (Metric.ball z ρ) p ≤ ENNReal.ofReal (C * ρ ^ ξ)) :
    weightedGmcBallMoment P M γ α z R p < ⊤ := by
  have weightedDyadicSum_real_term n : (R / (2 : ℝ) ^ (n + 1)) ^ (-γ * α * p) * (C * (R / (2 : ℝ) ^ n) ^ ξ) = (C * (R / 2) ^ (-γ * α * p) * R ^ ξ) * ((1 / 2 : ℝ) ^ (ξ - γ * α * p)) ^ n := by
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
  have weightedDyadicSum_shell_moment_le n (hball : ∀ ρ : ℝ, 0 < ρ → ρ ≤ R → gmcMassMoment P M (Metric.ball z ρ) p ≤ ENNReal.ofReal (C * ρ ^ ξ)) : ∫⁻ ω, (ENNReal.rpow (ENNReal.ofReal (R / (2 : ℝ) ^ (n + 1))) (-γ * α) * M ω (Metric.ball z (R / (2 : ℝ) ^ n))) ^ p ∂P ≤ ENNReal.ofReal ((R / (2 : ℝ) ^ (n + 1)) ^ (-γ * α * p) * (C * (R / (2 : ℝ) ^ n) ^ ξ)) := by
    have weightedDyadicSum_coeff_rpow : (ENNReal.rpow (ENNReal.ofReal (R / (2 : ℝ) ^ (n + 1))) (-γ * α)) ^ p = ENNReal.ofReal ((R / (2 : ℝ) ^ (n + 1)) ^ (-γ * α * p)) := by
      rw [ENNReal.rpow_eq_pow, ← ENNReal.rpow_mul, ENNReal.ofReal_rpow_of_pos (show 0 < R / (2 : ℝ) ^ (n + 1) by positivity)]
    calc
      _ = ∫⁻ ω, (ENNReal.rpow (ENNReal.ofReal (R / (2 : ℝ) ^ (n + 1))) (-γ * α)) ^ p *
            ENNReal.rpow (M ω (Metric.ball z (R / (2 : ℝ) ^ n))) p ∂P :=
        lintegral_congr fun ω => ENNReal.mul_rpow_of_nonneg _ _ hp.le
      _ = (ENNReal.rpow (ENNReal.ofReal (R / (2 : ℝ) ^ (n + 1))) (-γ * α)) ^ p *
            gmcMassMoment P M (Metric.ball z (R / (2 : ℝ) ^ n)) p :=
        lintegral_const_mul'' _ (ENNReal.continuous_rpow_const.measurable.comp_aemeasurable (hM _ Metric.isOpen_ball.measurableSet))
      _ ≤ ENNReal.ofReal ((R / (2 : ℝ) ^ (n + 1)) ^ (-γ * α * p)) *
            ENNReal.ofReal (C * (R / (2 : ℝ) ^ n) ^ ξ) := by
        rw [weightedDyadicSum_coeff_rpow]
        exact mul_le_mul' le_rfl (hball _ (by positivity) (div_le_self hR.le (one_le_pow₀ (by norm_num))))
      _ = _ := (ENNReal.ofReal_mul (Real.rpow_nonneg (show 0 < R / (2 : ℝ) ^ (n + 1) by positivity).le _)).symm
  have weightedDyadicSum_lintegral_tsum_rpow_lt_top {P : Measure Ω} (f : ℕ → Ω → ℝ≥0∞) (hf : ∀ n, AEMeasurable (f n) P) {p : ℝ} (hp : 0 < p) {K : ℝ≥0∞} {q : ℝ≥0∞} (hK : K ≠ ⊤) (hq : q < 1) (hbound : ∀ n, ∫⁻ ω, f n ω ^ p ∂P ≤ K * q ^ n) : ∫⁻ ω, (∑' n, f n ω) ^ p ∂P < ⊤ := by
    have weightedDyadicSum_lintegral_tsum_rpow_lt_top_of_one_lt {p : ℝ} (hp : 1 < p) {K : ℝ≥0∞} {q : ℝ≥0∞} (hK : K ≠ ⊤) (hq : q < 1) (hbound : ∀ n, ∫⁻ ω, f n ω ^ p ∂P ≤ K * q ^ n) : ∫⁻ ω, (∑' n, f n ω) ^ p ∂P < ⊤ := by
      have hp0 := zero_lt_one.trans hp
      have hinv := one_div_pos.2 hp0
      have hroot (n : ℕ) :
          (∫⁻ ω, f n ω ^ p ∂P) ^ (1 / p) ≤ K ^ (1 / p) * (q ^ (1 / p)) ^ n :=
        calc
          (∫⁻ ω, f n ω ^ p ∂P) ^ (1 / p) ≤ (K * q ^ n) ^ (1 / p) :=
            ENNReal.rpow_le_rpow (hbound n) hinv.le
          _ = K ^ (1 / p) * (q ^ n) ^ (1 / p) := ENNReal.mul_rpow_of_nonneg _ _ hinv.le
          _ = K ^ (1 / p) * (q ^ (1 / p)) ^ n := by rw [weightedDyadicSum_pow_rpow_comm]
      calc
        ∫⁻ ω, (∑' n, f n ω) ^ p ∂P ≤ (∑' n, (∫⁻ ω, f n ω ^ p ∂P) ^ (1 / p)) ^ p :=
          ennreal_lintegral_rpow_tsum_le_of_roots_summable f p hp.le hf
        _ ≤ (∑' n : ℕ, K ^ (1 / p) * (q ^ (1 / p)) ^ n) ^ p :=
          ENNReal.rpow_le_rpow (ENNReal.tsum_le_tsum hroot) hp0.le
        _ = (K ^ (1 / p) * (1 - q ^ (1 / p))⁻¹) ^ p := by
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
        _ < ⊤ := ENNReal.rpow_lt_top_of_nonneg hp0.le (ENNReal.mul_lt_top ((ENNReal.rpow_lt_top_of_nonneg hinv.le hK).ne).lt_top (ENNReal.inv_lt_top.2 (tsub_pos_of_lt (ENNReal.rpow_lt_one hq hinv)))).ne
    have weightedDyadicSum_lintegral_tsum_rpow_lt_top_of_le_one (hp1 : p ≤ 1) {K : ℝ≥0∞} {q : ℝ≥0∞} (hK : K ≠ ⊤) (hq : q < 1) (hbound : ∀ n, ∫⁻ ω, f n ω ^ p ∂P ≤ K * q ^ n) : ∫⁻ ω, (∑' n, f n ω) ^ p ∂P < ⊤ := by
      calc
        ∫⁻ ω, (∑' n, f n ω) ^ p ∂P ≤ ∫⁻ ω, ∑' n, f n ω ^ p ∂P :=
          lintegral_mono fun ω => ennreal_rpow_tsum_le_tsum_rpow _ hp hp1
        _ = ∑' n, ∫⁻ ω, f n ω ^ p ∂P := lintegral_tsum (fun n => ENNReal.continuous_rpow_const.measurable.comp_aemeasurable (hf n))
        _ ≤ ∑' n : ℕ, K * q ^ n := ENNReal.tsum_le_tsum hbound
        _ = K * (1 - q)⁻¹ := by rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
        _ < ⊤ := ENNReal.mul_lt_top hK.lt_top (ENNReal.inv_lt_top.2 (tsub_pos_of_lt hq))
    rcases le_or_gt p 1 with hp1 | hp1
    · exact weightedDyadicSum_lintegral_tsum_rpow_lt_top_of_le_one hp1 hK hq hbound
    · exact weightedDyadicSum_lintegral_tsum_rpow_lt_top_of_one_lt hp1 hK hq hbound
  let qReal := (1 / 2 : ℝ) ^ (ξ - γ * α * p)
  let shell : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    ENNReal.rpow (ENNReal.ofReal (R / (2 : ℝ) ^ (n + 1))) (-γ * α) *
      M ω (Metric.ball z (R / (2 : ℝ) ^ n))
  have hqNonneg : 0 ≤ qReal := Real.rpow_nonneg (by norm_num) _
  have hshellBound (n : ℕ) : ∫⁻ ω, shell n ω ^ p ∂P ≤
      ENNReal.ofReal (C * (R / 2) ^ (-γ * α * p) * R ^ ξ) * ENNReal.ofReal qReal ^ n := by
    refine (weightedDyadicSum_shell_moment_le n hball).trans ?_
    rw [weightedDyadicSum_real_term n, ENNReal.ofReal_mul' (pow_nonneg hqNonneg n),
      ENNReal.ofReal_pow hqNonneg]
  calc
    weightedGmcBallMoment P M γ α z R p
        ≤ ∫⁻ ω, (∑' n, shell n ω) ^ p ∂P :=
      lintegral_mono fun ω => ENNReal.rpow_le_rpow
        (weightedGmcBallMass_le_dyadic_charge_center (M ω) γ α R z hγ hα hR hR1) hp.le
    _ < ⊤ := (weightedDyadicSum_lintegral_tsum_rpow_lt_top shell (fun n => aemeasurable_const.mul (hM _ Metric.isOpen_ball.measurableSet)) hp ENNReal.ofReal_ne_top (ENNReal.ofReal_lt_one.2 (Real.rpow_lt_one (by norm_num) (by norm_num) he)) hshellBound)

end DOZZ.Proofs
