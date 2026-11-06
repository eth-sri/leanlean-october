/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.WeightedLocalBasic
public import DOZZ.GMC.SharpMoments.WeightedDyadicSum
public import DOZZ.GMC.SharpMoments.BallScaling

/-! # Finiteness of weighted local moments in the sharp range

Below both the bulk threshold `4/γ²` and the insertion threshold `2(Q-α)/γ`, the weighted local
moment is finite at every center and radius. For small radii the dyadic shell sum is controlled by
the sharp ball upper bound at the center; larger radii add a bounded weight times the mass of a
bounded disk. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Integrals of a fixed measurable function over a fixed measurable set against an `IsGMCOf`
version are a.e. measurable. -/
theorem gmc_setLIntegral_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) X (hX : IsEquatorGFF P X)
    γ (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (f : ℂ → ℝ≥0∞) (hf : Measurable f) s (hs : MeasurableSet s) :
    AEMeasurable (fun ω => ∫⁻ x in s, f x ∂M ω) P := by
  obtain ⟨N, hN, _, hMN⟩ := equatorGFF_GMC_measurable_version P X hX γ hγ hγ2 M hM
  have hNint : Measurable (fun ω => ∫⁻ x, s.indicator f x ∂N ω) :=
    (Measure.measurable_lintegral (hf.indicator hs)).comp hN
  refine hNint.aemeasurable.congr ?_
  filter_upwards [hMN] with ω hω
  rw [lintegral_indicator hs, hω]

/-- Weighted local masses of an `IsGMCOf` version are a.e. measurable. -/
theorem gmc_weighted_mass_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) X (hX : IsEquatorGFF P X)
    γ (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    α z r :
    AEMeasurable (fun ω => weightedGmcBallMass γ (M ω) α z r) P :=
  gmc_setLIntegral_aemeasurable P X hX γ hγ hγ2 M hM
    (fun x => ENNReal.rpow (ENNReal.ofReal ‖x - z‖) (-γ * α))
    ((ENNReal.continuous_rpow_const (y := -γ * α)).measurable.comp
      (ENNReal.measurable_ofReal.comp (measurable_id.sub_const z).norm)) _
    Metric.isOpen_ball.measurableSet



/-- Weighted local moments are finite in the sharp range at every center and radius. -/
theorem weightedGmcBallMoment_lt_top_of_sharp_range
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) X (hX : IsEquatorGFF P X)
    γ (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    α z r (hr : 0 < r) p (hp : 0 < p)
    (hpRange : p < min (4 / γ ^ 2) (2 / γ * (Q γ - α))) :
    weightedGmcBallMoment P M γ α z r p < ⊤ := by
  have weightedGmcBallMoment_lt_top_of_pos_charge_small (hα : 0 < α) z r (hr : 0 < r) (hr8 : r ≤ 1 / 8) p (hp : 0 < p) (hpRange : p < min (4 / γ ^ 2) (2 / γ * (Q γ - α))) : weightedGmcBallMoment P M γ α z r p < ⊤ := by
    have sharpBallExponent_sub_insertion : 2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2 - γ * α * p = γ * (Q γ - α) * p - γ ^ 2 * p ^ 2 / 2 := by
      rw [Q]
      field_simp
      ring
    let _ : IsProbabilityMeasure P := hX.1
    obtain ⟨C, -, hC⟩ := gmc_ball_moment_sharp_upper_center P X hX γ hγ hγ2 M hM z p
      (lt_min_iff.mp hpRange).1
    exact weightedGmcBallMoment_lt_top_of_ball_upper P M
      (fun s hs => gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM s hs)
      γ α p _ C r z hγ hα hp hr (hr8.trans (by norm_num)) (by rw [sharpBallExponent_sub_insertion]; exact weightedGmcMomentExponent_pos_of_sharp_range hγ hp hpRange)
      (fun ρ hρ hρr => hC ρ hρ (hρr.trans hr8))
  let _ : IsProbabilityMeasure P := hX.1
  have hpBulk := (lt_min_iff.mp hpRange).1
  rcases le_or_gt α 0 with hα | hα
  · exact weightedGmcBallMoment_lt_top_of_nonpos_charge P X hX γ hγ hγ2 M hM α hα z r p hp
      hpBulk
  rcases le_or_gt r (1 / 8) with hr8 | hr8
  · exact weightedGmcBallMoment_lt_top_of_pos_charge_small hα z r hr hr8
      p hp hpRange
  set ρ : ℝ := 1 / 8 with hρ
  set c : ℝ≥0∞ := ENNReal.ofReal (ρ ^ (-γ * α)) with hc
  have hinner := weightedGmcBallMoment_lt_top_of_pos_charge_small hα z ρ
    (by norm_num) le_rfl p hp hpRange
  have hW := gmc_weighted_mass_aemeasurable P X hX γ hγ hγ2 M hM α z ρ
  have hB := gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM (Metric.ball z r)
    Metric.isOpen_ball.measurableSet
  set L : ℝ≥0∞ := ENNReal.LpAddConst (ENNReal.ofReal p)⁻¹ with hL
  have hLtop : L ≠ ⊤ := (ENNReal.LpAddConst_lt_top _).ne
  calc weightedGmcBallMoment P M γ α z r p
      ≤ ∫⁻ ω, L * (weightedGmcBallMass γ (M ω) α z ρ ^ p +
          c ^ p * M ω (Metric.ball z r) ^ p) ∂P := by
        apply lintegral_mono
        intro ω
        calc ENNReal.rpow (weightedGmcBallMass γ (M ω) α z r) p
            ≤ (weightedGmcBallMass γ (M ω) α z ρ + c * M ω (Metric.ball z r)) ^ p :=
              ENNReal.rpow_le_rpow (weightedGmcBallMass_le_inner_add_total (M ω) γ α z r ρ (mul_pos hγ hα) (by norm_num)) hp.le
          _ ≤ L * (weightedGmcBallMass γ (M ω) α z ρ ^ p + (c * M ω (Metric.ball z r)) ^ p) :=
              ENNReal.rpow_add_le_mul_rpow_add_rpow' _ _ hp.le
          _ = L * (weightedGmcBallMass γ (M ω) α z ρ ^ p +
                c ^ p * M ω (Metric.ball z r) ^ p) := by
              rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le]
    _ = L * (weightedGmcBallMoment P M γ α z ρ p +
          c ^ p * gmcMassMoment P M (Metric.ball z r) p) := by
        have hsum : AEMeasurable (fun ω => weightedGmcBallMass γ (M ω) α z ρ ^ p +
            c ^ p * M ω (Metric.ball z r) ^ p) P :=
          (hW.pow_const p).add ((hB.pow_const p).const_mul _)
        rw [lintegral_const_mul'' _ hsum, lintegral_add_left' (hW.pow_const p),
          lintegral_const_mul'' _ (hB.pow_const p)]
        rfl
    _ < ⊤ := ENNReal.mul_lt_top hLtop.lt_top (ENNReal.add_lt_top.mpr
        ⟨hinner, ENNReal.mul_lt_top (ENNReal.rpow_ne_top_of_nonneg hp.le ENNReal.ofReal_ne_top).lt_top (gmc_bounded_moment_lt_top P X hX γ hγ hγ2 M hM (Metric.ball z r) Metric.isBounded_ball p hp.le hpBulk)⟩)

end DOZZ.Proofs
