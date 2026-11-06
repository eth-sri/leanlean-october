/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.WeightedCenterInsertion
public import DOZZ.GMC.SharpMoments.WeightedCenterTransfer
public import DOZZ.Statements.GMC.WeightedGmcBallMoment

/-! # The sharp weighted local moment range

For `α < Q`, the weighted local moment of positive order `p` is finite exactly when `p` lies below
both the bulk threshold `4/γ²` and the insertion threshold `2(Q-α)/γ`. Sufficiency is the dyadic
shell bound; at and above `4/γ²` an off-center subdisk already diverges; between the insertion and
bulk thresholds the moment at the chart center diverges by exact scaling, and the truncated-weight
location transfer carries the divergence to every center. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs



/-- Sharp one-root weighted local moment threshold. -/
theorem equatorGFF_GMC_weighted_local_moment_range
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) X (hX : IsEquatorGFF P X)
    γ (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) α (hα : α < Q γ)
    p (hp : 0 < p) z r (hr : 0 < r) :
    (weightedGmcBallMoment P M γ α z r p < ⊤) ↔
      p < min (4 / γ ^ 2) (2 / γ * (Q γ - α)) := by
  have weightedInsertion_exponent_nonpos {α} (hp4 : p < 4 / γ ^ 2) (hins : 2 / γ * (Q γ - α) ≤ p) : 0 < α ∧ (2 - γ * α) * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2 ≤ 0 := by
    have : Q γ - α ≤ γ * p / 2 := by
      have h := mul_le_mul_of_nonneg_left hins (by positivity : (0 : ℝ) ≤ γ / 2)
      rw [(show γ / 2 * (2 / γ * (Q γ - α)) = Q γ - α by field_simp)] at h
      linarith
    have : γ * p / 2 < 2 / γ := by
      have h := mul_lt_mul_of_pos_left hp4 (by positivity : (0 : ℝ) < γ / 2)
      rw [(show γ / 2 * (4 / γ ^ 2) = 2 / γ by field_simp; ring)] at h
      linarith
    have : Q γ - 2 / γ = γ / 2 := by
      rw [Q]
      ring
    refine ⟨by linarith, ?_⟩
    rw [(show (2 - γ * α) * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2 = γ * p * ((Q γ - α) - γ * p / 2) by rw [(show 2 - γ * α = γ * Q γ - γ ^ 2 / 2 - γ * α by rw [(show γ * Q γ = 2 + γ ^ 2 / 2 by rw [Q]; field_simp)]; ring)]; ring)]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  have weightedGmcBallMoment_eq_top_of_insertion (hα : 0 < α) p (hp : 0 < p) (hp4 : p < 4 / γ ^ 2) (he : (2 - γ * α) * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2 ≤ 0) z r (hr : 0 < r) : weightedGmcBallMoment P M γ α z r p = ⊤ := by
    set ρ : ℝ := min r (1 / 8) with hρdef
    have hρ : 0 < ρ := lt_min hr (by norm_num)
    have hρ8 : ρ ≤ 1 / 8 := min_le_right _ _
    have h0 := weightedGmcBallMoment_center_eq_top_of_insertion P X hX γ hγ hγ2 M hM α hα p hp he
      ρ hρ (by linarith)
    have htr := weightedGmcBallMoment_center_le_transfer P X hX γ hγ hγ2 M hM α z ρ hρ hρ8 p hp hp4
    rw [h0] at htr
    apply top_unique
    rw [← (show weightedGmcBallMoment P M γ α z ρ p = ⊤ by by_contra hne; exact absurd htr (not_le.mpr (ENNReal.mul_lt_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.rpow_ne_top_of_nonneg (abs_nonneg p) ENNReal.ofReal_ne_top)).lt_top (lt_top_iff_ne_top.mpr hne))))]
    exact lintegral_mono fun ω => ENNReal.rpow_le_rpow
      (lintegral_mono_set (Metric.ball_subset_ball (min_le_left _ _))) hp.le
  -- the charge bound `α < Q` only makes the insertion range nonempty
  have _ := hα
  constructor
  · intro hfin
    by_contra hnot
    rw [lt_min_iff, not_and_or, not_lt, not_lt] at hnot
    by_cases hp4 : p < 4 / γ ^ 2
    · have hins : 2 / γ * (Q γ - α) ≤ p := hnot.resolve_left (not_le.mpr hp4)
      obtain ⟨hα0, he⟩ := weightedInsertion_exponent_nonpos hp4 hins
      rw [weightedGmcBallMoment_eq_top_of_insertion hα0 p hp hp4 he z r
        hr] at hfin
      exact lt_irrefl _ hfin
    · rw [weightedGmcBallMoment_eq_top_of_bulk P X hX γ hγ hγ2 M hM α z r hr p
        (not_lt.mp hp4)] at hfin
      exact lt_irrefl _ hfin
  · intro hrange
    exact weightedGmcBallMoment_lt_top_of_sharp_range P X hX γ hγ hγ2 M hM α z r hr p hp hrange

end DOZZ.Proofs
