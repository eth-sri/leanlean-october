/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.MomentRange
public import DOZZ.Statements.GMC.WeightedGmcBallMoment
public import DOZZ.GMC.Moments.WeightedLocalSubunit
public import DOZZ.GMC.Moments.WeightedExponent

/-! # Elementary bounds for weighted local masses

A weighted local mass dominates a fixed multiple of the mass of an off-center subdisk, so it
inherits the divergence of unweighted moments at and above `4/γ²`. For nonpositive charges the
weight is bounded on the disk and the unweighted moment range gives finiteness below `4/γ²`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs
section
variable (z : ℂ) {r : ℝ}
section
variable (hr : 0 < r)
include hr

theorem offcenter_ball_subset :
    Metric.ball (z + ((r / 2 : ℝ) : ℂ)) (r / 4) ⊆ Metric.ball z r := by
  intro x hx
  rw [Metric.mem_ball, dist_eq_norm] at hx ⊢
  have hc : ‖((r / 2 : ℝ) : ℂ)‖ = r / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc ‖x - z‖ = ‖(x - (z + ((r / 2 : ℝ) : ℂ))) + ((r / 2 : ℝ) : ℂ)‖ := by congr 1; ring
    _ ≤ ‖x - (z + ((r / 2 : ℝ) : ℂ))‖ + ‖((r / 2 : ℝ) : ℂ)‖ := norm_add_le ..
    _ < r := by linarith

theorem offcenter_dist_bounds {x : ℂ}
    (hx : x ∈ Metric.ball (z + ((r / 2 : ℝ) : ℂ)) (r / 4)) :
    r / 4 ≤ ‖x - z‖ ∧ ‖x - z‖ ≤ 3 * r / 4 := by
  rw [Metric.mem_ball, dist_eq_norm] at hx
  have hc : ‖((r / 2 : ℝ) : ℂ)‖ = r / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have h1 : x - z = (x - (z + ((r / 2 : ℝ) : ℂ))) + ((r / 2 : ℝ) : ℂ) := by ring
  constructor
  · have h2 : ((r / 2 : ℝ) : ℂ) = (x - z) - (x - (z + ((r / 2 : ℝ) : ℂ))) := by ring
    have h3 := norm_sub_le (x - z) (x - (z + ((r / 2 : ℝ) : ℂ)))
    grind
  · rw [h1]
    linarith [norm_add_le (x - (z + ((r / 2 : ℝ) : ℂ))) ((r / 2 : ℝ) : ℂ)]

end

end

/-- The weight of a weighted local mass is bounded below on the off-center subdisk. -/
theorem weightedGmcBallMass_ge_offcenter (μ : Measure ℂ) (γ α : ℝ) (z : ℂ) {r : ℝ}
    (hr : 0 < r) :
    min (ENNReal.rpow (ENNReal.ofReal (r / 4)) (-γ * α))
        (ENNReal.rpow (ENNReal.ofReal (3 * r / 4)) (-γ * α)) *
        μ (Metric.ball (z + ((r / 2 : ℝ) : ℂ)) (r / 4)) ≤
      weightedGmcBallMass γ μ α z r := by
  set B := Metric.ball (z + ((r / 2 : ℝ) : ℂ)) _ with hB
  have hBm : MeasurableSet B := Metric.isOpen_ball.measurableSet
  calc min _
          (ENNReal.rpow ..) * μ B
      = ∫⁻ _x in B, min (ENNReal.rpow (ENNReal.ofReal (r / 4)) (-γ * α))
          (ENNReal.rpow (ENNReal.ofReal (3 * r / 4)) (-γ * α)) ∂μ := by
        simp
    _ ≤ ∫⁻ x in B, ENNReal.rpow _ _ ∂μ := by
        apply setLIntegral_mono' hBm
        intro x hx
        obtain ⟨h1, h2⟩ := offcenter_dist_bounds z hr hx
        rcases le_or_gt 0 (-γ * α) with hs | hs
        · refine (min_le_left ..).trans ?_
          exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal h1) hs
        · refine (min_le_right ..).trans ?_
          exact ennreal_rpow_antitone_of_nonpos (ENNReal.ofReal_le_ofReal h2) hs.le
    _ ≤ ∫⁻ x in Metric.ball z r, ENNReal.rpow _ _ ∂μ :=
        lintegral_mono_set (offcenter_ball_subset z hr)
section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
section
variable (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (α : ℝ)
include hX hγ hγ2 hM

/-- At and above `4/γ²` every positive-order weighted local moment diverges. -/
theorem weightedGmcBallMoment_eq_top_of_bulk
    (z : ℂ) (r : ℝ) (hr : 0 < r) (p : ℝ) (hp : 4 / γ ^ 2 ≤ p) :
    weightedGmcBallMoment P M γ α z r p = ⊤ := by
  have hp0 : 0 < p := lt_of_lt_of_le (by positivity) hp
  set c := min (ENNReal.rpow (ENNReal.ofReal (r / 4)) (-γ * α))
    (ENNReal.rpow (ENNReal.ofReal (3 * r / 4)) (-γ * α)) with hc
  have hc0 : c ≠ 0 := by
    simp_all
  have hctop : c ≠ ⊤ := by
    simp_all
  have htop := gmc_ball_moment_eq_top_of_critical_le P X hX γ hγ hγ2 M hM
    (z + ((r / 2 : ℝ) : ℂ)) (r / 4) (by positivity) p hp
  have hmeas : AEMeasurable (fun ω => M ω (Metric.ball (z + ((r / 2 : ℝ) : ℂ)) (r / 4)) ^ p) P :=
    (gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM _
      Metric.isOpen_ball.measurableSet).pow_const _
  apply top_unique
  calc ⊤ = c ^ p * gmcMassMoment P M (Metric.ball (z + ((r / 2 : ℝ) : ℂ)) (r / 4)) p := by
        rw [htop, ENNReal.mul_top (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hc0) hctop).ne']
    _ = ∫⁻ ω, (c * M ω (Metric.ball (z + ((r / 2 : ℝ) : ℂ)) (r / 4))) ^ p ∂P := by
        rw [lintegral_congr (fun ω => ENNReal.mul_rpow_of_nonneg c
          (M ω (Metric.ball (z + ((r / 2 : ℝ) : ℂ)) (r / 4))) hp0.le),
          lintegral_const_mul'' _ hmeas]
        rfl
    _ ≤ weightedGmcBallMoment P M γ α z r p := by
        apply lintegral_mono
        intro ω
        exact ENNReal.rpow_le_rpow (weightedGmcBallMass_ge_offcenter (M ω) γ α z hr) hp0.le

/-- For nonpositive charges the weighted local moment is finite below `4/γ²`. -/
theorem weightedGmcBallMoment_lt_top_of_nonpos_charge
    (hα : α ≤ 0) (z : ℂ) (r p : ℝ) (hp0 : 0 < p)
    (hp : p < 4 / γ ^ 2) :
    weightedGmcBallMoment P M γ α z r p < ⊤ := by
  have hs : 0 ≤ -γ * α := by nlinarith
  set c := ENNReal.rpow (ENNReal.ofReal r) _ with hc
  have hctop : c ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hs ENNReal.ofReal_ne_top
  have hbound : ∀ ω, weightedGmcBallMass γ (M ω) α z r ≤ c * M ω (Metric.ball z r) := by
    intro ω
    calc ∫⁻ x in Metric.ball z r, ENNReal.rpow _ _ ∂M ω
        ≤ ∫⁻ _x in Metric.ball z r, c ∂M ω := by
          apply setLIntegral_mono' Metric.isOpen_ball.measurableSet
          intro x hx
          rw [Metric.mem_ball, dist_eq_norm] at hx
          exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hx.le) hs
      _ = c * M ω _ := setLIntegral_const ..
  have hmeas : AEMeasurable (fun ω => M ω (Metric.ball z r) ^ p) P :=
    (gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM _
      Metric.isOpen_ball.measurableSet).pow_const _
  have hfin := gmc_bounded_moment_lt_top P X hX γ hγ hγ2 M hM (Metric.ball z r)
    Metric.isBounded_ball p hp0.le hp
  calc weightedGmcBallMoment P M γ α z r p
      ≤ ∫⁻ ω, (c * M ω _) ^ p ∂P := by
        apply lintegral_mono
        intro ω
        exact ENNReal.rpow_le_rpow (hbound ω) hp0.le
    _ = c ^ p * gmcMassMoment P M _ p := by
        rw [lintegral_congr (fun ω => ENNReal.mul_rpow_of_nonneg c _
          hp0.le), lintegral_const_mul'' _ hmeas]
        rfl
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hp0.le hctop) hfin

end

end

end DOZZ.Proofs
