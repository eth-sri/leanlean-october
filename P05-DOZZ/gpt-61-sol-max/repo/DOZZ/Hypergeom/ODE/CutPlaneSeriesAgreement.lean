/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.CutPlaneHolomorphic
public import DOZZ.Hypergeom.ODE.SeriesEquation
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Tactic

/-! Agreement of path-independent Gauss continuations with the ordinary series. -/

public section

open Filter Set Topology

namespace DOZZ.Proofs

variable (a b c : ℂ) (hc : ∀ n : ℕ, c ≠ -(n : ℂ))

include a b c hc in
/-- The selected continuation at `1/2` has its prescribed ordinary-series initial value. -/
theorem gaussCutPlaneContinuationState_midpoint_eq_seriesState
     :
    gaussCutPlaneContinuationState a b c gaussCutPlaneMidpoint =
      ordinaryHypergeometricState a b c (1 / 2 : ℂ) := by
  obtain ⟨r, M, hr, _, hM, D, hcenter, hbound, hseries⟩ :=
    exists_gauss_ordinary_seed_disk a b c hc
  let y := ordinaryHypergeometricState a b c (1 / 2 : ℂ)
  have hcenter' : D.center = (gaussCutPlaneMidpoint : ℂ) := by
    exact hcenter
  have hinitial : D.initial = y := by
    calc
      D.initial = D.solution D.center := D.solution_center.symm
      _ = D.solution (gaussCutPlaneMidpoint : ℂ) := by rw [hcenter']
      _ = y := hseries _ (Metric.mem_ball_self hr)
  let Q₀ := constant_path_continuation_lift
    (gaussCutPlaneMidpoint : ℂ) r M hr hM D hcenter' hbound hinitial
  have hrefl : ∀ t ∈ Icc (0 : ℝ) 1,
      gaussCutPlanePathFunction (Path.refl gaussCutPlaneMidpoint) t =
        (gaussCutPlaneMidpoint : ℂ) := by
    continuity
  let Q := path_continuation_lift_congr Q₀ hrefl
  let A := gaussCutPlaneCanonicalContinuationLift a b c gaussCutPlaneMidpoint
  have hendpoint := gauss_cut_plane_path_lifts_endpoint_eq a b c
    (gaussCutPlaneCanonicalPath gaussCutPlaneMidpoint)
    (Path.refl gaussCutPlaneMidpoint) y A Q
  assumption_mod_cast

include a b c hc in
/-- Near `1/2`, the cut-plane endpoint's scalar component is the ordinary Gauss series. -/
theorem gaussCutPlaneScalarState_eq_ordinary_eventually
     :
    gaussCutPlaneScalarState a b c =ᶠ[𝓝 (gaussCutPlaneMidpoint : ℂ)]
      ordinaryHypergeometric a b c := by
  obtain ⟨r₀, M₀, hr₀, _, hM₀, D₀, hD₀center, hD₀bound, hD₀series⟩ :=
    exists_gauss_ordinary_seed_disk a b c hc
  obtain ⟨R, δ, hR, hδ, hδR, D, hDcenter, hlocal⟩ :=
    gaussCutPlaneContinuationState_locally_eq_picard a b c gaussCutPlaneMidpoint
  have hcenter : (gaussCutPlaneMidpoint : ℂ) = (1 / 2 : ℂ) := by
    rfl
  
  let y := ordinaryHypergeometricState a b c (1 / 2 : ℂ)
  have hstateMid :
      gaussCutPlaneContinuationState a b c gaussCutPlaneMidpoint = y := gaussCutPlaneContinuationState_midpoint_eq_seriesState a b c hc
  have hDmid : D.solution (gaussCutPlaneMidpoint : ℂ) = y := by
    simp_all
  have hD₀mid : D₀.solution (gaussCutPlaneMidpoint : ℂ) = y := by
    continuity
  let H : ℂ → ℂ × ℂ →L[ℂ] ℂ × ℂ := gaussSystemOperator a b c
  have hbaseRegular  :=
    gaussCutPlane_subset_regularPlane gaussCutPlaneMidpoint.property
  obtain ⟨rU, MU, hrU, hMU, hlocalU⟩ :=
    exists_uniform_holomorphic_disks_on_compact
      isCompact_singleton (fun z : ℂ => z) continuousOn_id
      gaussRegularPlane gaussRegularPlane_isOpen H
      (gaussSystemOperator_differentiableOn a b c)
      (by rintro z rfl; exact hbaseRegular)
  have hlocalUbase := hlocalU (gaussCutPlaneMidpoint : ℂ) (by simp)
  let ρ := min δ (min r₀ rU)
  have hρ  := lt_min hδ (lt_min hr₀ hrU)
  have hρδ : ρ ≤ δ := min_le_left _ _
  have hρr₀ : ρ ≤ r₀ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hρrU : ρ ≤ rU := le_trans (min_le_right _ _) (min_le_right _ _)
  have hρR : ρ ≤ R := by linarith [hρδ, hδR]
  have hballD : Metric.ball (gaussCutPlaneMidpoint : ℂ) ρ ⊆ Metric.ball D.center R := by
    intro z hz
    rw [Metric.mem_ball] at hz ⊢
    rw [hDcenter]
    exact lt_of_lt_of_le hz hρR
  have hballD₀ : Metric.ball (gaussCutPlaneMidpoint : ℂ) ρ ⊆
      Metric.ball D₀.center r₀ := by
    intro z hz
    rw [Metric.mem_ball] at hz ⊢
    grind
  have hboundρ : ∀ z ∈ Metric.ball (gaussCutPlaneMidpoint : ℂ) ρ,
      ‖H z‖ ≤ MU := by
    intro z hz
    exact hlocalUbase.2 z (Metric.ball_subset_ball hρrU hz)
  have hDunique : ∀ z ∈ Metric.ball (gaussCutPlaneMidpoint : ℂ) ρ,
      D.solution z = D₀.solution z := by
    intro z hz
    exact holomorphic_linear_system_solution_unique_of_eq_at
      (gaussCutPlaneMidpoint : ℂ) ρ MU H hMU hboundρ
      (fun u hu => D.derivative u (hballD hu))
      (fun u hu => D₀.derivative u (hballD₀ hu))
      (Metric.mem_ball_self hρ) hz (hDmid.trans hD₀mid.symm)
  obtain ⟨ε, hε, hεball⟩ := Metric.mem_nhds_iff.mp
    (gaussCutPlane_isOpen.mem_nhds gaussCutPlaneMidpoint.property)
  let σ := min ρ ε
  have hσ  := lt_min hρ hε
  have hσρ : σ ≤ ρ := min_le_left _ _
  have hσε : σ ≤ ε := min_le_right _ _
  have hnear : gaussCutPlaneScalarState a b c =ᶠ[𝓝 (gaussCutPlaneMidpoint : ℂ)]
      ordinaryHypergeometric a b c := by
    filter_upwards [Metric.ball_mem_nhds (gaussCutPlaneMidpoint : ℂ) hσ]
      with z hz
    have hzcut  :=
      hεball (Metric.ball_subset_ball hσε hz)
    let w : gaussCutPlane := ⟨z, hzcut⟩
    have hzδ  := lt_of_lt_of_le (Metric.mem_ball.mp hz) (le_trans hσρ hρδ)
    have hstate := hlocal w hzδ
    have hzρ  :=
      Metric.ball_subset_ball hσρ hz
    have hpatch := hDunique z hzρ
    have hzseed : z ∈ Metric.ball (1 / 2 : ℂ) r₀ := by
      simpa [hD₀center] using hballD₀ hzρ
    dsimp [gaussCutPlaneScalarState]
    rw [dite_eq_left hzcut]
    calc
      (gaussCutPlaneContinuationState a b c w).1 = (D.solution z).1 :=
        congrArg Prod.fst hstate
      _ = (D₀.solution z).1 := congrArg Prod.fst hpatch
      _ = (ordinaryHypergeometricState a b c z).1 := congrArg Prod.fst (hD₀series z hzseed)
      _ = ordinaryHypergeometric a b c z := rfl
  exact hnear

include a b c hc in
/-- On the cut plane, the endpoint continuation recovers the ordinary series throughout the unit
disk. -/
theorem gaussCutPlaneScalarState_eq_ordinary_on_unitDisk
    
    {z : ℂ} (hz : z ∈ gaussCutPlane) (hznorm : ‖z‖ < 1) :
    gaussCutPlaneScalarState a b c z = ordinaryHypergeometric a b c z := by
  let V := gaussCutPlane ∩ Metric.ball (0 : ℂ) 1
  have hbaseBall : (gaussCutPlaneMidpoint : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    change dist (1 / 2 : ℂ) 0 < 1
    norm_num [dist_eq_norm]
  have hballStar  :=
    (convex_ball (0 : ℂ) 1).starConvex hbaseBall
  have hVstar  :=
    gaussCutPlane_starConvex.inter hballStar
  have hbaseV : (gaussCutPlaneMidpoint : ℂ) ∈ V :=
    ⟨gaussCutPlaneMidpoint.property, hbaseBall⟩
  have hVpre  :=
    (hVstar.isPathConnected hbaseV).isConnected.isPreconnected
  have hFanalytic  :=
    (gaussCutPlaneScalarState_differentiableOn a b c).analyticOnNhd gaussCutPlane_isOpen
  have hseriesAnalytic  :=
    ordinaryHypergeometric_analyticOnNhd_unitDisk a b c hc
  have hFanalyticV : AnalyticOnNhd ℂ (gaussCutPlaneScalarState a b c) V :=
    fun w hw => hFanalytic w hw.1
  have hseriesAnalyticV : AnalyticOnNhd ℂ (ordinaryHypergeometric a b c) V :=
    fun w hw => hseriesAnalytic w hw.2
  have hidentity  :=
    AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      hFanalyticV hseriesAnalyticV hVpre hbaseV
      (gaussCutPlaneScalarState_eq_ordinary_eventually a b c hc)
  continuity

end DOZZ.Proofs
