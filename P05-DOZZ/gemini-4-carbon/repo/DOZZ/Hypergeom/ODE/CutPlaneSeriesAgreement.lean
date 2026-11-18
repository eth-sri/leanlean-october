/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.CutPlaneHolomorphic
public import DOZZ.Hypergeom.ODE.SeriesEquation
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Convex.PathConnected

/-! Agreement of path-independent Gauss continuations with the ordinary series. -/

@[expose] public section

open Filter Set Topology

namespace DOZZ.Proofs



/-- On the cut plane, the endpoint continuation recovers the ordinary series throughout the unit
disk. -/
theorem gaussCutPlaneScalarState_eq_ordinary_on_unitDisk
    (a b c : ℂ) (hc : ∀ n : ℕ, c ≠ -(n : ℂ))
    {z : ℂ} (hz : z ∈ gaussCutPlane) (hznorm : ‖z‖ < 1) :
    gaussCutPlaneScalarState a b c z = ordinaryHypergeometric a b c z := by
  have gaussCutPlaneScalarState_eq_ordinary_eventually : gaussCutPlaneScalarState a b c =ᶠ[𝓝 (gaussCutPlaneMidpoint : ℂ)]
        ordinaryHypergeometric a b c := by
    have gaussCutPlaneContinuationState_midpoint_eq_seriesState : gaussCutPlaneContinuationState a b c gaussCutPlaneMidpoint =
          ordinaryHypergeometricState a b c (1 / 2 : ℂ) := by
      obtain ⟨r, M, hr, _, hM, D, hcenter, hbound, hseries⟩ :=
        exists_gauss_ordinary_seed_disk a b c hc
      let y := ordinaryHypergeometricState a b c (1 / 2 : ℂ)
      have hcenter' : D.center = (gaussCutPlaneMidpoint : ℂ) := by
        simpa [gaussCutPlaneMidpoint] using hcenter
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
        intro t ht
        change ((Path.refl gaussCutPlaneMidpoint)
          (Set.projIcc 0 1 zero_le_one t) : ℂ) = _
        rfl
      let Q := path_continuation_lift_congr Q₀ hrefl
      let A := gaussCutPlaneCanonicalContinuationLift a b c gaussCutPlaneMidpoint
      have hendpoint := gauss_cut_plane_path_lifts_endpoint_eq a b c
        (gaussCutPlaneCanonicalPath gaussCutPlaneMidpoint)
        (Path.refl gaussCutPlaneMidpoint) y A Q
      change (gaussCutPlaneCanonicalContinuationLift a b c gaussCutPlaneMidpoint).value 1 = y
      exact hendpoint
    obtain ⟨r₀, M₀, hr₀, _, hM₀, D₀, hD₀center, hD₀bound, hD₀series⟩ :=
      exists_gauss_ordinary_seed_disk a b c hc
    obtain ⟨R, δ, hR, hδ, hδR, D, hDcenter, hlocal⟩ :=
      gaussCutPlaneContinuationState_locally_eq_picard a b c gaussCutPlaneMidpoint
    have hcenter : (gaussCutPlaneMidpoint : ℂ) = (1 / 2 : ℂ) := by
      rfl
    have hD₀center' : D₀.center = (gaussCutPlaneMidpoint : ℂ) := by
      exact (hD₀center).trans (hcenter.symm)
    let y := ordinaryHypergeometricState a b c (1 / 2 : ℂ)
    have hstateMid :
        gaussCutPlaneContinuationState a b c gaussCutPlaneMidpoint = y := gaussCutPlaneContinuationState_midpoint_eq_seriesState
    have hDmid : D.solution (gaussCutPlaneMidpoint : ℂ) = y := by
      calc
        D.solution (gaussCutPlaneMidpoint : ℂ) =
            gaussCutPlaneContinuationState a b c gaussCutPlaneMidpoint := by
              symm
              exact hlocal gaussCutPlaneMidpoint (by simp [dist_self, hδ])
        _ = y := hstateMid
    have hD₀mid : D₀.solution (gaussCutPlaneMidpoint : ℂ) = y := by
      have hmidball : (gaussCutPlaneMidpoint : ℂ) ∈
          Metric.ball (1 / 2 : ℂ) r₀ := by
        rw [hcenter]
        exact Metric.mem_ball_self hr₀
      exact hD₀series (gaussCutPlaneMidpoint : ℂ) hmidball
    let H := gaussSystemOperator a b c
    obtain ⟨rU, MU, hrU, hMU, hlocalU⟩ :=
      exists_uniform_holomorphic_disks_on_compact
        isCompact_singleton (fun z : ℂ => z) continuousOn_id
        gaussRegularPlane gaussRegularPlane_isOpen H
        (gaussSystemOperator_differentiableOn a b c)
        (by rintro z rfl; exact gaussCutPlane_subset_regularPlane gaussCutPlaneMidpoint.property)
    let ρ := min δ (min r₀ rU)
    have hρ : 0 < ρ := lt_min hδ (lt_min hr₀ hrU)
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
      rw [hD₀center']
      exact lt_of_lt_of_le hz hρr₀
    have hboundρ : ∀ z ∈ Metric.ball (gaussCutPlaneMidpoint : ℂ) ρ,
        ‖H z‖ ≤ MU := by
      intro z hz
      exact (hlocalU (gaussCutPlaneMidpoint : ℂ) (by simp)).2 z (Metric.ball_subset_ball hρrU hz)
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
    have hσρ : σ ≤ ρ := min_le_left _ _
    have hσε : σ ≤ ε := min_le_right _ _
    have hnear : gaussCutPlaneScalarState a b c =ᶠ[𝓝 (gaussCutPlaneMidpoint : ℂ)]
        ordinaryHypergeometric a b c := by
      filter_upwards [Metric.ball_mem_nhds (gaussCutPlaneMidpoint : ℂ) (lt_min hρ hε)]
        with z hz
      have hzcut :=
        hεball (Metric.ball_subset_ball hσε hz)
      let w : gaussCutPlane := ⟨z, hzcut⟩
      have hzρ :=
        Metric.ball_subset_ball hσρ hz
      have hzseed : z ∈ Metric.ball (1 / 2 : ℂ) r₀ := by
        simpa [hD₀center] using hballD₀ hzρ
      dsimp [gaussCutPlaneScalarState]
      rw [dite_eq_left hzcut]
      exact ((congrArg Prod.fst (hlocal w (lt_of_lt_of_le (Metric.mem_ball.mp hz) (le_trans hσρ hρδ)))).trans (congrArg Prod.fst (hDunique z hzρ))).trans (congrArg Prod.fst (hD₀series z hzseed))
    exact hnear
  let V := gaussCutPlane ∩ Metric.ball (0 : ℂ) 1
  have hbaseBall : (gaussCutPlaneMidpoint : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    change dist (1 / 2 : ℂ) 0 < 1
    norm_num [dist_eq_norm]
  have hbaseV : (gaussCutPlaneMidpoint : ℂ) ∈ V :=
    ⟨gaussCutPlaneMidpoint.property, hbaseBall⟩
  have hFanalyticV : AnalyticOnNhd ℂ (gaussCutPlaneScalarState a b c) V :=
    fun w hw => ((gaussCutPlaneScalarState_differentiableOn a b c).analyticOnNhd gaussCutPlane_isOpen) w hw.1
  have hseriesAnalyticV : AnalyticOnNhd ℂ (ordinaryHypergeometric a b c) V :=
    fun w hw => (ordinaryHypergeometric_analyticOnNhd_unitDisk a b c hc) w hw.2
  have hidentity :=
    AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      hFanalyticV hseriesAnalyticV (((gaussCutPlane_starConvex.inter ((convex_ball (0 : ℂ) 1).starConvex hbaseBall)).isPathConnected hbaseV).isConnected.isPreconnected) hbaseV
      (gaussCutPlaneScalarState_eq_ordinary_eventually)
  have hznorm' : z ∈ Metric.ball (0 : ℂ) 1 := by
    simpa [Metric.mem_ball, dist_zero_right] using hznorm
  exact hidentity ⟨hz, hznorm'⟩

end DOZZ.Proofs
