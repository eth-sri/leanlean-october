/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.NegativeCutPlaneHolomorphic
public import DOZZ.Hypergeom.ODE.SeriesEquation
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Convex.PathConnected

/-! Agreement of path-independent Gauss continuations with the ordinary series. -/

@[expose] public section

open Filter Set Topology

namespace DOZZ.Proofs



/-- On the negative cut plane, the endpoint continuation recovers the ordinary series throughout the unit
disk. -/
theorem gaussNegativeCutPlaneScalarState_eq_ordinary_on_unitDisk
    a b c (hc : ∀ n : ℕ, c ≠ -(n : ℂ))
    {z} (hz : z ∈ gaussNegativeCutPlane) (hznorm : ‖z‖ < 1) :
    gaussNegativeCutPlaneScalarState a b c z = ordinaryHypergeometric a b c z := by
  have gaussNegativeCutPlaneScalarState_eq_ordinary_eventually : gaussNegativeCutPlaneScalarState a b c =ᶠ[𝓝 (gaussNegativeCutPlaneBasepoint : ℂ)] ordinaryHypergeometric a b c := by
    have gaussNegativeCutPlaneContinuationState_basepoint_eq_seriesState : gaussNegativeCutPlaneContinuationState a b c gaussNegativeCutPlaneBasepoint = ordinaryHypergeometricState a b c (-1 / 2 : ℂ) := by
      obtain ⟨r, M, hr, _, hM, D, hcenter, hbound, hseries⟩ :=
        exists_gauss_ordinary_seed_disk_negative a b c hc
      let y := ordinaryHypergeometricState a b c (-1 / 2 : ℂ)
      have hcenter' : D.center = (gaussNegativeCutPlaneBasepoint : ℂ) := by
        simpa [gaussNegativeCutPlaneBasepoint] using hcenter
      have hinitial : D.initial = y := by
        calc
          D.initial = D.solution D.center := D.solution_center.symm
          _ = D.solution (gaussNegativeCutPlaneBasepoint : ℂ) := by rw [hcenter']
          _ = y := hseries _ (Metric.mem_ball_self hr)
      let Q := path_continuation_lift_congr (constant_path_continuation_lift (gaussNegativeCutPlaneBasepoint : ℂ) r M hr hM D hcenter' hbound hinitial) (by intro t ht; change ((Path.refl gaussNegativeCutPlaneBasepoint) (Set.projIcc 0 1 zero_le_one t) : ℂ) = _; rfl)
      let A := gaussNegativeCutPlaneCanonicalContinuationLift a b c gaussNegativeCutPlaneBasepoint
      change (gaussNegativeCutPlaneCanonicalContinuationLift a b c gaussNegativeCutPlaneBasepoint).value 1 = y
      calc
        (gaussNegativeCutPlaneCanonicalContinuationLift a b c gaussNegativeCutPlaneBasepoint).value 1 =
            A.value 1 := rfl
        _ = Q.value 1 := (subtype_path_lifts_endpoint_eq_of_simplyConnected gaussNegativeCutPlane_subset_regularPlane a b c (gaussNegativeCutPlaneCanonicalPath gaussNegativeCutPlaneBasepoint) (Path.refl gaussNegativeCutPlaneBasepoint) y A Q)
        _ = y := rfl
    obtain ⟨r₀, M₀, hr₀, _, hM₀, D₀, hD₀center, hD₀bound, hD₀series⟩ :=
      exists_gauss_ordinary_seed_disk_negative a b c hc
    obtain ⟨R, δ, hR, hδ, hδR, D, hDcenter, hlocal⟩ :=
      gaussNegativeCutPlaneContinuationState_locally_eq_picard a b c gaussNegativeCutPlaneBasepoint
    have hcenter : (gaussNegativeCutPlaneBasepoint : ℂ) = (-1 / 2 : ℂ) := by
      rfl
    have hD₀center' : D₀.center = (gaussNegativeCutPlaneBasepoint : ℂ) := by
      calc
        D₀.center = (-1 / 2 : ℂ) := hD₀center
        _ = (gaussNegativeCutPlaneBasepoint : ℂ) := hcenter.symm
    let y := ordinaryHypergeometricState a b c (-1 / 2 : ℂ)
    have hDmid : D.solution (gaussNegativeCutPlaneBasepoint : ℂ) = y := by
      calc
        D.solution (gaussNegativeCutPlaneBasepoint : ℂ) =
            gaussNegativeCutPlaneContinuationState a b c gaussNegativeCutPlaneBasepoint := by
              symm
              exact hlocal gaussNegativeCutPlaneBasepoint (by simp [dist_self, hδ])
        _ = y := (gaussNegativeCutPlaneContinuationState_basepoint_eq_seriesState)
    have hD₀mid : D₀.solution (gaussNegativeCutPlaneBasepoint : ℂ) = y := by
      calc
        D₀.solution (gaussNegativeCutPlaneBasepoint : ℂ) =
            ordinaryHypergeometricState a b c (-1 / 2 : ℂ) := by
              exact hD₀series (gaussNegativeCutPlaneBasepoint : ℂ) (by rw [hcenter]; exact Metric.mem_ball_self hr₀)
        _ = y := rfl
    let H := gaussSystemOperator a b c
    obtain ⟨rU, MU, hrU, hMU, hlocalU⟩ :=
      exists_uniform_holomorphic_disks_on_compact
        isCompact_singleton (fun z => z) continuousOn_id
        gaussRegularPlane gaussRegularPlane_isOpen H
        (gaussSystemOperator_differentiableOn a b c)
        (by rintro z rfl; exact (gaussNegativeCutPlane_subset_regularPlane gaussNegativeCutPlaneBasepoint.property))
    have hlocalUbase := hlocalU (gaussNegativeCutPlaneBasepoint : ℂ) (by simp)
    let ρ := min δ (min r₀ rU)
    have hρ := lt_min hδ (lt_min hr₀ hrU)
    have hρδ : ρ ≤ δ := min_le_left _ _
    have hballD : Metric.ball (gaussNegativeCutPlaneBasepoint : ℂ) ρ ⊆ Metric.ball D.center R := by
      intro z hz
      rw [Metric.mem_ball] at hz ⊢
      rw [hDcenter]
      exact lt_of_lt_of_le hz (by linarith [hρδ, hδR])
    have hballD₀ : Metric.ball (gaussNegativeCutPlaneBasepoint : ℂ) ρ ⊆
        Metric.ball D₀.center r₀ := by
      intro z hz
      rw [Metric.mem_ball] at hz ⊢
      rw [hD₀center']
      exact lt_of_lt_of_le hz (le_trans (min_le_right _ _) (min_le_left _ _))
    obtain ⟨ε, hε, hεball⟩ := Metric.mem_nhds_iff.mp
      (gaussNegativeCutPlane_isOpen.mem_nhds gaussNegativeCutPlaneBasepoint.property)
    have hσρ : (min ρ ε) ≤ ρ := min_le_left _ _
    filter_upwards [Metric.ball_mem_nhds (gaussNegativeCutPlaneBasepoint : ℂ) (lt_min hρ hε)]
      with z hz
    have hzcut : z ∈ gaussNegativeCutPlane :=
      hεball (Metric.ball_subset_ball (min_le_right _ _) hz)
    let w : gaussNegativeCutPlane := ⟨z, hzcut⟩
    have hzρ : z ∈ Metric.ball (gaussNegativeCutPlaneBasepoint : ℂ) ρ :=
      Metric.ball_subset_ball hσρ hz
    dsimp [gaussNegativeCutPlaneScalarState]
    rw [dite_eq_left hzcut]
    calc
      (gaussNegativeCutPlaneContinuationState a b c w).1 = (D.solution z).1 :=
        congrArg Prod.fst (hlocal w (by exact lt_of_lt_of_le (Metric.mem_ball.mp hz) (le_trans hσρ hρδ)))
      _ = (D₀.solution z).1 := congrArg Prod.fst ((show ∀ z ∈ Metric.ball (gaussNegativeCutPlaneBasepoint : ℂ) ρ, D.solution z = D₀.solution z by intro z hz; exact holomorphic_linear_system_solution_unique_of_eq_at (gaussNegativeCutPlaneBasepoint : ℂ) ρ MU H hMU (show ∀ z ∈ Metric.ball (gaussNegativeCutPlaneBasepoint : ℂ) ρ, ‖H z‖ ≤ MU by intro z hz; exact hlocalUbase.2 z (Metric.ball_subset_ball (le_trans (min_le_right _ _) (min_le_right _ _)) hz)) (fun u hu => D.derivative u (hballD hu)) (fun u hu => D₀.derivative u (hballD₀ hu)) (Metric.mem_ball_self hρ) hz (hDmid.trans hD₀mid.symm)) z hzρ)
      _ = (ordinaryHypergeometricState a b c z).1 := congrArg Prod.fst (hD₀series z (by simpa [hD₀center] using hballD₀ hzρ))
      _ = ordinaryHypergeometric a b c z := rfl
  have hbaseBall : (gaussNegativeCutPlaneBasepoint : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    change dist (-1 / 2 : ℂ) 0 < 1
    norm_num [dist_eq_norm]
  have hbaseV : (gaussNegativeCutPlaneBasepoint : ℂ) ∈ (gaussNegativeCutPlane ∩ Metric.ball (0 : ℂ) 1) :=
    ⟨gaussNegativeCutPlaneBasepoint.property, hbaseBall⟩
  exact (AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (fun w hw => ((gaussNegativeCutPlaneScalarState_differentiableOn a b c).analyticOnNhd gaussNegativeCutPlane_isOpen) w hw.1) (fun w hw => (ordinaryHypergeometric_analyticOnNhd_unitDisk a b c hc) w hw.2) (((gaussNegativeCutPlane_starConvex.inter ((convex_ball (0 : ℂ) 1).starConvex hbaseBall)).isPathConnected hbaseV).isConnected.isPreconnected) hbaseV (gaussNegativeCutPlaneScalarState_eq_ordinary_eventually)) ⟨hz, (by simpa [Metric.mem_ball, dist_zero_right] using hznorm)⟩

end DOZZ.Proofs
