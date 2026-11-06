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
section
variable (a b c : ℂ)
section
variable (hc : ∀ n : ℕ, c ≠ -(n : ℂ))
include hc

/-- The selected continuation at `-1/2` has its prescribed ordinary-series initial value. -/
theorem gaussNegativeCutPlaneContinuationState_basepoint_eq_seriesState
    :
    gaussNegativeCutPlaneContinuationState a b c gaussNegativeCutPlaneBasepoint =
      ordinaryHypergeometricState a b c (-1 / 2 : ℂ) := by
  obtain ⟨r, M, hr, _, hM, D, hcenter, hbound, hseries⟩ :=
    exists_gauss_ordinary_seed_disk_negative a b c hc
  let y := ordinaryHypergeometricState a b c (-1 / 2)
  have hcenter' : D.center = gaussNegativeCutPlaneBasepoint := by
    assumption
  have hinitial : D.initial = y := by
    calc
      D.initial = D.solution D.center := D.solution_center.symm
      _ = D.solution gaussNegativeCutPlaneBasepoint := by simp_all
      _ = y := hseries _ (Metric.mem_ball_self hr)
  let Q₀ := constant_path_continuation_lift
    gaussNegativeCutPlaneBasepoint r M hr hM D hcenter' hbound hinitial
  have hrefl : ∀ t ∈ Icc 0 1,
      subtypePathFunction (Path.refl gaussNegativeCutPlaneBasepoint) t =
        gaussNegativeCutPlaneBasepoint := by
    tauto
  let Q := path_continuation_lift_congr Q₀ hrefl
  let A := gaussNegativeCutPlaneCanonicalContinuationLift a b c gaussNegativeCutPlaneBasepoint
  exact subtype_path_lifts_endpoint_eq_of_simplyConnected
    gaussNegativeCutPlane_subset_regularPlane a b c
    (gaussNegativeCutPlaneCanonicalPath gaussNegativeCutPlaneBasepoint)
    (Path.refl gaussNegativeCutPlaneBasepoint) y A Q

/-- Near `-1/2`, the negative-cut endpoint's scalar component is the ordinary Gauss series. -/
theorem gaussNegativeCutPlaneScalarState_eq_ordinary_eventually
    :
    gaussNegativeCutPlaneScalarState a b c =ᶠ[𝓝 (gaussNegativeCutPlaneBasepoint : ℂ)]
      ordinaryHypergeometric a b c := by
  obtain ⟨r₀, M₀, hr₀, _, hM₀, D₀, hD₀center, hD₀bound, hD₀series⟩ :=
    exists_gauss_ordinary_seed_disk_negative a b c hc
  obtain ⟨R, δ, hR, hδ, hδR, D, hDcenter, hlocal⟩ :=
    gaussNegativeCutPlaneContinuationState_locally_eq_picard a b c gaussNegativeCutPlaneBasepoint
  have hcenter : (gaussNegativeCutPlaneBasepoint : ℂ) = (-1 / 2 : ℂ) := by
    rfl
  have hD₀center' : D₀.center = (gaussNegativeCutPlaneBasepoint : ℂ) := by
    assumption
  let y := ordinaryHypergeometricState a b c (-1 / 2 : ℂ)
  have hstateMid :
      gaussNegativeCutPlaneContinuationState a b c gaussNegativeCutPlaneBasepoint = y := by
    exact gaussNegativeCutPlaneContinuationState_basepoint_eq_seriesState a b c hc
  have hDmid : D.solution (gaussNegativeCutPlaneBasepoint : ℂ) = y := by
    simp_all
  have hD₀mid : D₀.solution (gaussNegativeCutPlaneBasepoint : ℂ) = y := by
    aesop
  let H := gaussSystemOperator a b c
  have hbaseRegular : (gaussNegativeCutPlaneBasepoint : ℂ) ∈ gaussRegularPlane :=
    gaussNegativeCutPlane_subset_regularPlane gaussNegativeCutPlaneBasepoint.property
  obtain ⟨rU, MU, hrU, hMU, hlocalU⟩ :=
    exists_uniform_holomorphic_disks_on_compact
      isCompact_singleton (fun z => z) continuousOn_id
      gaussRegularPlane gaussRegularPlane_isOpen H
      (gaussSystemOperator_differentiableOn a b c)
      (by simpa)
  have hlocalUbase := hlocalU (gaussNegativeCutPlaneBasepoint : ℂ) (by simp)
  let ρ := min δ (min r₀ rU)
  have hρ : 0 < ρ := by positivity
  have hρδ : ρ ≤ δ := min_le_left ..
  have hρr₀ : ρ ≤ r₀ := by grind
  have hρrU : ρ ≤ rU := by grind
  have hρR : ρ ≤ R := by linarith
  have hballD : Metric.ball (gaussNegativeCutPlaneBasepoint : ℂ) ρ ⊆ Metric.ball D.center R := by
    intro z hz
    rw [hDcenter]
    exact lt_of_lt_of_le hz hρR
  have hballD₀ : Metric.ball (gaussNegativeCutPlaneBasepoint : ℂ) ρ ⊆
      Metric.ball D₀.center r₀ := by
    intro z hz
    rw [hD₀center']
    exact lt_of_lt_of_le hz hρr₀
  have hboundρ : ∀ z ∈ Metric.ball (gaussNegativeCutPlaneBasepoint : ℂ) ρ,
      ‖H z‖ ≤ MU := by
    intro z hz
    exact hlocalUbase.2 z (Metric.ball_subset_ball hρrU hz)
  have hDunique : ∀ z ∈ Metric.ball (gaussNegativeCutPlaneBasepoint : ℂ) ρ,
      D.solution z = D₀.solution z := by
    intro z hz
    exact holomorphic_linear_system_solution_unique_of_eq_at
      (gaussNegativeCutPlaneBasepoint : ℂ) ρ MU H hMU hboundρ
      (fun u hu => D.derivative u (hballD hu))
      (fun u hu => D₀.derivative u (hballD₀ hu))
      (Metric.mem_ball_self hρ) hz (hDmid.trans hD₀mid.symm)
  obtain ⟨ε, hε, hεball⟩ := Metric.mem_nhds_iff.mp
    (gaussNegativeCutPlane_isOpen.mem_nhds gaussNegativeCutPlaneBasepoint.property)
  let σ := min ρ ε
  have hσ : 0 < σ := lt_min hρ hε
  have hσρ : σ ≤ ρ := min_le_left ..
  have hσε : σ ≤ ε := min_le_right ..
  have hnear : gaussNegativeCutPlaneScalarState a b c =ᶠ[𝓝 (gaussNegativeCutPlaneBasepoint : ℂ)]
      ordinaryHypergeometric a b c := by
    filter_upwards [Metric.ball_mem_nhds (gaussNegativeCutPlaneBasepoint : ℂ) hσ]
      with z hz
    have hzcut : z ∈ gaussNegativeCutPlane :=
      hεball (Metric.ball_subset_ball hσε hz)
    let w : gaussNegativeCutPlane := ⟨z, hzcut⟩
    have hzδ : dist (w : ℂ) (gaussNegativeCutPlaneBasepoint : ℂ) < δ := by
      exact lt_of_lt_of_le (Metric.mem_ball.mp hz) (le_trans hσρ hρδ)
    have hzρ : z ∈ Metric.ball (gaussNegativeCutPlaneBasepoint : ℂ) ρ :=
      Metric.ball_subset_ball hσρ hz
    have hzseed : z ∈ Metric.ball (-1 / 2 : ℂ) r₀ := by
      simpa [hD₀center] using hballD₀ hzρ
    dsimp [gaussNegativeCutPlaneScalarState]
    rw [dite_eq_left hzcut]
    calc
      (gaussNegativeCutPlaneContinuationState a b c w).1 = (D.solution z).1 :=
        congrArg Prod.fst (hlocal w hzδ)
      _ = (D₀.solution z).1 := congrArg Prod.fst (hDunique z hzρ)
      _ = (ordinaryHypergeometricState a b c z).1 := congrArg Prod.fst (hD₀series z hzseed)
      _ = ordinaryHypergeometric a b c z := rfl
  exact hnear

/-- On the negative cut plane, the endpoint continuation recovers the ordinary series throughout the unit
disk. -/
theorem gaussNegativeCutPlaneScalarState_eq_ordinary_on_unitDisk
    {z : ℂ} (hz : z ∈ gaussNegativeCutPlane) (hznorm : ‖z‖ < 1) :
    gaussNegativeCutPlaneScalarState a b c z = ordinaryHypergeometric a b c z := by
  let V := gaussNegativeCutPlane ∩ Metric.ball 0 1
  have hbaseBall : (gaussNegativeCutPlaneBasepoint : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    change dist (-1 / 2) 0 < 1
    norm_num
  have hballStar : StarConvex ℝ (gaussNegativeCutPlaneBasepoint : ℂ)
      (Metric.ball (0 : ℂ) 1) :=
    (convex_ball (0 : ℂ) 1).starConvex hbaseBall
  have hVstar :=
    gaussNegativeCutPlane_starConvex.inter hballStar
  have hbaseV : (gaussNegativeCutPlaneBasepoint : ℂ) ∈ V :=
    by aesop
  have hVpre :=
    (hVstar.isPathConnected hbaseV).isConnected.isPreconnected
  have hFanalytic :=
    (gaussNegativeCutPlaneScalarState_differentiableOn a b c).analyticOnNhd gaussNegativeCutPlane_isOpen
  have hseriesAnalytic :=
    ordinaryHypergeometric_analyticOnNhd_unitDisk a b c hc
  have hFanalyticV : AnalyticOnNhd ℂ (gaussNegativeCutPlaneScalarState a b c) V :=
    fun w hw => hFanalytic w hw.1
  have hseriesAnalyticV : AnalyticOnNhd ℂ (ordinaryHypergeometric a b c) V :=
    fun w hw => hseriesAnalytic w hw.2
  have hidentity :=
    AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      hFanalyticV hseriesAnalyticV hVpre hbaseV
      (gaussNegativeCutPlaneScalarState_eq_ordinary_eventually a b c hc)
  aesop

end

end

end DOZZ.Proofs
