module

public import RequestProject.LocalConformalBoundaryGeometry
public import RequestProject.LocalConformalArcReparam
public import Mathlib.Analysis.Complex.Angle
public import RequestProject.GreenWinding
public import RequestProject.CirclePullback

/-! The conformal trace has winding number one, and arclength preserves its signed area. -/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped ComplexConjugate Topology Real

/-- Pulling back the logarithmic derivative evaluates the winding number. -/
private theorem trace_windingNumber_eq {F : ℂ → ℂ} (coords : ConformalDiskCoordinates F) (w : ℂ) :
    windingNumber (physicalCircleTrace F) w = (2 * π * Complex.I)⁻¹ *
      ∮ z in C(0, 1), deriv F z / (F z - w) := by
  rw [windingNumber]
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  dsimp 
  rw [coords.trace_deriv, deriv_circleMap]
  change deriv F (circleMap 0 1 t) * (circleMap 0 1 t * Complex.I) / (F (circleMap 0 1 t) - w) = _
  simp  [div_eq_mul_inv]
  ring

theorem localConformal_circleTrace_signedArea {F : ℂ → ℂ} (coords : ConformalDiskCoordinates F) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), signedAreaDensity (physicalCircleTrace F) θ) =
      2 * (volume (F '' ball (0 : ℂ) 1)).toReal := by
  obtain ⟨K, hK⟩ := exists_periodic_C1_density_lipschitz _ coords.trace_contDiff (physicalCircleTrace_periodic F)
  have hF := coords.holomorphic_collar.mono (closedBall_subset_ball coords.one_lt_radius)
  have hd := (coords.holomorphic_collar.deriv isOpen_ball).mono (closedBall_subset_ball coords.one_lt_radius)
  have him := localConformal_circleTrace_image_frontier coords.one_lt_radius F coords.smooth
    coords.injOn_closed coords.lipschitz.1.1
  have h_in : ∀ w ∈ F '' ball 0 1, windingNumber (physicalCircleTrace F) w = 1 := by
    rintro _ ⟨z, hz, rfl⟩
    rw [trace_windingNumber_eq coords, circle_pullback_pole hz hF coords.injOn_closed
      (coords.deriv_ne_zero_closed (ball_subset_closedBall hz)) hd,
      div_self (coords.deriv_ne_zero_closed (ball_subset_closedBall hz)), mul_one,
      inv_mul_cancel₀ (by simp )]
  have h_out : ∀ w ∉ closure (F '' ball 0 1), windingNumber (physicalCircleTrace F) w = 0 := by
    intro w hw
    rw [← localConformal_closedDisk_image_eq_closure coords.one_lt_radius F coords.smooth] at hw
    have h : DifferentiableOn ℂ (fun z => deriv F z / (F z - w)) (closedBall 0 1) :=
      hd.div (hF.sub_const w) (fun z hz => sub_ne_zero.mpr
      (fun he => hw ⟨z, hz, he⟩))
    rw [trace_windingNumber_eq coords,
      (DiffContOnCl.mk_ball (h.mono ball_subset_closedBall) h.continuousOn).circleIntegral_eq_zero zero_le_one,
      mul_zero]
  simpa using integral_signedAreaDensity_of_winding coords.lipschitz.1.1 coords.bounded hK him 1
    (fun w hw => by simpa using h_in w hw) h_out

/-- The exact normalized arclength map preserves the actual signed area. -/
theorem normalizedArcCurve_signedArea {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ)
    (hper : Function.Periodic γ (2 * Real.pi)) (hnz : ∀ θ, deriv γ θ ≠ 0) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), signedAreaDensity (normalizedArcCurve hγ hper hnz) θ) =
      ∫ θ in (0 : ℝ)..(2 * Real.pi), signedAreaDensity γ θ := by
  obtain ⟨c, hτ, _, _⟩ := exists_isC1TraceReparam_normalizedArc hγ hper hnz
  obtain ⟨K, hK⟩ := hτ.lipschitz
  let e := normalizedArcOrderIso hγ hper hnz
  have he : LipschitzWith K e := hK
  have hcomp : normalizedArcCurve hγ hper hnz ∘ e = γ :=
    funext fun θ => (normalizedArcCurve_factorization hγ hper hnz θ).symm
  have hchain := ae_deriv_comp (normalizedArcCurve_lipschitz hγ hper hnz) e.monotone he
  rw [hcomp] at hchain
  have hcv := integral_comp_orderIso he (normalizedArcOrderIso_zero hγ hper hnz)
    (normalizedArcOrderIso_endpoint hγ hper hnz)
    (signedAreaDensity (normalizedArcCurve hγ hper hnz))
  rw [hcv]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hchain] with θ hθ _
  have hpoint : normalizedArcCurve hγ hper hnz (e θ) = γ θ := congrFun hcomp θ
  simp only [signedAreaDensity]
  rw [hpoint, hθ, mul_left_comm, Complex.im_ofReal_mul]

/-- The constructed exact arclength curve is now a genuine positively
oriented physical boundary parameter, with all six fields proved. -/
theorem localConformal_normalizedArcCurve_isBoundaryParam {F : ℂ → ℂ} (coords : ConformalDiskCoordinates F) :
    IsBoundaryParam (F '' ball (0 : ℂ) 1)
      (normalizedArcCurve coords.trace_contDiff (physicalCircleTrace_periodic F) coords.trace_deriv_ne_zero) := by
  let hγ := coords.trace_contDiff
  let hp := physicalCircleTrace_periodic F
  let hv := coords.trace_deriv_ne_zero
  have hinj := coords.injOn_closed
  have him := localConformal_circleTrace_image_frontier coords.one_lt_radius F coords.smooth hinj coords.lipschitz.1.1
  refine
    { lipschitz := ⟨_, normalizedArcCurve_lipschitz hγ hp hv⟩
      periodic := normalizedArcCurve_periodic hγ hp hv
      injOn := normalizedArcCurve_injOn hγ hp hv
        (physicalCircleTrace_injOn_of_closedDisk_inj F hinj)
      image := normalizedArcCurve_image_frontier hγ hp hv him
      const_speed := ⟨arcLen (physicalCircleTrace F) (2 * Real.pi) / (2 * Real.pi),
        div_pos (arcLen_period_pos_of_regular hγ hv) Real.two_pi_pos,
        Filter.Eventually.of_forall (normalizedArcCurve_speed hγ hp hv)⟩
      area := ?_ }
  exact (normalizedArcCurve_signedArea hγ hp hv).trans
    (localConformal_circleTrace_signedArea coords)

end PolyaNeumann

end
