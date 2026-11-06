module

public import RequestProject.SmoothBoundaryParamUniqueness
public import RequestProject.LocalConformalAreaOrientation
public import RequestProject.LocalConformalRotation

/-!
# Actual supplied coordinates synchronized with the original boundary

The canonical normalized-arclength curve is proved C¹ from its actual inverse
derivative.  Its actual physical boundary predicate and the proved uniqueness
of constant-speed boundary parameters then select a genuine circle rotation.
Rebasing the genuine arclength lift synchronizes the rotated supplied map with
the original physical boundary parameter, including both fixed endpoints.

Every rotated coordinate property follows from the original supplied map and
its actual smooth inverse.  This constructs no initial conformal map.
-/

@[expose] public section


noncomputable section

namespace PolyaNeumann

open Set Metric MeasureTheory Filter
open scoped Topology Real ContDiff

variable {Γ : ℝ → ℂ}

/-- The canonical arc curve has a genuinely nonzero velocity everywhere. -/
theorem normalizedArcCurve_deriv_ne_zero 
    (hΓ : ContDiff ℝ 1 Γ) hper
    hnz (t : ℝ) :
    deriv (normalizedArcCurve hΓ hper hnz) t ≠ 0 := by
  apply norm_pos_iff.mp
  rw [normalizedArcCurve_speed hΓ hper hnz]
  exact div_pos (arcLen_period_pos_of_regular hΓ hnz) Real.two_pi_pos

/-- The actual canonical arc parameter, not merely an existential reference,
is a physical boundary parameter.  Its identification with the proved reference
uses surjectivity of the actual normalized-arclength map. -/
theorem exists_normalizedArc_origin_sync {Ω : Set ℂ} 
    (hb : Bornology.IsBounded Ω) (hΩ : IsDomain Ω)
    (hΓ : ContDiff ℝ 1 Γ) hper
    hnz
    (hβ : IsBoundaryParam Ω (normalizedArcCurve hΓ hper hnz))
    (hγ : IsBoundaryParam Ω γ) :
    ∃ φ ∈ Icc 0 (2 * Real.pi), ∃ c : ℝ,
      IsC1TraceReparam (localConformalRotateTraceReparam (normalizedArcReparam Γ) φ) c ∧
      (∀ θ : ℝ,
        localConformalRotateTraceReparam (normalizedArcReparam Γ) φ (θ + 2 * Real.pi) =
          localConformalRotateTraceReparam (normalizedArcReparam Γ) φ θ + 2 * Real.pi) ∧
      (∀ θ : ℝ, Γ (θ + φ) =
        γ (localConformalRotateTraceReparam (normalizedArcReparam Γ) φ θ)) := by
  obtain ⟨t, ht, hshift⟩ := exists_boundaryParam_shift_of_bounded_domain hb hΩ hβ
    (by
      let σ := (normalizedArcOrderIso hΓ hper hnz).symm
      have hv :=
        hΓ.continuous_deriv_one.comp ((normalizedArcOrderIso hΓ hper hnz).symm.continuous)
      have hdne t : 2 * Real.pi / arcLen Γ (2 * Real.pi) * ‖deriv Γ (σ t)‖ ≠ 0 :=
        (mul_pos (div_pos Real.two_pi_pos (arcLen_period_pos_of_regular hΓ hnz)) (norm_pos_iff.mpr (hnz (σ t)))).ne'
      refine contDiff_one_iff_deriv.mpr ⟨?_, ?_⟩
      · exact fun t => (normalizedArcCurve_hasDerivAt hΓ hper hnz t).differentiableAt
      · rw [funext (fun t => (normalizedArcCurve_hasDerivAt hΓ hper hnz t).deriv)]
        exact ((continuous_const.mul hv.norm).inv₀ hdne).smul hv)
    (normalizedArcCurve_deriv_ne_zero hΓ hper hnz) hγ
  let φ : ℝ := (normalizedArcOrderIso hΓ hper hnz).symm t
  have hφval : normalizedArcReparam Γ φ = t :=
    (normalizedArcOrderIso hΓ hper hnz).apply_symm_apply t
  obtain ⟨c, hτ, _, hτper⟩ := exists_isC1TraceReparam_normalizedArc hΓ hper hnz
  refine ⟨φ, (by
    constructor
    · simpa using
        (normalizedArcOrderIso hΓ hper hnz).symm.monotone ht.1
    · simpa using
        (normalizedArcOrderIso hΓ hper hnz).symm.monotone ht.2), c, localConformalRotateTraceReparam_isC1 hτ hτper φ,
    localConformalRotateTraceReparam_add_period hτper φ, ?_⟩
  intro θ
  calc
    _ = _ :=
      normalizedArcCurve_factorization hΓ hper hnz (θ + φ)
    _ = _ := by
      congr 1
      simp [localConformalRotateTraceReparam, hφval]
    _ = _ :=
      (hshift _).symm

/-- Closed-disk injectivity follows from the genuine supplied inverse, so no
additional boundary injectivity premise is needed by synchronization. -/
local notation "Φ1" => closedBall 0 1

theorem localConformal_closedDisk_inj_of_supplied_inverse
    (F : ℂ → ℂ) (e : OpenPartialHomeomorph ℂ ℂ) (he : e = F)
    (hsource : Φ1 ⊆ e.source) :
    InjOn F (Φ1) := by
  intro z hz w hw hzw
  have h := congrArg e.symm (show e z = e w by simpa [he] using hzw)
  change e.symm (e z) = e.symm (e w) at h
  rw [e.left_inv (hsource hz), e.left_inv (hsource hw)] at h
  exact h

/-- Genuine C¹ regularity and periodicity give a finite global speed bound,
and hence a genuine Lipschitz constant for the actual circle trace. -/
theorem exists_regularPeriodicCurve_lipschitz 
    (hΓ : ContDiff ℝ 1 Γ) (hper : Function.Periodic Γ (2 * Real.pi))
    (hnz : ∀ θ, deriv Γ θ ≠ 0) : ∃ L : NNReal, LipschitzWith L Γ := by
  obtain ⟨m, M, hm, hM, hbounds⟩ := exists_regular_periodic_speed_bounds hΓ hper hnz
  refine ⟨Real.toNNReal M, ?_⟩
  apply lipschitzWith_of_nnnorm_deriv_le hΓ.differentiable_one
  intro θ
  apply NNReal.coe_le_coe.mp
  change ‖deriv Γ θ‖ ≤ _
  rw [Real.coe_toNNReal _ hM]
  exact (hbounds θ).2

/-- The complete actual supplied-coordinate package at the original physical
boundary origin.  The displayed maps are genuine rotations of the original
map and its genuine inverse; the original constants `C` and `K` are retained.
This theorem selects no nonzero transport cut. -/
local notation "Φ0" => ball 0 1

theorem exists_localConformal_original_boundary_coordinates
    {R C K : ℝ} (hR : 1 < R) F
    (hFs : ContDiffOn ℝ ∞ F (ball 0 R))
    (hb : Bornology.IsBounded (F '' Φ0))
    (hL : IsLipschitzDomain (F '' Φ0))
    (hhol : DifferentiableOn ℂ F (Φ0))
    (hC : ∀ z ∈ Φ0, 1 ≤ C * ‖deriv F z‖ ^ 2)
    (hK : ∀ z ∈ ball (0 : ℂ) 1, ‖fderiv ℝ F z 1‖ ≤ K)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : e = F)
    (hsource : closedBall (0 : ℂ) 1 ⊆ e.source)
    (hes : ContDiffOn ℝ ∞ e.symm e.target)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam (F '' Φ0) γ) :
    ∃ φ ∈ Icc 0 (2 * Real.pi), ∃ c : ℝ, ∃ L : NNReal,
      localConformalRotate F φ '' Φ0 = F '' Φ0 ∧
      localConformalRotate F φ '' Φ1 = F '' Φ1 ∧
      ContDiffOn ℝ ∞ (localConformalRotate F φ) (ball 0 R) ∧
      Bornology.IsBounded (localConformalRotate F φ '' Φ0) ∧
      IsLipschitzDomain (localConformalRotate F φ '' Φ0) ∧
      DifferentiableOn ℂ (localConformalRotate F φ) (Φ0) ∧
      InjOn (localConformalRotate F φ) (Φ1) ∧
      (∀ z ∈ Φ0, 1 ≤ C * ‖deriv (localConformalRotate F φ) z‖ ^ 2) ∧
      (∀ z ∈ Φ0, ‖fderiv ℝ (localConformalRotate F φ) z 1‖ ≤ K) ∧
      (localConformalRotatePartialHomeomorph e φ : ℂ → ℂ) = localConformalRotate F φ ∧
      Φ1 ⊆ (localConformalRotatePartialHomeomorph e φ).source ∧
      ContDiffOn ℝ ∞ (localConformalRotatePartialHomeomorph e φ).symm
        (localConformalRotatePartialHomeomorph e φ).target ∧
      IsBoundaryParam (localConformalRotate F φ '' Φ0) γ ∧
      IsC1TraceReparam
        (localConformalRotateTraceReparam (normalizedArcReparam (physicalCircleTrace F)) φ) c ∧
      (∀ θ : ℝ,
        localConformalRotateTraceReparam (normalizedArcReparam (physicalCircleTrace F)) φ
            (θ + 2 * Real.pi) =
          localConformalRotateTraceReparam (normalizedArcReparam (physicalCircleTrace F)) φ θ +
            2 * Real.pi) ∧
      (∀ θ : ℝ, localConformalRotate F φ (circleMap 0 1 θ) =
        γ (localConformalRotateTraceReparam (normalizedArcReparam (physicalCircleTrace F)) φ θ)) ∧
      LipschitzWith L (physicalCircleTrace (localConformalRotate F φ)) ∧
      localConformalRotate F φ 1 = γ 0 := by
  obtain ⟨φ, hφ, c, hτ, hτper, hcoord⟩ : ∃ φ ∈ Icc 0 (2 * Real.pi), ∃ c : ℝ, IsC1TraceReparam (localConformalRotateTraceReparam (normalizedArcReparam (physicalCircleTrace F)) φ) c ∧ (∀ θ : ℝ, localConformalRotateTraceReparam (normalizedArcReparam (physicalCircleTrace F)) φ (θ + 2 * Real.pi) = localConformalRotateTraceReparam (normalizedArcReparam (physicalCircleTrace F)) φ θ + 2 * Real.pi) ∧ (∀ θ : ℝ, localConformalRotate F φ (circleMap 0 1 θ) = γ (localConformalRotateTraceReparam (normalizedArcReparam (physicalCircleTrace F)) φ θ)) := by
    have hnz : ∀ z ∈ sphere 0 1, fderiv ℝ F z 1 ≠ 0 :=
      fun z hz => (localConformalRotation_closedDifferential_ne_zero_of_inverse hR F hFs e he hsource hes) z (sphere_subset_closedBall hz)
    have h_inl : let hΓ : ContDiff ℝ 1 (physicalCircleTrace F) :=
      contDiff_physicalCircleTrace_of_neighborhood hR F (hFs.of_le (WithTop.coe_le_coe.mpr le_top))
      let hp := physicalCircleTrace_periodic F
      let hv := localConformal_circleTrace_deriv_ne_zero hR F hFs hhol hnz
      IsBoundaryParam (F '' Φ0) (normalizedArcCurve hΓ hp hv) := by
      dsimp only
      let hΓ :=
      contDiff_physicalCircleTrace_of_neighborhood hR F (hFs.of_le (WithTop.coe_le_coe.mpr le_top))
      let hp := physicalCircleTrace_periodic F
      let hv := localConformal_circleTrace_deriv_ne_zero hR F hFs hhol hnz
      obtain ⟨β, c, hβ, _, hfactor⟩ :=
      exists_localConformal_isBoundaryParam hR F hFs hhol (localConformal_closedDisk_inj_of_supplied_inverse F e he hsource) hnz hL
      rw [show β = normalizedArcCurve hΓ hp hv by
      funext t
      obtain ⟨θ, hθ⟩ := normalizedArcReparam_surjective hΓ hp hv t
      calc
      _ = _ := by rw [hθ]
      _ = _ := (hfactor θ).symm
      _ = _ :=
      normalizedArcCurve_factorization hΓ hp hv θ
      _ = _ := by rw [hθ]] at hβ
      exact hβ
    obtain ⟨φ, hφ, c, hτ, hτper, hcoord⟩ :=
      exists_normalizedArc_origin_sync hb hL.1 (contDiff_physicalCircleTrace_of_neighborhood hR F (hFs.of_le (WithTop.coe_le_coe.mpr le_top))) (physicalCircleTrace_periodic F) (localConformal_circleTrace_deriv_ne_zero hR F hFs hhol hnz) h_inl hγ
    refine ⟨φ, hφ, c, hτ, hτper, ?_⟩
    intro θ
    calc
      _ = _ := rfl
      _ = _ := physicalCircleTrace_localConformalRotate F φ θ
      _ = _ := hcoord θ
  obtain ⟨L, hΓLip⟩ := exists_regularPeriodicCurve_lipschitz (contDiff_physicalCircleTrace_of_neighborhood hR F (hFs.of_le (WithTop.coe_le_coe.mpr le_top))) (physicalCircleTrace_periodic F) (localConformal_circleTrace_deriv_ne_zero hR F hFs hhol (fun z hz => (localConformalRotation_closedDifferential_ne_zero_of_inverse hR F hFs e he hsource hes) z (sphere_subset_closedBall hz)))
  have himage := localConformalRotate_image_ball F φ 1
  refine ⟨φ, hφ, c, L, himage, localConformalRotate_image_closedBall F φ 1,
    localConformalRotate_contDiffOn hFs φ, (by
      rw [himage]
      exact hb), (by
      rw [himage]
      exact hL),
    localConformalRotate_holomorphic hhol φ,
    localConformalRotate_injOn_closedBall
      (localConformal_closedDisk_inj_of_supplied_inverse F e he hsource) φ,
    localConformalRotate_lower_deriv_bound hhol hC φ,
    localConformalRotate_upper_differential_bound hR F hFs hhol hK φ,
    localConformalRotatePartialHomeomorph_coe e he φ,
    localConformalRotatePartialHomeomorph_closedDisk_source e hsource φ,
    localConformalRotatePartialHomeomorph_smoothInverse e hes φ,
    (by
      rw [himage]
      exact hγ), hτ, hτper, hcoord,
    physicalCircleTrace_localConformalRotate_lipschitz hΓLip φ, ?_⟩
  simpa [show circleMap 0 1 0 = 1 by simp [circleMap], hτ.zero] using hcoord 0

end PolyaNeumann

end
