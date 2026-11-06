module

public import RequestProject.PlanarTypes

public import RequestProject.PlanarGeometry

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

public section

open scoped ContDiff



namespace PolyaNeumann

open Set Metric MeasureTheory Filter

section
variable {Γ : ComplexCurve} (hΓ : ContDiff ℝ 1 Γ) (hper : Function.Periodic Γ circlePeriod) (hnz : ∀ θ, deriv Γ θ ≠ 0)
include Γ hΓ hper hnz

/-- The canonical arc curve is genuinely C¹: its previously proved inverse
derivative is continuous because the original speed is continuous and nonzero. -/
theorem normalizedArcCurve_contDiff :
    ContDiff ℝ 1 (normalizedArcCurve hΓ hper hnz) := by
  let σ  := (normalizedArcOrderIso hΓ hper hnz).symm
  let a  := 2 * Real.pi / arcLen Γ circlePeriod
  have ha  := div_pos Real.two_pi_pos (arcLen_period_pos_of_regular hΓ hnz)
  have hσ  := (normalizedArcOrderIso hΓ hper hnz).symm.continuous
  have hv  :=
    hΓ.continuous_deriv_one.comp hσ
  have hd : Continuous (fun t : ℝ => a * ‖deriv Γ (σ t)‖) := continuous_const.mul hv.norm
  have hdne (t : ℝ)  :=
    (mul_pos ha (norm_pos_iff.mpr (hnz (σ t)))).ne'
  have hformula  :=
    funext (fun t => (normalizedArcCurve_hasDerivAt hΓ hper hnz t).deriv)
  refine contDiff_one_iff_deriv.mpr ⟨?_, ?_⟩
  · exact fun t => (normalizedArcCurve_hasDerivAt hΓ hper hnz t).differentiableAt
  · rw [hformula]
    exact (hd.inv₀ hdne).smul hv

/-- The canonical arc curve has a genuinely nonzero velocity everywhere. -/
theorem normalizedArcCurve_deriv_ne_zero t :
    deriv (normalizedArcCurve hΓ hper hnz) t ≠ 0 := by
  apply norm_pos_iff.mp
  rw [normalizedArcCurve_speed hΓ hper hnz]
  exact div_pos (arcLen_period_pos_of_regular hΓ hnz) Real.two_pi_pos

end


section
variable {R } (hR : 1 < R) (F : PlaneMap) (hFs : RealSmoothOnBall F R)

include R hR F hFs in
/-- The actual canonical arc parameter, not merely an existential reference,
is a physical boundary parameter.  Its identification with the proved reference
uses surjectivity of the actual normalized-arclength map. -/
theorem localConformal_normalizedArcCurve_isBoundaryParam
    hhol
    (hinj : InjOn F closedUnitDisk)
    hnz
    (hL : IsLipschitzDomain (F '' unitDisk)) :
    let hΓ : ContDiff ℝ 1 (physicalCircleTrace F) :=
      contDiff_physicalCircleTrace_of_neighborhood hR F (hFs.of_le (WithTop.coe_le_coe.mpr le_top))
    let hp := physicalCircleTrace_periodic F
    let hv := localConformal_circleTrace_deriv_ne_zero hR F hFs hhol hnz
    IsBoundaryParam (F '' unitDisk) (normalizedArcCurve hΓ hp hv) := by
  let hΓ  :=
    contDiff_physicalCircleTrace_of_neighborhood hR F (hFs.of_le (WithTop.coe_le_coe.mpr le_top))
  let hp := physicalCircleTrace_periodic F
  let hv := localConformal_circleTrace_deriv_ne_zero hR F hFs hhol hnz
  obtain ⟨β, c, hβ, _, hfactor⟩ :=
    exists_localConformal_isBoundaryParam hR F hFs hhol hinj hnz hL
  have heq : β = normalizedArcCurve hΓ hp hv := by
    funext t
    obtain ⟨θ, hθ⟩ := normalizedArcReparam_surjective hΓ hp hv t
    calc
      β t = β (normalizedArcReparam (physicalCircleTrace F) θ) := by rw [hθ]
      _ = physicalCircleTrace F θ := (hfactor θ).symm
      _ = normalizedArcCurve hΓ hp hv
          (normalizedArcReparam (physicalCircleTrace F) θ) :=
        normalizedArcCurve_factorization hΓ hp hv θ
      _ = normalizedArcCurve hΓ hp hv t := by rw [hθ]
  rw [heq] at hβ
  exact hβ

/-- Given the proved canonical physical arc parameter, select the actual
circle phase and the genuine endpoint-preserving C¹ arclength lift for any
original physical boundary parameter. -/
theorem exists_normalizedArc_origin_sync  
    (hb : Bornology.IsBounded Ω) (hΩ : IsDomain Ω)
    hΓ hper
    (hnz : ∀ θ, deriv Γ θ ≠ 0)
    (hβ : IsBoundaryParam Ω (normalizedArcCurve hΓ hper hnz))
    (hγ : IsBoundaryParam Ω γ) :
    ∃ φ ∈ boundaryInterval, ∃ c : ℝ,
      IsC1TraceReparam (localConformalRotateTraceReparam (normalizedArcReparam Γ) φ) c ∧
      (∀ θ : ℝ,
        localConformalRotateTraceReparam (normalizedArcReparam Γ) φ (θ + 2 * Real.pi) =
          localConformalRotateTraceReparam (normalizedArcReparam Γ) φ θ + 2 * Real.pi) ∧
      (∀ θ : ℝ, Γ (θ + φ) =
        γ (localConformalRotateTraceReparam (normalizedArcReparam Γ) φ θ)) := by
  obtain ⟨t, ht, hshift⟩ := exists_boundaryParam_shift_of_bounded_domain hb hΩ hβ
    (normalizedArcCurve_contDiff hΓ hper hnz)
    (normalizedArcCurve_deriv_ne_zero hΓ hper hnz) hγ
  let φ  := (normalizedArcOrderIso hΓ hper hnz).symm t
  have hφ : φ ∈ boundaryInterval := by
    constructor
    · simpa   using
        (normalizedArcOrderIso hΓ hper hnz).symm.monotone ht.1
    · simpa   using
        (normalizedArcOrderIso hΓ hper hnz).symm.monotone ht.2
  have hφval : normalizedArcReparam Γ φ = t :=
    (normalizedArcOrderIso hΓ hper hnz).apply_symm_apply t
  obtain ⟨c, hτ, _, hτper⟩ := exists_isC1TraceReparam_normalizedArc hΓ hper hnz
  refine ⟨φ, hφ, c, localConformalRotateTraceReparam_isC1 hτ hτper φ,
    localConformalRotateTraceReparam_add_period hτper φ, ?_⟩
  intro θ
  calc
    Γ (θ + φ) = normalizedArcCurve hΓ hper hnz (normalizedArcReparam Γ (θ + φ)) :=
      normalizedArcCurve_factorization hΓ hper hnz (θ + φ)
    _ = normalizedArcCurve hΓ hper hnz
        (localConformalRotateTraceReparam (normalizedArcReparam Γ) φ θ + t) := by
      simp_all [localConformalRotateTraceReparam]
    _ = γ (localConformalRotateTraceReparam (normalizedArcReparam Γ) φ θ) :=
      (hshift _).symm

/-- Closed-disk injectivity follows from the genuine supplied inverse, so no
additional boundary injectivity premise is needed by synchronization. -/
theorem localConformal_closedDisk_inj_of_supplied_inverse
    F (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : PlaneMap) = F)
    (hsource : closedUnitDisk ⊆ e.source) :
    InjOn F closedUnitDisk := by
  intro z hz w hw hzw
  have hzw' : e z = e w := by simpa  [he] using hzw
  have h := congrArg e.symm hzw'
  rw [e.left_inv (hsource hz), e.left_inv (hsource hw)] at h
  exact h

include R hR F hFs in
/-- Actual rotation of supplied coordinates synchronizes their genuine
circle trace with the original physical boundary parameter. -/
theorem exists_localConformal_boundaryParam_sync
    (hb : Bornology.IsBounded (F '' unitDisk))
    (hL : IsLipschitzDomain (F '' unitDisk))
    (hhol : DifferentiableOn ℂ F unitDisk)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : PlaneMap) = F)
    (hsource : closedUnitDisk ⊆ e.source)
    (hes : RealSmoothOn e.symm e.target)
     (hγ : IsBoundaryParam (F '' unitDisk) γ) :
    ∃ φ ∈ boundaryInterval, ∃ c : ℝ,
      IsC1TraceReparam
        (localConformalRotateTraceReparam (normalizedArcReparam (physicalCircleTrace F)) φ) c ∧
      (∀ θ : ℝ,
        localConformalRotateTraceReparam (normalizedArcReparam (physicalCircleTrace F)) φ
            (θ + 2 * Real.pi) =
          localConformalRotateTraceReparam (normalizedArcReparam (physicalCircleTrace F)) φ θ +
            2 * Real.pi) ∧
      (∀ θ : ℝ, localConformalRotate F φ (unitCircleMap θ) =
        γ (localConformalRotateTraceReparam (normalizedArcReparam (physicalCircleTrace F)) φ θ)) := by
  have hinj := localConformal_closedDisk_inj_of_supplied_inverse F e he hsource
  have hnzclosed := localConformalRotation_closedDifferential_ne_zero_of_inverse
    hR F hFs e he hsource hes
  have hnz  :=
    fun z hz => hnzclosed z (sphere_subset_closedBall hz)
  have hΓ  :=
    contDiff_physicalCircleTrace_of_neighborhood hR F (hFs.of_le (WithTop.coe_le_coe.mpr le_top))
  have hp := physicalCircleTrace_periodic F
  have hv := localConformal_circleTrace_deriv_ne_zero hR F hFs hhol hnz
  have hβ := localConformal_normalizedArcCurve_isBoundaryParam hR F hFs hhol hinj hnz hL
  obtain ⟨φ, hφ, c, hτ, hτper, hcoord⟩ :=
    exists_normalizedArc_origin_sync hb hL.1 hΓ hp hv hβ hγ
  refine ⟨φ, hφ, c, hτ, hτper, ?_⟩
  intro θ
  calc
    localConformalRotate F φ (unitCircleMap θ) =
        physicalCircleTrace (localConformalRotate F φ) θ := rfl
    _ = physicalCircleTrace F (θ + φ) := physicalCircleTrace_localConformalRotate F φ θ
    _ = _ := hcoord θ

end


/-- Genuine C¹ regularity and periodicity give a finite global speed bound,
and hence a genuine Lipschitz constant for the actual circle trace. -/
theorem exists_regularPeriodicCurve_lipschitz {Γ : ComplexCurve}
    (hΓ : ContDiff ℝ 1 Γ) (hper : Function.Periodic Γ circlePeriod)
    (hnz : ∀ θ, deriv Γ θ ≠ 0) : ∃ L : NNReal, LipschitzWith L Γ := by
  obtain ⟨m, M, hm, hM, hbounds⟩ := exists_regular_periodic_speed_bounds hΓ hper hnz
  refine ⟨Real.toNNReal M, ?_⟩
  apply lipschitzWith_of_nnnorm_deriv_le hΓ.differentiable_one
  intro θ
  apply NNReal.coe_le_coe.mp
  simp_all

/-- The complete actual supplied-coordinate package at the original physical
boundary origin.  The displayed maps are genuine rotations of the original
map and its genuine inverse; the original constants `C` and `K` are retained.
This theorem selects no nonzero transport cut. -/
theorem exists_localConformal_original_boundary_coordinates
     (hR : 1 < R) F
    (hFs : RealSmoothOnBall F R)
    (hb : Bornology.IsBounded (F '' unitDisk))
    (hL : IsLipschitzDomain (F '' unitDisk))
    (hhol : DifferentiableOn ℂ F unitDisk)
    (hC : DiskInverseJacobianBound F C)
    (hK : DiskDerivativeBound F K)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : PlaneMap) = F)
    (hsource : closedUnitDisk ⊆ e.source)
    (hes : RealSmoothOn e.symm e.target)
     (hγ : IsBoundaryParam (F '' unitDisk) γ) :
    ∃ φ ∈ boundaryInterval, ∃ c : ℝ, ∃ L : NNReal,
      (localConformalRotate F φ '' unitDisk = F '' unitDisk) ∧
      (localConformalRotate F φ '' closedUnitDisk = F '' closedUnitDisk) ∧
      RealSmoothOn (localConformalRotate F φ) (ball (0 : ℂ) R) ∧
      Bornology.IsBounded (localConformalRotate F φ '' unitDisk) ∧
      IsLipschitzDomain (localConformalRotate F φ '' unitDisk) ∧
      DifferentiableOn ℂ (localConformalRotate F φ) unitDisk ∧
      InjOn (localConformalRotate F φ) closedUnitDisk ∧
      (∀ z ∈ unitDisk, 1 ≤ C * ‖deriv (localConformalRotate F φ) z‖ ^ 2) ∧
      (∀ z ∈ unitDisk, ‖fderiv ℝ (localConformalRotate F φ) z 1‖ ≤ K) ∧
      ((localConformalRotatePartialHomeomorph e φ : PlaneMap) = localConformalRotate F φ) ∧
      (closedUnitDisk ⊆ (localConformalRotatePartialHomeomorph e φ).source) ∧
      RealSmoothOn (localConformalRotatePartialHomeomorph e φ).symm
        (localConformalRotatePartialHomeomorph e φ).target ∧
      IsBoundaryParam (localConformalRotate F φ '' unitDisk) γ ∧
      IsC1TraceReparam
        (localConformalRotateTraceReparam (normalizedArcReparam (physicalCircleTrace F)) φ) c ∧
      (∀ θ : ℝ,
        localConformalRotateTraceReparam (normalizedArcReparam (physicalCircleTrace F)) φ
            (θ + 2 * Real.pi) =
          localConformalRotateTraceReparam (normalizedArcReparam (physicalCircleTrace F)) φ θ +
            2 * Real.pi) ∧
      (∀ θ : ℝ, localConformalRotate F φ (unitCircleMap θ) =
        γ (localConformalRotateTraceReparam (normalizedArcReparam (physicalCircleTrace F)) φ θ)) ∧
      LipschitzWith L (physicalCircleTrace (localConformalRotate F φ)) ∧
      localConformalRotate F φ 1 = γ 0 := by
  obtain ⟨φ, hφ, c, hτ, hτper, hcoord⟩ :=
    exists_localConformal_boundaryParam_sync hR F hFs hb hL hhol e he hsource hes hγ
  have hnzclosed := localConformalRotation_closedDifferential_ne_zero_of_inverse
    hR F hFs e he hsource hes
  have hnz  :=
    fun z hz => hnzclosed z (sphere_subset_closedBall hz)
  have hΓ  :=
    contDiff_physicalCircleTrace_of_neighborhood hR F (hFs.of_le (WithTop.coe_le_coe.mpr le_top))
  have hp := physicalCircleTrace_periodic F
  have hv := localConformal_circleTrace_deriv_ne_zero hR F hFs hhol hnz
  obtain ⟨L, hΓLip⟩ := exists_regularPeriodicCurve_lipschitz hΓ hp hv
  have himage := localConformalRotate_image_ball F φ 1
  have hbφ : Bornology.IsBounded (localConformalRotate F φ '' unitDisk) := by
    rw [himage]
    exact hb
  have hLφ : IsLipschitzDomain (localConformalRotate F φ '' unitDisk) := by
    rw [himage]
    exact hL
  have hγφ : IsBoundaryParam (localConformalRotate F φ '' unitDisk) γ := by
    rw [himage]
    exact hγ
  refine ⟨φ, hφ, c, L, himage, localConformalRotate_image_closedBall F φ 1,
    localConformalRotate_contDiffOn hFs φ, hbφ, hLφ,
    localConformalRotate_holomorphic hhol φ,
    localConformalRotate_injOn_closedBall
      (localConformal_closedDisk_inj_of_supplied_inverse F e he hsource) φ,
    localConformalRotate_lower_deriv_bound hhol hC φ,
    localConformalRotate_upper_differential_bound hR F hFs hhol hK φ,
    localConformalRotatePartialHomeomorph_coe e he φ,
    localConformalRotatePartialHomeomorph_closedDisk_source e hsource φ,
    localConformalRotatePartialHomeomorph_smoothInverse e hes φ,
    hγφ, hτ, hτper, hcoord,
    physicalCircleTrace_localConformalRotate_lipschitz hΓLip φ, ?_⟩
  have hc0 : unitCircleMap (0 : ℝ) = 1 := by simp [circleMap]
  simpa  [hc0] using hcoord 0

end PolyaNeumann
