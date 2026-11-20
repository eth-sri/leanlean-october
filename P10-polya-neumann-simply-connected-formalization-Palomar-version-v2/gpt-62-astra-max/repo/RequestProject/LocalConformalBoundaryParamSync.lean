module

public import RequestProject.DiskCoordinates

public import RequestProject.SmoothBoundaryParamUniqueness
public import RequestProject.LocalConformalAreaOrientation
public import RequestProject.LocalConformalRotation
public import RequestProject.PlanarNotation

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

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace PolyaNeumann

open Set Metric MeasureTheory Filter
open scoped Topology Real

/-- The canonical arc curve is genuinely C¹: its previously proved inverse
derivative is continuous because the original speed is continuous and nonzero. -/
theorem normalizedArcCurve_contDiff {Γ : ℝ → ℂ}
    (hΓ : ContDiff ℝ 1 Γ) (hper : Function.Periodic Γ anglePeriod)
    (hnz : ∀ θ, deriv Γ θ ≠ 0) :
    ContDiff ℝ 1 (normalizedArcCurve hΓ hper hnz) := by
  
  
  
  
  have hv  :=
    hΓ.continuous_deriv_one.comp ((normalizedArcOrderIso hΓ hper hnz).symm.continuous)
  
  have hdne (t : ℝ)  :=
    (mul_pos (div_pos Real.two_pi_pos (arcLen_period_pos_of_regular hΓ hnz)) (norm_pos_iff.mpr (hnz (((normalizedArcOrderIso hΓ hper hnz).symm) t)))).ne'
  
  refine contDiff_one_iff_deriv.mpr ⟨?_, ?_⟩
  · exact fun t => (normalizedArcCurve_hasDerivAt hΓ hper hnz t).differentiableAt
  · rw [(funext (fun t => (normalizedArcCurve_hasDerivAt hΓ hper hnz t).deriv))]
    fun_prop

/-- The canonical arc curve has a genuinely nonzero velocity everywhere. -/
theorem normalizedArcCurve_deriv_ne_zero {Γ : ℝ → ℂ}
    (hΓ : ContDiff ℝ 1 Γ) (hper : Function.Periodic Γ anglePeriod)
    (hnz : ∀ θ, deriv Γ θ ≠ 0) (t : ℝ) :
    deriv (normalizedArcCurve hΓ hper hnz) t ≠ 0 := by
  apply norm_pos_iff.mp
  rw [normalizedArcCurve_speed hΓ hper hnz]
  exact div_pos (arcLen_period_pos_of_regular hΓ hnz) Real.two_pi_pos

section

variable (Φ : DiskCoordinates) (t : ℝ)

/-- The actual canonical arc parameter, not merely an existential reference,
is a physical boundary parameter.  Its identification with the proved reference
uses surjectivity of the actual normalized-arclength map. -/
theorem localConformal_normalizedArcCurve_isBoundaryParam (Φ : SmoothDiskMap)
    (hhol : DifferentiableOn ℂ Φ.map unitDisk) (hinj : InjOn Φ.map closedDisk)
    (hnz : ∀ z ∈ diskSphere, fderiv ℝ Φ.map z 1 ≠ 0) (hL : IsLipschitzDomain Φ.domain) :
    let hΓ  :=
      Φ.boundaryC1
    let hp := Φ.periodic_boundary
    let hv := localConformal_circleTrace_deriv_ne_zero Φ hhol hnz
    IsBoundaryParam Φ.domain (normalizedArcCurve hΓ hp hv) := by
  
  let hΓ  :=
    Φ.boundaryC1
  let hp := Φ.periodic_boundary
  let hv := localConformal_circleTrace_deriv_ne_zero Φ hhol hnz
  obtain ⟨β, c, hβ, _, hfactor⟩ :=
    exists_localConformal_isBoundaryParam Φ hhol hinj hnz hL
  have heq : β = normalizedArcCurve hΓ hp hv := by
    funext t
    obtain ⟨θ, hθ⟩ := normalizedArcReparam_surjective hΓ hp hv t
    calc
      _ = β _ := by rw [hθ]
      _ = Φ.boundary θ := (hfactor θ).symm
      _ = _ :=
        normalizedArcCurve_factorization hΓ hp hv θ
      _ = _ := by rw [hθ]
  rw [heq] at hβ
  exact hβ

/-- Given the proved canonical physical arc parameter, select the actual
circle phase and the genuine endpoint-preserving C¹ arclength lift for any
original physical boundary parameter. -/
theorem exists_normalizedArc_origin_sync {Ω : Set ℂ} {Γ γ : ℝ → ℂ}
    (hb : Bornology.IsBounded Ω) (hΩ : IsDomain Ω)
    (hΓ : ContDiff ℝ 1 Γ) (hper : Function.Periodic Γ anglePeriod)
    (hnz : ∀ θ, deriv Γ θ ≠ 0)
    (hβ : IsBoundaryParam Ω (normalizedArcCurve hΓ hper hnz))
    (hγ : IsBoundaryParam Ω γ) :
    ∃ φ ∈ angleInterval, ∃ c : ℝ,
      IsC1TraceReparam (localConformalRotateTraceReparam (normalizedArcReparam Γ) φ) c ∧
      (∀ θ : ℝ,
        localConformalRotateTraceReparam (normalizedArcReparam Γ) φ (θ + anglePeriod) =
          localConformalRotateTraceReparam (normalizedArcReparam Γ) φ θ + anglePeriod) ∧
      (∀ θ : ℝ, Γ (θ + φ) =
        γ (localConformalRotateTraceReparam (normalizedArcReparam Γ) φ θ)) := by
  obtain ⟨t, ht, hshift⟩ := exists_boundaryParam_shift_of_bounded_domain hb hΩ hβ
    (normalizedArcCurve_contDiff hΓ hper hnz)
    (normalizedArcCurve_deriv_ne_zero hΓ hper hnz) hγ
  let φ  := (normalizedArcOrderIso hΓ hper hnz).symm t
  
  have hφval : normalizedArcReparam Γ φ = t :=
    (normalizedArcOrderIso hΓ hper hnz).apply_symm_apply t
  obtain ⟨c, hτ, _, hτper⟩ := exists_isC1TraceReparam_normalizedArc hΓ hper hnz
  refine ⟨φ, (by
    constructor
    · simpa using (normalizedArcOrderIso hΓ hper hnz).symm.monotone ht.1
    · simpa using (normalizedArcOrderIso hΓ hper hnz).symm.monotone ht.2), c, localConformalRotateTraceReparam_isC1 hτ hτper φ,
    localConformalRotateTraceReparam_add_period hτper φ, ?_⟩
  intro θ
  calc
    _ = _ :=
      normalizedArcCurve_factorization hΓ hper hnz _
    _ = normalizedArcCurve hΓ hper hnz
        _ := by
      simp [localConformalRotateTraceReparam, hφval]
    _ = _ :=
      (hshift _).symm

/-- Restricting the genuine neighborhood inverse gives closed-disk injectivity. -/
theorem DiskCoordinates.closedInj : InjOn Φ.map closedDisk :=
  Φ.chart_eq ▸ Φ.chart.injOn.mono Φ.source

include t Φ in
/-- Rotation of the disk acts on supplied coordinates without changing the domain
or differential bounds. -/
def DiskCoordinates.rotate : DiskCoordinates where
  radius := Φ.radius
  one_lt_radius := Φ.one_lt_radius
  map := localConformalRotate Φ.map t
  smooth := localConformalRotate_contDiffOn Φ.smooth t
  C := Φ.C
  bounded := (localConformalRotate_image_ball Φ.map t 1).symm ▸ Φ.bounded
  lipschitzDomain := (localConformalRotate_image_ball Φ.map t 1).symm ▸ Φ.lipschitzDomain
  holomorphic := localConformalRotate_holomorphic Φ.holomorphic t
  inj := (localConformalRotate_injOn_closedBall Φ.closedInj t).mono ball_subset_closedBall
  deriv_lower := localConformalRotate_lower_deriv_bound Φ.holomorphic Φ.deriv_lower t
  K := Φ.K
  deriv_upper := localConformalRotate_upper_differential_bound Φ Φ.holomorphic Φ.deriv_upper t
  chart := localConformalRotatePartialHomeomorph Φ.chart t
  chart_eq := localConformalRotatePartialHomeomorph_coe Φ.chart Φ.chart_eq t
  source := localConformalRotatePartialHomeomorph_closedDisk_source Φ.chart Φ.source t
  smoothInverse := localConformalRotatePartialHomeomorph_smoothInverse Φ.chart Φ.smoothInverse t

theorem DiskCoordinates.rotate_domain : (Φ.rotate t).domain = Φ.domain :=
  localConformalRotate_image_ball Φ.map t 1

/-- Actual rotation of supplied coordinates synchronizes their genuine
circle trace with the original physical boundary parameter. -/
theorem DiskCoordinates.boundaryParam_sync {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Φ.domain γ) :
    ∃ φ ∈ angleInterval, ∃ c : ℝ,
      IsC1TraceReparam
        (localConformalRotateTraceReparam (normalizedArcReparam Φ.boundary) φ) c ∧
      (Φ.rotate φ).boundary = γ ∘ localConformalRotateTraceReparam (normalizedArcReparam Φ.boundary) φ := by
  have hnz := Φ.closedDifferential_ne_zero Φ.chart Φ.chart_eq Φ.source Φ.smoothInverse
  have hnzb := fun z hz => hnz z (sphere_subset_closedBall hz)
  obtain ⟨φ, hφ, c, hτ, _, heq⟩ := exists_normalizedArc_origin_sync Φ.bounded Φ.lipschitzDomain.1
    Φ.boundaryC1 Φ.periodic_boundary (localConformal_circleTrace_deriv_ne_zero Φ Φ.holomorphic hnzb)
    (localConformal_normalizedArcCurve_isBoundaryParam Φ Φ.holomorphic Φ.closedInj hnzb Φ.lipschitzDomain) hγ
  exact ⟨φ, hφ, c, hτ, funext fun θ => (physicalCircleTrace_localConformalRotate Φ.map φ θ).trans (heq θ)⟩

end

end PolyaNeumann
end
