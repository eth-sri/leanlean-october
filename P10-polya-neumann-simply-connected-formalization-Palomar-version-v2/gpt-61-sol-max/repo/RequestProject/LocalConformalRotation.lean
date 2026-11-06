module

public import RequestProject.PlanarTypes
public import Mathlib.Tactic.FunProp

public import RequestProject.PlanarGeometry

public import RequestProject.LocalConformalArcReparam
public import RequestProject.BoundaryOrigin
public import RequestProject.BoundaryParamShift
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.Topology.OpenPartialHomeomorph.Composition
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
Rotation of the actual supplied conformal coordinates. Multiplication by
`unitCircleMap t` preserves the disk and every centered collar. Precomposition
therefore retains the original physical domain, real smoothness, complex
holomorphicity, and the actual inverse. The circle trace is precisely shifted
by `t`; this connects the genuine choice of transport cut to the same supplied
coordinate interface. The final lift lemmas concern a given genuine C¹ lift
with its proved period increment, and do not assert initial map existence.
This module is part of the verified dependency chain.
-/

@[expose] public section

open scoped ContDiff
noncomputable section
namespace PolyaNeumann

open Set Metric MeasureTheory Filter

/-- The real linear isometry that rotates the actual complex plane. -/
def localConformalRotationLIE t  :=
  rotation (Circle.exp t)

/-- The actual rotation, with its coefficient visible for complex calculus. -/
def localConformalRotation t z  := unitCircleMap t * z

section
variable (t : ℝ)
include t

@[simp] theorem localConformalRotationLIE_apply z :
    localConformalRotationLIE t z = localConformalRotation t z := by
  simp [localConformalRotationLIE, localConformalRotation, circleMap_zero]

theorem localConformalRotationLIE_coe :
    (localConformalRotationLIE t : PlaneMap) = localConformalRotation t :=
  funext (localConformalRotationLIE_apply t)



section
variable (z : ℂ)
include z

@[simp] theorem localConformalRotation_norm :
    ‖localConformalRotation t z‖ = ‖z‖ := by
  simp [localConformalRotation]

@[simp] theorem localConformalRotation_mem_ball r :
    localConformalRotation t z ∈ ball (0 : ℂ) r ↔ z ∈ ball (0 : ℂ) r := by
  simp_all

@[simp] theorem localConformalRotation_mem_closedBall r :
    localConformalRotation t z ∈ closedBall (0 : ℂ) r ↔
      z ∈ closedBall (0 : ℂ) r := by
  simp_all



@[simp] theorem localConformalRotation_neg_left :
    localConformalRotation (-t) (localConformalRotation t z) = z := by
  unfold localConformalRotation
  rw [← mul_assoc, circleMap_zero_mul, one_mul, neg_add_cancel]
  simp [circleMap]

@[simp] theorem localConformalRotation_neg_right :
    localConformalRotation t (localConformalRotation (-t) z) = z := by
  unfold localConformalRotation
  rw [← mul_assoc, circleMap_zero_mul, one_mul, add_neg_cancel]
  simp [circleMap]

end


theorem localConformalRotation_injective :
    Function.Injective (localConformalRotation t) :=
  Function.LeftInverse.injective (localConformalRotation_neg_left t)

@[fun_prop]
theorem localConformalRotation_contDiff  :
    ContDiff ℝ n (localConformalRotation t) := by
  rw [← localConformalRotationLIE_coe]
  fun_prop

theorem localConformalRotation_hasFDerivAt z :
    HasFDerivAt (localConformalRotation t)
      (localConformalRotationLIE t : ℂ →L[ℝ] ℂ) z := by
  have h : HasFDerivAt (localConformalRotationLIE t)
      (localConformalRotationLIE t : ℂ →L[ℝ] ℂ) z :=
    (localConformalRotationLIE t).hasFDerivAt
  simp_all [localConformalRotationLIE_coe]

theorem localConformalRotation_hasDerivAt z :
    HasDerivAt (localConformalRotation t) (unitCircleMap t) z :=
  hasDerivAt_const_mul (unitCircleMap t)

theorem localConformalRotation_image_ball r :
    localConformalRotation t '' ball (0 : ℂ) r = ball (0 : ℂ) r := by
  apply Subset.antisymm
  · grind [localConformalRotation_mem_ball, PolyaNeumann.localConformalRotation]
  · intro z hz
    exact ⟨localConformalRotation (-t) z,
      (localConformalRotation_mem_ball (-t) z r).mpr hz,
      localConformalRotation_neg_right t z⟩

theorem localConformalRotation_image_closedBall r :
    localConformalRotation t '' closedBall (0 : ℂ) r = closedBall (0 : ℂ) r := by
  apply Subset.antisymm
  · grind [localConformalRotation_mem_closedBall, PolyaNeumann.localConformalRotation]
  · intro z hz
    exact ⟨localConformalRotation (-t) z,
      (localConformalRotation_mem_closedBall (-t) z r).mpr hz,
      localConformalRotation_neg_right t z⟩

end


/-- Rotation of the given coordinate map, with no replacement of its image. -/
def localConformalRotate (F : PlaneMap) t  :=
  F ∘ localConformalRotation t

@[simp] theorem localConformalRotate_apply F t z :
    localConformalRotate F t z = F (unitCircleMap t * z) := rfl

theorem localConformalRotate_image_ball F t r :
    localConformalRotate F t '' ball (0 : ℂ) r = F '' ball (0 : ℂ) r := by
  calc
    _ = F '' (localConformalRotation t '' ball 0 r) :=
      (image_image F (localConformalRotation t) _).symm
    _ = _ := by rw [localConformalRotation_image_ball]

theorem localConformalRotate_image_closedBall F t r :
    localConformalRotate F t '' closedBall (0 : ℂ) r = F '' closedBall (0 : ℂ) r := by
  calc
    _ = F '' (localConformalRotation t '' closedBall 0 r) :=
      (image_image F (localConformalRotation t) _).symm
    _ = _ := by rw [localConformalRotation_image_closedBall]

section
variable {F : PlaneMap}
include F

theorem localConformalRotate_contDiffOn 
     (hF : ContDiffOn ℝ n F (ball (0 : ℂ) r)) t :
    ContDiffOn ℝ n (localConformalRotate F t) (ball (0 : ℂ) r) :=
  hF.comp (localConformalRotation_contDiff t).contDiffOn
    (fun z hz => (localConformalRotation_mem_ball t z r).mpr hz)

section
variable {r } (hF : DifferentiableOn ℂ F (ball (0 : ℂ) r)) (t : ℝ)

include r hF t in
theorem localConformalRotate_holomorphic :
    DifferentiableOn ℂ (localConformalRotate F t) (ball (0 : ℂ) r) :=
  hF.comp (fun z _ => (localConformalRotation_hasDerivAt t z).differentiableAt.differentiableWithinAt)
    (fun z hz => (localConformalRotation_mem_ball t z r).mpr hz)

theorem localConformalRotate_injOn_closedBall 
    (hF : InjOn F (closedBall (0 : ℂ) r)) t :
    InjOn (localConformalRotate F t) (closedBall (0 : ℂ) r) := by
  intro z hz w hw hzw
  exact localConformalRotation_injective t (hF
    ((localConformalRotation_mem_closedBall t z r).mpr hz)
    ((localConformalRotation_mem_closedBall t w r).mpr hw) hzw)

theorem localConformalRotate_hasDerivAt t 
    (hF : DifferentiableAt ℂ F (localConformalRotation t z)) :
    HasDerivAt (localConformalRotate F t)
      (deriv F (localConformalRotation t z) * unitCircleMap t) z := hF.hasDerivAt.comp z (localConformalRotation_hasDerivAt t z)

include r hF t in
theorem localConformalRotate_deriv_norm
     (hz : z ∈ ball (0 : ℂ) r) :
    ‖deriv (localConformalRotate F t) z‖ = ‖deriv F (localConformalRotation t z)‖ := by
  rw [(localConformalRotate_hasDerivAt t
    (hF.differentiableAt (isOpen_ball.mem_nhds
      ((localConformalRotation_mem_ball t z r).mpr hz)))).deriv]
  simp

end


theorem localConformalRotate_lower_deriv_bound 
    (hhol : DifferentiableOn ℂ F unitDisk)
    (hC : DiskInverseJacobianBound F C) t :
    ∀ z ∈ unitDisk, 1 ≤ C * ‖deriv (localConformalRotate F t) z‖ ^ 2 := by
  grind only [localConformalRotate_deriv_norm, localConformalRotation_mem_ball]

theorem localConformalRotate_fderiv t 
    (hF : DifferentiableAt ℝ F (localConformalRotation t z)) v :
    fderiv ℝ (localConformalRotate F t) z v =
      fderiv ℝ F (localConformalRotation t z) (localConformalRotation t v) := by
  change fderiv ℝ (F ∘ localConformalRotation t) z v = _
  rw [(hF.hasFDerivAt.comp z (localConformalRotation_hasFDerivAt t z)).fderiv]
  simp_all

end


section
variable {R } (hR : 1 < R) (F : PlaneMap) (hFs : RealSmoothOnBall F R) (hhol : DifferentiableOn ℂ F unitDisk)
include R hR F hFs hhol

theorem localConformalRotate_closedDifferential_norm t
     (hz : z ∈ closedUnitDisk) :
    ‖fderiv ℝ (localConformalRotate F t) z 1‖ =
      ‖fderiv ℝ F (localConformalRotation t z) 1‖ := by
  have hzt := (localConformalRotation_mem_closedBall t z 1).mpr hz
  rw [localConformalRotate_fderiv t
    ((hFs.contDiffAt (isOpen_ball.mem_nhds (closedBall_subset_ball hR hzt))).differentiableAt
      (by simp)),
    localConformal_fderiv_closedDisk hR F hFs hhol hzt]
  simp 

theorem localConformalRotate_upper_differential_bound 
    (hK : DiskDerivativeBound F K) t :
    ∀ z ∈ unitDisk, ‖fderiv ℝ (localConformalRotate F t) z 1‖ ≤ K := by
  intro z hz
  rw [localConformalRotate_closedDifferential_norm hR F hFs hhol t
    (ball_subset_closedBall hz)]
  simp_all

end


/-- The actual new boundary origin is the old point at parameter `t`. -/
theorem physicalCircleTrace_localConformalRotate F t θ :
    physicalCircleTrace (localConformalRotate F t) θ = physicalCircleTrace F (θ + t) := by
  simp  [physicalCircleTrace, circleMap_zero_mul, add_comm t θ]

theorem physicalCircleTrace_localConformalRotate_lipschitz
      (hΓ : LipschitzWith K (physicalCircleTrace F)) t :
    LipschitzWith K (physicalCircleTrace (localConformalRotate F t)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa [physicalCircleTrace_localConformalRotate] using
    hΓ.dist_le_mul (x + t) (y + t)



@[simp] theorem localConformalRotationLIE_symm t :
    (localConformalRotationLIE t).symm = localConformalRotationLIE (-t) := by
  simp_all [localConformalRotationLIE]

/-- Precomposition of the supplied actual local homeomorphism by rotation. -/
def localConformalRotatePartialHomeomorph (e : OpenPartialHomeomorph ℂ ℂ) t  :=
  (localConformalRotationLIE t).toHomeomorph.transOpenPartialHomeomorph e

section
variable (e : OpenPartialHomeomorph ℂ ℂ) (t : ℝ)
include e t

@[simp] theorem localConformalRotatePartialHomeomorph_apply z :
    localConformalRotatePartialHomeomorph e t z = e (localConformalRotation t z) := by
  change e (localConformalRotationLIE t z) = _
  rw [localConformalRotationLIE_apply]

@[simp] theorem localConformalRotatePartialHomeomorph_symm_apply w :
    (localConformalRotatePartialHomeomorph e t).symm w =
      localConformalRotation (-t) (e.symm w) := by
  change (localConformalRotationLIE t).symm (e.symm w) = _
  simp_all

theorem localConformalRotatePartialHomeomorph_source :
    (localConformalRotatePartialHomeomorph e t).source =
      localConformalRotation t ⁻¹' e.source := by
  ext z
  change localConformalRotationLIE t z ∈ e.source ↔ _
  norm_num

@[simp] theorem localConformalRotatePartialHomeomorph_target :
    (localConformalRotatePartialHomeomorph e t).target = e.target := rfl

end


theorem localConformalRotatePartialHomeomorph_coe 
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : PlaneMap) = F) t :
    (localConformalRotatePartialHomeomorph e t : PlaneMap) = localConformalRotate F t := by
  aesop

theorem localConformalRotatePartialHomeomorph_closedDisk_source
    e
    (hsource : closedUnitDisk ⊆ e.source) t :
    closedUnitDisk ⊆ (localConformalRotatePartialHomeomorph e t).source := by
  grind [localConformalRotatePartialHomeomorph_source, localConformalRotation_mem_closedBall]

theorem localConformalRotatePartialHomeomorph_smoothInverse
    e
    (hes : RealSmoothOn e.symm e.target) t :
    RealSmoothOn (localConformalRotatePartialHomeomorph e t).symm
      (localConformalRotatePartialHomeomorph e t).target := by
  have hfun  :=
    funext (localConformalRotatePartialHomeomorph_symm_apply e t)
  rw [localConformalRotatePartialHomeomorph_target, hfun]
  fun_prop

/-- The smooth inverse forces the actual closed-disk real differential to
be nonzero, including at the boundary. -/
theorem localConformalRotation_closedDifferential_ne_zero_of_inverse
     (hR : 1 < R) F
    (hFs : RealSmoothOnBall F R)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : PlaneMap) = F)
    (hsource : closedUnitDisk ⊆ e.source)
    (hes : RealSmoothOn e.symm e.target) :
    ∀ z ∈ closedUnitDisk, fderiv ℝ F z 1 ≠ 0 := by
  intro z hz
  have hzs := hsource hz
  have hzt : F z ∈ e.target := by
    rw [← he]
    exact e.mapsTo hzs
  have hdF := ((hFs.contDiffAt (isOpen_ball.mem_nhds (closedBall_subset_ball hR hz))).differentiableAt
    (by simp)).hasFDerivAt
  have hdG := ((hes.contDiffAt (e.open_target.mem_nhds hzt)).differentiableAt
    (by simp)).hasFDerivAt
  have hcomp := hdG.comp z hdF
  have hid : HasFDerivAt id
      ((fderiv ℝ e.symm (F z)).comp (fderiv ℝ F z)) z := by
    apply hcomp.congr_of_eventuallyEq
    filter_upwards [e.open_source.mem_nhds hzs] with x hx
    measurability
  have hlin := hid.unique (hasFDerivAt_id z)
  have hval := congrArg (fun A : ℂ →L[ℝ] ℂ => A 1) hlin
  change fderiv ℝ e.symm (F z) (fderiv ℝ F z 1) = 1 at hval
  measurability

/-- Rebase the genuine parameter lift at the selected conformal origin. -/
def localConformalRotateTraceReparam (τ : RealMap) t θ  :=
  τ (θ + t) - τ t

@[simp] theorem localConformalRotateTraceReparam_zero τ t :
    localConformalRotateTraceReparam τ t 0 = 0 := by
  simp [localConformalRotateTraceReparam]

section
variable {τ } {c } (hτ : IsC1TraceReparam τ c)
include τ c hτ

theorem localConformalRotateTraceReparam_hasDerivAt t θ :
    HasDerivAt (localConformalRotateTraceReparam τ t) (deriv τ (θ + t)) θ := by
  show HasDerivAt (fun θ => τ (θ + t) - τ t) _ θ
  simpa   using
    (((hτ.contDiff.differentiable_one (θ + t)).hasDerivAt.comp θ
      ((hasDerivAt_id θ).add_const t)).sub_const (τ t))

theorem localConformalRotateTraceReparam_deriv t θ :
    deriv (localConformalRotateTraceReparam τ t) θ = deriv τ (θ + t) :=
  (localConformalRotateTraceReparam_hasDerivAt hτ t θ).deriv

/-- C¹ continuity upgrades the original AE lower bound on its closed cut
interval to a true pointwise bound on that interval. -/
theorem IsC1TraceReparam.lower_pointwise :
    ∀ θ ∈ boundaryInterval, c ≤ deriv τ θ := by
  have heq : EqOn (fun θ => max c (deriv τ θ)) (deriv τ)
      boundaryInterval := by
    apply Measure.eqOn_of_ae_eq
      (hτ.lower_ae.mono (fun θ hθ => max_eq_right hθ))
      (continuous_const.max hτ.contDiff.continuous_deriv_one).continuousOn
      hτ.contDiff.continuous_deriv_one.continuousOn
    simp_all
  grind

end


section
variable {τ } {c } (hτ : IsC1TraceReparam τ c) (hper : ∀ θ, τ (θ + 2 * Real.pi) = τ θ + 2 * Real.pi)
include τ c hτ hper

theorem IsC1TraceReparam.deriv_periodic_of_add_period :
    Function.Periodic (deriv τ) circlePeriod := by
  intro θ
  have hd : HasDerivAt (fun x => τ (x + 2 * Real.pi))
      (deriv τ (θ + 2 * Real.pi)) θ := by
    simpa  [Function.comp_def] using
      (hτ.contDiff.differentiable_one (θ + 2 * Real.pi)).hasDerivAt.comp θ
        ((hasDerivAt_id θ).add_const circlePeriod)
  have heq  :=
    funext hper
  rw [heq] at hd
  exact hd.unique ((hτ.contDiff.differentiable_one θ).hasDerivAt.add_const circlePeriod)

/-- The period increment transports the original lower bound to the whole
real line, rather than introducing a new global Jacobian premise. -/
theorem IsC1TraceReparam.lower_global_of_add_period θ :
    c ≤ deriv τ θ := by
  let θ' := toIcoMod Real.two_pi_pos 0 θ
  have hθ' : θ' ∈ Ico 0 circlePeriod := by
    simpa   using toIcoMod_mem_Ico Real.two_pi_pos 0 θ
  have heq : deriv τ θ' = deriv τ θ := by
    dsimp only [θ']
    rw [toIcoMod, (hτ.deriv_periodic_of_add_period hper).sub_zsmul_eq]
  rw [← heq]
  exact hτ.lower_pointwise θ' (Ico_subset_Icc_self hθ')

theorem localConformalRotateTraceReparam_isC1 t :
    IsC1TraceReparam (localConformalRotateTraceReparam τ t) c := by
  obtain ⟨K, hK⟩ := hτ.lipschitz
  refine ⟨?_, ⟨K, ?_⟩, ?_, localConformalRotateTraceReparam_zero τ t, ?_,
    hτ.lower_pos, ?_⟩
  · intro x y hxy
    exact sub_le_sub_right (hτ.monotone (add_le_add hxy (le_refl t))) (τ t)
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa [localConformalRotateTraceReparam] using
      hK.dist_le_mul (x + t) (y + t)
  · exact (hτ.contDiff.comp (contDiff_id.add contDiff_const)).sub contDiff_const
  · grind only [localConformalRotateTraceReparam]
  · apply Eventually.of_forall
    intro θ
    rw [localConformalRotateTraceReparam_deriv hτ]
    exact hτ.lower_global_of_add_period hper (θ + t)

end


theorem localConformalRotateTraceReparam_add_period 
    (hper : ∀ θ, τ (θ + 2 * Real.pi) = τ θ + 2 * Real.pi) t θ :
    localConformalRotateTraceReparam τ t (θ + 2 * Real.pi) =
      localConformalRotateTraceReparam τ t θ + 2 * Real.pi := by
  grind only [localConformalRotateTraceReparam]

end PolyaNeumann
end
