module

public import RequestProject.DiskCoordinates

public import RequestProject.LocalConformalArcReparam
public import RequestProject.BoundaryOrigin
public import RequestProject.BoundaryParamShift
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.Topology.OpenPartialHomeomorph.Composition
public import Mathlib.MeasureTheory.Measure.OpenPos
public import RequestProject.PlanarNotation

/-!
Rotation of the actual supplied conformal coordinates. Multiplication by
`circleMap 0 1 t` preserves the disk and every centered collar. Precomposition
therefore retains the original physical domain, real smoothness, complex
holomorphicity, and the actual inverse. The circle trace is precisely shifted
by `t`; this connects the genuine choice of transport cut to the same supplied
coordinate interface. The final lift lemmas concern a given genuine C¹ lift
with its proved period increment, and do not assert initial map existence.
This module is part of the verified dependency chain.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped ContDiff

namespace PolyaNeumann

open Set Metric MeasureTheory Filter
open scoped Topology

section

variable (F : ℂ → ℂ) (t : ℝ) (z : ℂ) (r : ℝ)
include t

/-- The real linear isometry that rotates the actual complex plane. -/
def localConformalRotationLIE : ℂ ≃ₗᵢ[ℝ] ℂ :=
  rotation (Circle.exp t)

include z in
/-- The actual rotation, with its coefficient visible for complex calculus. -/
def localConformalRotation : ℂ := unitCirclePt t * z

@[simp] theorem localConformalRotationLIE_apply :
    localConformalRotationLIE t z = localConformalRotation t z := by
  simp [localConformalRotationLIE, rotation_apply, Circle.coe_exp,
    localConformalRotation, circleMap_zero]

theorem localConformalRotationLIE_coe :
    (localConformalRotationLIE t : ℂ → ℂ) = localConformalRotation t :=
  funext (localConformalRotationLIE_apply t)

@[simp] theorem localConformalRotation_norm :
    ‖localConformalRotation t z‖ = ‖z‖ := by
  simp [localConformalRotation]

@[simp] theorem localConformalRotation_mem_ball :
    localConformalRotation t z ∈ ball (0 : ℂ) r ↔ z ∈ ball (0 : ℂ) r := by
  simp

@[simp] theorem localConformalRotation_mem_closedBall :
    localConformalRotation t z ∈ closedBall (0 : ℂ) r ↔
      z ∈ closedBall (0 : ℂ) r := by
  simp

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

theorem localConformalRotation_injective :
    Function.Injective (localConformalRotation t) :=
  Function.LeftInverse.injective (localConformalRotation_neg_left t)

theorem localConformalRotation_contDiff {n : WithTop ℕ∞} :
    ContDiff ℝ n (localConformalRotation t) := by
  rw [← localConformalRotationLIE_coe]
  fun_prop

theorem localConformalRotation_hasFDerivAt :
    HasFDerivAt (localConformalRotation t)
      (localConformalRotationLIE t : ℂ →L[ℝ] ℂ) z := by
  have h : HasFDerivAt (localConformalRotationLIE t)
      (localConformalRotationLIE t : ℂ →L[ℝ] ℂ) z :=
    (localConformalRotationLIE t).hasFDerivAt
  rw [localConformalRotationLIE_coe] at h
  exact h

theorem localConformalRotation_hasDerivAt :
    HasDerivAt (localConformalRotation t) (unitCirclePt t) z :=
  hasDerivAt_const_mul (unitCirclePt t)

theorem localConformalRotation_image_ball :
    localConformalRotation t '' ball (0 : ℂ) r = ball (0 : ℂ) r := by
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    aesop
  · intro z hz
    exact ⟨localConformalRotation (-t) z,
      (localConformalRotation_mem_ball (-t) z r).mpr hz,
      localConformalRotation_neg_right t z⟩

theorem localConformalRotation_image_closedBall :
    localConformalRotation t '' closedBall (0 : ℂ) r = closedBall (0 : ℂ) r := by
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    aesop
  · intro z hz
    exact ⟨localConformalRotation (-t) z,
      (localConformalRotation_mem_closedBall (-t) z r).mpr hz,
      localConformalRotation_neg_right t z⟩

include F in
/-- Rotation of the given coordinate map, with no replacement of its image. -/
def localConformalRotate : ℂ → ℂ :=
  F ∘ localConformalRotation t

@[simp] theorem localConformalRotate_apply :
    localConformalRotate F t z = F (unitCirclePt t * z) := rfl

theorem localConformalRotate_image_ball :
    localConformalRotate F t '' ball (0 : ℂ) r = F '' ball (0 : ℂ) r := calc
    _ = _ :=
      (image_image F (localConformalRotation t) _).symm
    _ = _ := by rw [localConformalRotation_image_ball]

theorem localConformalRotate_image_closedBall :
    localConformalRotate F t '' closedBall (0 : ℂ) r = F '' closedBall (0 : ℂ) r := calc
    _ = _ :=
      (image_image F (localConformalRotation t) _).symm
    _ = _ := by rw [localConformalRotation_image_closedBall]

end

section

variable (Φ : SmoothDiskMap) (F : ℂ → ℂ) (e : OpenPartialHomeomorph ℂ ℂ) (τ : ℝ → ℝ)
    (hhol : DifferentiableOn ℂ Φ.map unitDisk) (hsource : closedDisk ⊆ e.source)
    (hes : ContDiffOn ℝ ∞ e.symm e.target) (t θ : ℝ)

theorem localConformalRotate_contDiffOn {F : ℂ → ℂ} {r : ℝ}
    {n : WithTop ℕ∞} (hF : ContDiffOn ℝ n F (ball (0 : ℂ) r)) (t : ℝ) :
    ContDiffOn ℝ n (localConformalRotate F t) (ball (0 : ℂ) r) :=
  hF.comp (localConformalRotation_contDiff t).contDiffOn
    (fun z hz => (localConformalRotation_mem_ball t z r).mpr hz)

theorem localConformalRotate_holomorphic {F : ℂ → ℂ} {r : ℝ}
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) r)) (t : ℝ) :
    DifferentiableOn ℂ (localConformalRotate F t) (ball (0 : ℂ) r) :=
  hF.comp (fun z _ => (localConformalRotation_hasDerivAt t z).differentiableAt.differentiableWithinAt)
    (fun z hz => (localConformalRotation_mem_ball t z r).mpr hz)

theorem localConformalRotate_injOn_closedBall {F : ℂ → ℂ} {r : ℝ}
    (hF : InjOn F (closedBall (0 : ℂ) r)) (t : ℝ) :
    InjOn (localConformalRotate F t) (closedBall (0 : ℂ) r) := by
  intro z hz w hw hzw
  exact localConformalRotation_injective t (hF
    ((localConformalRotation_mem_closedBall t z r).mpr hz)
    ((localConformalRotation_mem_closedBall t w r).mpr hw) hzw)

theorem localConformalRotate_hasDerivAt {F : ℂ → ℂ} (t : ℝ) {z : ℂ}
    (hF : DifferentiableAt ℂ F (localConformalRotation t z)) :
    HasDerivAt (localConformalRotate F t)
      (deriv F (localConformalRotation t z) * unitCirclePt t) z := hF.hasDerivAt.comp z (localConformalRotation_hasDerivAt t z)

theorem localConformalRotate_deriv_norm {F : ℂ → ℂ} {r : ℝ}
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) r)) (t : ℝ)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) r) :
    ‖deriv (localConformalRotate F t) z‖ = ‖deriv F (localConformalRotation t z)‖ := by
  rw [(localConformalRotate_hasDerivAt t
    (hF.differentiableAt (isOpen_ball.mem_nhds
      ((localConformalRotation_mem_ball t z r).mpr hz)))).deriv]
  simp

theorem localConformalRotate_lower_deriv_bound {F : ℂ → ℂ} {C : ℝ}
    (hhol : DifferentiableOn ℂ F unitDisk)
    (hC : ∀ z ∈ unitDisk, 1 ≤ C * ‖deriv F z‖ ^ 2) (t : ℝ) :
    ∀ z ∈ unitDisk, 1 ≤ C * ‖deriv (localConformalRotate F t) z‖ ^ 2 := by
  intro z hz
  rw [localConformalRotate_deriv_norm hhol t hz]
  aesop

theorem localConformalRotate_fderiv {F : ℂ → ℂ} (t : ℝ) {z : ℂ}
    (hF : DifferentiableAt ℝ F (localConformalRotation t z)) (v : ℂ) :
    fderiv ℝ (localConformalRotate F t) z v =
      fderiv ℝ F (localConformalRotation t z) (localConformalRotation t v) := by
  change fderiv ℝ (F ∘ localConformalRotation t) z v = _
  rw [(hF.hasFDerivAt.comp z (localConformalRotation_hasFDerivAt t z)).fderiv]
  simp

include hhol in
theorem localConformalRotate_closedDifferential_norm {z : ℂ} (hz : z ∈ closedDisk) :
    ‖fderiv ℝ (localConformalRotate Φ.map t) z 1‖ =
      ‖fderiv ℝ Φ.map (localConformalRotation t z) 1‖ := by
  have hzt := (localConformalRotation_mem_closedBall t z 1).mpr hz
  rw [localConformalRotate_fderiv t
    ((Φ.smooth.contDiffAt (isOpen_ball.mem_nhds (closedBall_subset_ball Φ.one_lt_radius hzt))).differentiableAt
      (by simp)),
    localConformal_fderiv_closedDisk Φ hhol hzt]
  simp

include hhol in
theorem localConformalRotate_upper_differential_bound {K : ℝ}
    (hK : ∀ z ∈ unitDisk, ‖fderiv ℝ Φ.map z 1‖ ≤ K) (t : ℝ) :
    ∀ z ∈ unitDisk, ‖fderiv ℝ (localConformalRotate Φ.map t) z 1‖ ≤ K := by
  intro z hz
  rw [localConformalRotate_closedDifferential_norm Φ hhol t
    (ball_subset_closedBall hz)]
  aesop

/-- The actual new boundary origin is the old point at parameter `t`. -/
theorem physicalCircleTrace_localConformalRotate :
    physicalCircleTrace (localConformalRotate F t) θ = physicalCircleTrace F (θ + t) := by
  simp [physicalCircleTrace, circleMap_zero_mul, add_comm t θ]

theorem physicalCircleTrace_localConformalRotate_lipschitz
    {F : ℂ → ℂ} {K : NNReal} (hΓ : LipschitzWith K (physicalCircleTrace F)) (t : ℝ) :
    LipschitzWith K (physicalCircleTrace (localConformalRotate F t)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa [physicalCircleTrace_localConformalRotate] using
    hΓ.dist_le_mul (x + t) (y + t)

@[simp] theorem localConformalRotationLIE_symm :
    (localConformalRotationLIE t).symm = localConformalRotationLIE (-t) := by
  simp [localConformalRotationLIE, rotation_symm]

include e t in
/-- Precomposition of the supplied actual local homeomorphism by rotation. -/
def localConformalRotatePartialHomeomorph :
    OpenPartialHomeomorph ℂ ℂ :=
  (localConformalRotationLIE t).toHomeomorph.transOpenPartialHomeomorph e

@[simp] theorem localConformalRotatePartialHomeomorph_apply (z : ℂ) :
    localConformalRotatePartialHomeomorph e t z = e (localConformalRotation t z) := by
  change e (localConformalRotationLIE t z) = _
  rw [localConformalRotationLIE_apply]

@[simp] theorem localConformalRotatePartialHomeomorph_symm_apply (w : ℂ) :
    (localConformalRotatePartialHomeomorph e t).symm w =
      localConformalRotation (-t) (e.symm w) := by
  change (localConformalRotationLIE t).symm (e.symm w) = _
  rw [localConformalRotationLIE_symm, localConformalRotationLIE_apply]

theorem localConformalRotatePartialHomeomorph_source :
    (localConformalRotatePartialHomeomorph e t).source =
      localConformalRotation t ⁻¹' e.source := by
  ext z
  change localConformalRotationLIE t z ∈ e.source ↔ _
  simp

@[simp] theorem localConformalRotatePartialHomeomorph_target :
    (localConformalRotatePartialHomeomorph e t).target = e.target := rfl

theorem localConformalRotatePartialHomeomorph_coe {F : ℂ → ℂ}
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : ℂ → ℂ) = F) (t : ℝ) :
    (localConformalRotatePartialHomeomorph e t : ℂ → ℂ) = localConformalRotate F t := by
  funext z
  rw [localConformalRotatePartialHomeomorph_apply, he]
  rfl

include hsource in
theorem localConformalRotatePartialHomeomorph_closedDisk_source :
    closedDisk ⊆ (localConformalRotatePartialHomeomorph e t).source := by
  rw [localConformalRotatePartialHomeomorph_source]
  intro z hz
  aesop

include hes in
theorem localConformalRotatePartialHomeomorph_smoothInverse :
    ContDiffOn ℝ ∞ (localConformalRotatePartialHomeomorph e t).symm
      (localConformalRotatePartialHomeomorph e t).target := by
  
  rw [localConformalRotatePartialHomeomorph_target, (funext (localConformalRotatePartialHomeomorph_symm_apply e t))]
  exact (localConformalRotation_contDiff (-t)).comp_contDiffOn hes

include t θ τ in
/-- Rebase the genuine parameter lift at the selected conformal origin. -/
def localConformalRotateTraceReparam : ℝ :=
  τ (θ + t) - τ t

@[simp] theorem localConformalRotateTraceReparam_zero :
    localConformalRotateTraceReparam τ t 0 = 0 := by
  simp [localConformalRotateTraceReparam]

end

theorem localConformalRotateTraceReparam_hasDerivAt {τ : ℝ → ℝ} {c : ℝ}
    (hτ : IsC1TraceReparam τ c) (t θ : ℝ) :
    HasDerivAt (localConformalRotateTraceReparam τ t) (deriv τ (θ + t)) θ := by
  show HasDerivAt (fun θ => τ (θ + t) - τ t) _ θ
  simpa using (((hτ.contDiff.differentiable_one (θ + t)).hasDerivAt.comp θ
      ((hasDerivAt_id θ).add_const t)).sub_const (τ t))

theorem localConformalRotateTraceReparam_deriv {τ : ℝ → ℝ} {c : ℝ}
    (hτ : IsC1TraceReparam τ c) (t θ : ℝ) :
    deriv (localConformalRotateTraceReparam τ t) θ = deriv τ (θ + t) :=
  (localConformalRotateTraceReparam_hasDerivAt hτ t θ).deriv

/-- C¹ continuity upgrades the original AE lower bound on its closed cut
interval to a true pointwise bound on that interval. -/
theorem IsC1TraceReparam.lower_pointwise {τ : ℝ → ℝ} {c : ℝ}
    (hτ : IsC1TraceReparam τ c) :
    ∀ θ ∈ angleInterval, c ≤ deriv τ θ := by
  have heq : EqOn (fun θ => max c (deriv τ θ)) (deriv τ)
      angleInterval := by
    apply Measure.eqOn_of_ae_eq
      (hτ.lower_ae.mono (fun θ hθ => max_eq_right hθ))
      (continuous_const.max hτ.contDiff.continuous_deriv_one).continuousOn
      hτ.contDiff.continuous_deriv_one.continuousOn
    simpa using (subset_rfl : angleInterval ⊆ angleInterval)
  grind

theorem IsC1TraceReparam.deriv_periodic_of_add_period {τ : ℝ → ℝ} {c : ℝ}
    (hτ : IsC1TraceReparam τ c)
    (hper : ∀ θ, τ (θ + anglePeriod) = τ θ + anglePeriod) :
    Function.Periodic (deriv τ) anglePeriod := by
  intro θ
  have hd : HasDerivAt (fun x => τ (x + anglePeriod))
      (deriv τ (θ + anglePeriod)) θ := by
    simpa only [mul_one, Function.comp_def, id] using
      (hτ.contDiff.differentiable_one (θ + anglePeriod)).hasDerivAt.comp θ
        ((hasDerivAt_id θ).add_const anglePeriod)
  
  rw [(funext hper)] at hd
  exact hd.unique ((hτ.contDiff.differentiable_one θ).hasDerivAt.add_const anglePeriod)

/-- The period increment transports the original lower bound to the whole
real line, rather than introducing a new global Jacobian premise. -/
theorem IsC1TraceReparam.lower_global_of_add_period {τ : ℝ → ℝ} {c : ℝ}
    (hτ : IsC1TraceReparam τ c)
    (hper : ∀ θ, τ (θ + anglePeriod) = τ θ + anglePeriod) (θ : ℝ) :
    c ≤ deriv τ θ := by
  let θ' := toIcoMod Real.two_pi_pos 0 θ
  have hθ' : θ' ∈ angleIco := by
    simpa only [zero_add, θ'] using toIcoMod_mem_Ico Real.two_pi_pos 0 θ
  have heq : deriv τ θ' = deriv τ θ := by
    dsimp only [θ']
    rw [toIcoMod, (hτ.deriv_periodic_of_add_period hper).sub_zsmul_eq]
  rw [← heq]
  exact hτ.lower_pointwise θ' (Ico_subset_Icc_self hθ')

theorem localConformalRotateTraceReparam_isC1 {τ : ℝ → ℝ} {c : ℝ}
    (hτ : IsC1TraceReparam τ c)
    (hper : ∀ θ, τ (θ + anglePeriod) = τ θ + anglePeriod) (t : ℝ) :
    IsC1TraceReparam (localConformalRotateTraceReparam τ t) c := by
  obtain ⟨K, hK⟩ := hτ.lipschitz
  refine ⟨?_, ⟨K, ?_⟩, ?_, localConformalRotateTraceReparam_zero τ t, ?_,
    hτ.lower_pos, ?_⟩
  · intro x y hxy
    exact sub_le_sub_right (hτ.monotone ((by bound))) (τ t)
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa [localConformalRotateTraceReparam] using
      hK.dist_le_mul (x + t) (y + t)
  · exact (hτ.contDiff.comp (contDiff_id.add contDiff_const)).sub contDiff_const
  · dsimp [localConformalRotateTraceReparam]
    rw [add_comm anglePeriod t, hper]
    ring
  · apply Eventually.of_forall
    intro θ
    rw [localConformalRotateTraceReparam_deriv hτ]
    exact hτ.lower_global_of_add_period hper (θ + t)

theorem localConformalRotateTraceReparam_add_period {τ : ℝ → ℝ}
    (hper : ∀ θ, τ (θ + anglePeriod) = τ θ + anglePeriod) (t θ : ℝ) :
    localConformalRotateTraceReparam τ t (θ + anglePeriod) =
      localConformalRotateTraceReparam τ t θ + anglePeriod := by
  dsimp [localConformalRotateTraceReparam]
  rw [show θ + anglePeriod + t = (θ + t) + anglePeriod by ring, hper]
  ring

end PolyaNeumann
end
