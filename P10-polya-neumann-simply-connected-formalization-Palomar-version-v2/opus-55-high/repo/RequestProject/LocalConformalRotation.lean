module

public import RequestProject.LocalConformalArcReparam
public import RequestProject.BoundaryOrigin
public import RequestProject.BoundaryParamShift
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.Topology.OpenPartialHomeomorph.Composition
public import Mathlib.MeasureTheory.Measure.OpenPos

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
namespace PolyaNeumann

open Set Metric MeasureTheory Filter
open scoped Topology

/-- The real linear isometry that rotates the actual complex plane. -/
def localConformalRotationLIE (t : ℝ) : ℂ ≃ₗᵢ[ℝ] ℂ :=
  rotation (Circle.exp t)

/-- The actual rotation, with its coefficient visible for complex calculus. -/
def localConformalRotation (t : ℝ) (z : ℂ) : ℂ := circleMap 0 1 t * z

@[simp] theorem localConformalRotationLIE_apply (t : ℝ) (z : ℂ) :
    localConformalRotationLIE t z = localConformalRotation t z := by
  simp [localConformalRotationLIE, localConformalRotation, circleMap_zero]

theorem localConformalRotationLIE_coe (t : ℝ) :
    localConformalRotationLIE t = localConformalRotation t :=
  funext (localConformalRotationLIE_apply t)


@[simp] theorem localConformalRotation_norm (t : ℝ) (z : ℂ) :
    ‖localConformalRotation t z‖ = ‖z‖ := by
  simp [localConformalRotation]

@[simp] theorem localConformalRotation_mem_ball (t : ℝ) (z : ℂ) (r : ℝ) :
    localConformalRotation t z ∈ ball 0 r ↔ z ∈ ball 0 r := by
  simp 

@[simp] theorem localConformalRotation_mem_closedBall (t : ℝ) (z : ℂ) (r : ℝ) :
    localConformalRotation t z ∈ closedBall 0 r ↔
      z ∈ closedBall 0 r := by
  simp 


@[simp] theorem localConformalRotation_neg_left (t : ℝ) (z : ℂ) :
    localConformalRotation (-t) (localConformalRotation t z) = z := by
  unfold localConformalRotation
  rw [← mul_assoc, circleMap_zero_mul]
  simp [circleMap]

@[simp] theorem localConformalRotation_neg_right (t : ℝ) (z : ℂ) :
    localConformalRotation t (localConformalRotation (-t) z) = z := by
  unfold localConformalRotation
  rw [← mul_assoc, circleMap_zero_mul]
  simp [circleMap]

theorem localConformalRotation_injective (t : ℝ) :
    Function.Injective (localConformalRotation t) :=
  Function.LeftInverse.injective (localConformalRotation_neg_left t)

theorem localConformalRotation_contDiff (t : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (localConformalRotation t) := by
  rw [← localConformalRotationLIE_coe]
  fun_prop

theorem localConformalRotation_hasFDerivAt (t : ℝ) (z : ℂ) :
    HasFDerivAt (localConformalRotation t)
      (localConformalRotationLIE t : ℂ →L[ℝ] ℂ) z := by
  have h : HasFDerivAt (localConformalRotationLIE t)
      (localConformalRotationLIE t : ℂ →L[ℝ] ℂ) z :=
    (localConformalRotationLIE t).hasFDerivAt
  simp_all [localConformalRotationLIE_coe]

theorem localConformalRotation_hasDerivAt (t : ℝ) (z : ℂ) :
    HasDerivAt (localConformalRotation t) (circleMap 0 1 t) z :=
  hasDerivAt_const_mul (circleMap 0 1 t)

theorem localConformalRotation_image_ball (t : ℝ) (r : ℝ) :
    localConformalRotation t '' ball 0 r = ball 0 r := by
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    simp_all
  · intro z hz
    exact ⟨localConformalRotation (-t) z,
      (localConformalRotation_mem_ball (-t) z r).mpr hz,
      localConformalRotation_neg_right t z⟩

theorem localConformalRotation_image_closedBall (t : ℝ) (r : ℝ) :
    localConformalRotation t '' closedBall 0 r = closedBall 0 r := by
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    simp_all
  · intro z hz
    exact ⟨localConformalRotation (-t) z,
      (localConformalRotation_mem_closedBall (-t) z r).mpr hz,
      localConformalRotation_neg_right t z⟩

/-- Rotation of the given coordinate map, with no replacement of its image. -/
def localConformalRotate (F : ℂ → ℂ) (t : ℝ) : ℂ → ℂ :=
  F ∘ localConformalRotation t

@[simp] theorem localConformalRotate_apply (F : ℂ → ℂ) (t : ℝ) (z : ℂ) :
    localConformalRotate F t z = F (circleMap 0 1 t * z) := rfl

theorem localConformalRotate_image_ball (F : ℂ → ℂ) (t r : ℝ) :
    localConformalRotate F t '' ball 0 r = F '' ball 0 r := by
  calc
    _ = F '' (localConformalRotation t '' ball 0 r) :=
      (image_image F (localConformalRotation t) _).symm
    _ = _ := by rw [localConformalRotation_image_ball]

theorem localConformalRotate_image_closedBall (F : ℂ → ℂ) (t r : ℝ) :
    localConformalRotate F t '' closedBall 0 r = F '' closedBall 0 r := by
  calc
    _ = F '' (localConformalRotation t '' closedBall 0 r) :=
      (image_image F (localConformalRotation t) _).symm
    _ = _ := by rw [localConformalRotation_image_closedBall]

theorem localConformalRotate_contDiffOn {F : ℂ → ℂ} {r : ℝ}
    {n : WithTop ℕ∞} (hF : ContDiffOn ℝ n F (ball 0 r)) (t : ℝ) :
    ContDiffOn ℝ n (localConformalRotate F t) (ball 0 r) :=
  hF.comp (localConformalRotation_contDiff t).contDiffOn
    (fun z hz => (localConformalRotation_mem_ball t z r).mpr hz)

theorem localConformalRotate_holomorphic {F : ℂ → ℂ} {r : ℝ}
    (hF : DifferentiableOn ℂ F (ball 0 r)) (t : ℝ) :
    DifferentiableOn ℂ (localConformalRotate F t) (ball 0 r) :=
  hF.comp (fun z _ => (localConformalRotation_hasDerivAt t z).differentiableAt.differentiableWithinAt)
    (fun z hz => (localConformalRotation_mem_ball t z r).mpr hz)

theorem localConformalRotate_injOn_closedBall {F : ℂ → ℂ} {r : ℝ}
    (hF : InjOn F (closedBall 0 r)) (t : ℝ) :
    InjOn (localConformalRotate F t) (closedBall 0 r) := by
  intro z hz w hw hzw
  exact localConformalRotation_injective t (hF
    ((localConformalRotation_mem_closedBall t z r).mpr hz)
    ((localConformalRotation_mem_closedBall t w r).mpr hw) hzw)

theorem localConformalRotate_hasDerivAt {F : ℂ → ℂ} (t : ℝ) {z : ℂ}
    (hF : DifferentiableAt ℂ F (localConformalRotation t z)) :
    HasDerivAt (localConformalRotate F t)
      (deriv F (localConformalRotation t z) * circleMap 0 1 t) z := hF.hasDerivAt.comp z (localConformalRotation_hasDerivAt t z)

theorem localConformalRotate_deriv_norm {F : ℂ → ℂ} {r : ℝ}
    (hF : DifferentiableOn ℂ F (ball 0 r)) (t : ℝ)
    {z : ℂ} (hz : z ∈ ball 0 r) :
    ‖deriv (localConformalRotate F t) z‖ = ‖deriv F (localConformalRotation t z)‖ := by
  simp [(localConformalRotate_hasDerivAt t     (hF.differentiableAt (isOpen_ball.mem_nhds       ((localConformalRotation_mem_ball t z r).mpr hz)))).deriv]

theorem localConformalRotate_lower_deriv_bound {F : ℂ → ℂ} {C : ℝ}
    (hhol : DifferentiableOn ℂ F (ball 0 1))
    (hC : ∀ z ∈ ball 0 1, 1 ≤ C * ‖deriv F z‖ ^ 2) (t : ℝ) :
    ∀ z ∈ ball 0 1, 1 ≤ C * ‖deriv (localConformalRotate F t) z‖ ^ 2 := by
  intro z hz
  simp_all [localConformalRotate_deriv_norm hhol t hz]

theorem localConformalRotate_fderiv {F : ℂ → ℂ} (t : ℝ) {z : ℂ}
    (hF : DifferentiableAt ℝ F (localConformalRotation t z)) (v : ℂ) :
    fderiv ℝ (localConformalRotate F t) z v =
      fderiv ℝ F (localConformalRotation t z) (localConformalRotation t v) := by
  change fderiv ℝ (F ∘ localConformalRotation t) z v = _
  simp [(hF.hasFDerivAt.comp z (localConformalRotation_hasFDerivAt t z)).fderiv]

theorem localConformalRotate_closedDifferential_norm {R : ℝ} (hR : 1 < R)
    (F : ℂ → ℂ) (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball 0 R))
    (hhol : DifferentiableOn ℂ F (ball 0 1)) (t : ℝ)
    {z : ℂ} (hz : z ∈ closedBall 0 1) :
    ‖fderiv ℝ (localConformalRotate F t) z 1‖ =
      ‖fderiv ℝ F (localConformalRotation t z) 1‖ := by
  have hzt := (localConformalRotation_mem_closedBall t z 1).mpr hz
  rw [localConformalRotate_fderiv t
    ((hFs.contDiffAt (isOpen_ball.mem_nhds (closedBall_subset_ball hR hzt))).differentiableAt
      (by simp)),
    localConformal_fderiv_closedDisk hR F hFs hhol hzt]
  simp 

theorem localConformalRotate_upper_differential_bound {R : ℝ} (hR : 1 < R)
    (F : ℂ → ℂ) (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball 0 R))
    (hhol : DifferentiableOn ℂ F (ball 0 1)) {K : ℝ}
    (hK : ∀ z ∈ ball 0 1, ‖fderiv ℝ F z 1‖ ≤ K) (t : ℝ) :
    ∀ z ∈ ball 0 1, ‖fderiv ℝ (localConformalRotate F t) z 1‖ ≤ K := by
  intro z hz
  simp_all [localConformalRotate_closedDifferential_norm hR F hFs hhol t     (ball_subset_closedBall hz)]

/-- The actual new boundary origin is the old point at parameter `t`. -/
theorem physicalCircleTrace_localConformalRotate (F : ℂ → ℂ) (t θ : ℝ) :
    physicalCircleTrace (localConformalRotate F t) θ = physicalCircleTrace F (θ + t) := by
  simp [physicalCircleTrace, circleMap_zero_mul, add_comm t θ]

theorem physicalCircleTrace_localConformalRotate_lipschitz
    {F : ℂ → ℂ} {K : NNReal} (hΓ : LipschitzWith K (physicalCircleTrace F)) (t : ℝ) :
    LipschitzWith K (physicalCircleTrace (localConformalRotate F t)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa [physicalCircleTrace_localConformalRotate] using
    hΓ.dist_le_mul (x + t) (y + t)


@[simp] theorem localConformalRotationLIE_symm (t : ℝ) :
    (localConformalRotationLIE t).symm = localConformalRotationLIE (-t) := by
  simp [localConformalRotationLIE]

/-- Precomposition of the supplied actual local homeomorphism by rotation. -/
def localConformalRotatePartialHomeomorph (e : OpenPartialHomeomorph ℂ ℂ) (t : ℝ) :
    OpenPartialHomeomorph ℂ ℂ :=
  (localConformalRotationLIE t).toHomeomorph.transOpenPartialHomeomorph e

@[simp] theorem localConformalRotatePartialHomeomorph_apply
    (e : OpenPartialHomeomorph ℂ ℂ) (t : ℝ) (z : ℂ) :
    localConformalRotatePartialHomeomorph e t z = e (localConformalRotation t z) := by
  change e (localConformalRotationLIE t z) = _
  rw [localConformalRotationLIE_apply]

@[simp] theorem localConformalRotatePartialHomeomorph_symm_apply
    (e : OpenPartialHomeomorph ℂ ℂ) (t : ℝ) (w : ℂ) :
    (localConformalRotatePartialHomeomorph e t).symm w =
      localConformalRotation (-t) (e.symm w) := by
  change (localConformalRotationLIE t).symm (e.symm w) = _
  rw [localConformalRotationLIE_symm, localConformalRotationLIE_apply]

theorem localConformalRotatePartialHomeomorph_source
    (e : OpenPartialHomeomorph ℂ ℂ) (t : ℝ) :
    (localConformalRotatePartialHomeomorph e t).source =
      localConformalRotation t ⁻¹' e.source := by
  ext z
  change localConformalRotationLIE t z ∈ e.source ↔ _
  norm_num

@[simp] theorem localConformalRotatePartialHomeomorph_target
    (e : OpenPartialHomeomorph ℂ ℂ) (t : ℝ) :
    (localConformalRotatePartialHomeomorph e t).target = e.target := rfl

theorem localConformalRotatePartialHomeomorph_coe {F : ℂ → ℂ}
    (e : OpenPartialHomeomorph ℂ ℂ) (he : e = F) (t : ℝ) :
    localConformalRotatePartialHomeomorph e t = localConformalRotate F t := by
  funext z
  rw [localConformalRotatePartialHomeomorph_apply, he]
  rfl

theorem localConformalRotatePartialHomeomorph_closedDisk_source
    (e : OpenPartialHomeomorph ℂ ℂ)
    (hsource : closedBall 0 1 ⊆ e.source) (t : ℝ) :
    closedBall 0 1 ⊆ (localConformalRotatePartialHomeomorph e t).source := by
  rw [localConformalRotatePartialHomeomorph_source]
  intro z hz
  exact hsource ((localConformalRotation_mem_closedBall t z 1).mpr hz)

theorem localConformalRotatePartialHomeomorph_smoothInverse
    (e : OpenPartialHomeomorph ℂ ℂ)
    (hes : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target) (t : ℝ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (localConformalRotatePartialHomeomorph e t).symm
      (localConformalRotatePartialHomeomorph e t).target := by
  rw [funext (localConformalRotatePartialHomeomorph_symm_apply e t)]
  exact (localConformalRotation_contDiff (-t)).comp_contDiffOn hes

/-- The smooth inverse forces the actual closed-disk real differential to
be nonzero, including at the boundary. -/
theorem localConformalRotation_closedDifferential_ne_zero_of_inverse
    {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball 0 R))
    (e : OpenPartialHomeomorph ℂ ℂ) (he : e = F)
    (hsource : closedBall 0 1 ⊆ e.source)
    (hes : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target) :
    ∀ z ∈ closedBall 0 1, fderiv ℝ F z 1 ≠ 0 := by
  intro z hz
  have hzs := hsource hz
  have hid : HasFDerivAt (fun x  => x)
      ((fderiv ℝ e.symm (F z)).comp (fderiv ℝ F z)) z := by
    apply (((hes.contDiffAt (e.open_target.mem_nhds (by
    rw [← he]
    exact e.mapsTo hzs))).differentiableAt
    (by simp)).hasFDerivAt.comp z ((hFs.contDiffAt (isOpen_ball.mem_nhds (closedBall_subset_ball hR hz))).differentiableAt
    (by simp)).hasFDerivAt).congr_of_eventuallyEq
    filter_upwards [e.open_source.mem_nhds hzs] with x hx
    rw [← he]
    exact (e.left_inv hx).symm
  have hval := congrArg (fun A  => A 1) (hid.unique (hasFDerivAt_id z))
  intro hzero
  simp_all

/-- Rebase the genuine parameter lift at the selected conformal origin. -/
def localConformalRotateTraceReparam (τ : ℝ → ℝ) (t : ℝ) (θ : ℝ) : ℝ :=
  τ (θ + t) - τ t

@[simp] theorem localConformalRotateTraceReparam_zero (τ : ℝ → ℝ) (t : ℝ) :
    localConformalRotateTraceReparam τ t 0 = 0 := by
  simp [localConformalRotateTraceReparam]

theorem localConformalRotateTraceReparam_hasDerivAt {τ : ℝ → ℝ} {c : ℝ}
    (hτ : IsC1TraceReparam τ c) (t θ : ℝ) :
    HasDerivAt (localConformalRotateTraceReparam τ t) (deriv τ (θ + t)) θ := by
  show HasDerivAt (fun θ => τ (θ + t) - τ t) _ θ
  simpa only [mul_one, Function.comp_def, id] using
    (((hτ.contDiff.differentiable_one (θ + t)).hasDerivAt.comp θ
      ((hasDerivAt_id θ).add_const t)).sub_const (τ t))

theorem localConformalRotateTraceReparam_deriv {τ : ℝ → ℝ} {c : ℝ}
    (hτ : IsC1TraceReparam τ c) (t θ : ℝ) :
    deriv (localConformalRotateTraceReparam τ t) θ = deriv τ (θ + t) :=
  (localConformalRotateTraceReparam_hasDerivAt hτ t θ).deriv

/-- C¹ continuity upgrades the original AE lower bound on its closed cut
interval to a true pointwise bound on that interval. -/
theorem IsC1TraceReparam.lower_pointwise {τ : ℝ → ℝ} {c : ℝ}
    (hτ : IsC1TraceReparam τ c) :
    ∀ θ ∈ Icc 0 (2 * Real.pi), c ≤ deriv τ θ := by
  have heq : EqOn (fun θ => max c (deriv τ θ)) (deriv τ)
      (Icc 0 (2 * Real.pi)) := by
    apply Measure.eqOn_of_ae_eq
      (hτ.lower_ae.mono (fun θ hθ => max_eq_right hθ))
      (continuous_const.max hτ.contDiff.continuous_deriv_one).continuousOn
      hτ.contDiff.continuous_deriv_one.continuousOn
    norm_num
  grind

theorem IsC1TraceReparam.deriv_periodic_of_add_period {τ : ℝ → ℝ} {c : ℝ}
    (hτ : IsC1TraceReparam τ c)
    (hper : ∀ θ, τ (θ + 2 * Real.pi) = τ θ + 2 * Real.pi) :
    Function.Periodic (deriv τ) (2 * Real.pi) := by
  intro θ
  have hd : HasDerivAt (fun x => τ (x + 2 * Real.pi))
      (deriv τ (θ + 2 * Real.pi)) θ := by
    simpa only [mul_one, Function.comp_def, id] using
      (hτ.contDiff.differentiable_one (θ + 2 * Real.pi)).hasDerivAt.comp θ
        ((hasDerivAt_id θ).add_const (2 * Real.pi))
  rw [funext hper] at hd
  exact hd.unique ((hτ.contDiff.differentiable_one θ).hasDerivAt.add_const (2 * Real.pi))

/-- The period increment transports the original lower bound to the whole
real line, rather than introducing a new global Jacobian premise. -/
theorem IsC1TraceReparam.lower_global_of_add_period {τ : ℝ → ℝ} {c : ℝ}
    (hτ : IsC1TraceReparam τ c)
    (hper : ∀ θ, τ (θ + 2 * Real.pi) = τ θ + 2 * Real.pi) (θ : ℝ) :
    c ≤ deriv τ θ := by
  let θ' := toIcoMod Real.two_pi_pos 0 θ
  have heq : deriv τ θ' = deriv τ θ := by
    dsimp only [θ']
    rw [toIcoMod, (hτ.deriv_periodic_of_add_period hper).sub_zsmul_eq]
  rw [← heq]
  exact hτ.lower_pointwise θ' (Ico_subset_Icc_self (by
    simpa only [zero_add] using toIcoMod_mem_Ico Real.two_pi_pos 0 θ))

theorem localConformalRotateTraceReparam_isC1 {τ : ℝ → ℝ} {c : ℝ}
    (hτ : IsC1TraceReparam τ c)
    (hper : ∀ θ, τ (θ + 2 * Real.pi) = τ θ + 2 * Real.pi) (t : ℝ) :
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
  · simp [localConformalRotateTraceReparam, add_comm (2 * Real.pi) t, hper]
  · apply Eventually.of_forall
    intro θ
    rw [localConformalRotateTraceReparam_deriv hτ]
    exact hτ.lower_global_of_add_period hper (θ + t)

theorem localConformalRotateTraceReparam_add_period {τ : ℝ → ℝ}
    (hper : ∀ θ, τ (θ + 2 * Real.pi) = τ θ + 2 * Real.pi) (t θ : ℝ) :
    localConformalRotateTraceReparam τ t (θ + 2 * Real.pi) =
      localConformalRotateTraceReparam τ t θ + 2 * Real.pi := by
  dsimp only [localConformalRotateTraceReparam]
  grind

end PolyaNeumann
end
