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
noncomputable section
namespace PolyaNeumann

open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

/-- The real linear isometry that rotates the actual complex plane. -/
def localConformalRotationLIE (t : ℝ) : ℂ ≃ₗᵢ[ℝ] ℂ :=
  rotation (Circle.exp t)

/-- The actual rotation, with its coefficient visible for complex calculus. -/
def localConformalRotation (t : ℝ) (z : ℂ) : ℂ := circleMap 0 1 t * z

@[simp] theorem localConformalRotationLIE_apply t z :
    localConformalRotationLIE t z = localConformalRotation t z := by
  simp [localConformalRotationLIE, localConformalRotation, circleMap_zero]

theorem localConformalRotationLIE_coe t :
    (localConformalRotationLIE t : ℂ → ℂ) = localConformalRotation t :=
  funext (localConformalRotationLIE_apply t)


@[simp] theorem localConformalRotation_norm t z :
    ‖localConformalRotation t z‖ = ‖z‖ := by
  simp [localConformalRotation]

local notation "Φ0" => ball 0

@[simp] theorem localConformalRotation_mem_ball t z r :
    localConformalRotation t z ∈ Φ0 r ↔ z ∈ Φ0 r := by
  simp

@[simp] theorem localConformalRotation_mem_closedBall t z r :
    localConformalRotation t z ∈ closedBall 0 r ↔
      z ∈ closedBall 0 r := by
  simp


@[simp] theorem localConformalRotation_neg_right t z :
    localConformalRotation t (localConformalRotation (-t) z) = z := by
  unfold localConformalRotation
  rw [← mul_assoc, circleMap_zero_mul, one_mul, add_neg_cancel]
  simp [circleMap]

theorem localConformalRotation_contDiff t  :
    ContDiff ℝ n (localConformalRotation t) := by
  rw [← localConformalRotationLIE_coe]
  exact (localConformalRotationLIE t).contDiff

theorem localConformalRotation_hasDerivAt t z :
    HasDerivAt (localConformalRotation t) (circleMap 0 1 t) z :=
  hasDerivAt_const_mul (circleMap 0 1 t)

theorem localConformalRotation_image_ball t r :
    localConformalRotation t '' Φ0 r = Φ0 r := by
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact (localConformalRotation_mem_ball t z r).mpr hz
  · intro z hz
    exact ⟨localConformalRotation (-t) z,
      (localConformalRotation_mem_ball (-t) z r).mpr hz,
      localConformalRotation_neg_right t z⟩

theorem localConformalRotation_image_closedBall t r :
    localConformalRotation t '' closedBall 0 r = closedBall 0 r := by
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact (localConformalRotation_mem_closedBall t z r).mpr hz
  · intro z hz
    exact ⟨localConformalRotation (-t) z,
      (localConformalRotation_mem_closedBall (-t) z r).mpr hz,
      localConformalRotation_neg_right t z⟩

/-- Rotation of the given coordinate map, with no replacement of its image. -/
def localConformalRotate (F : ℂ → ℂ) (t : ℝ) : ℂ → ℂ :=
  F ∘ localConformalRotation t

@[simp] theorem localConformalRotate_apply F t z :
    localConformalRotate F t z = F (circleMap 0 1 t * z) := rfl

theorem localConformalRotate_image_ball F t r :
    localConformalRotate F t '' Φ0 r = F '' Φ0 r := by
  calc
    _ = _ :=
      (image_image F (localConformalRotation t) _).symm
    _ = _ := by rw [localConformalRotation_image_ball]

theorem localConformalRotate_image_closedBall F t r :
    localConformalRotate F t '' closedBall 0 r = F '' closedBall 0 r := by
  calc
    _ = _ :=
      (image_image F (localConformalRotation t) _).symm
    _ = _ := by rw [localConformalRotation_image_closedBall]

theorem localConformalRotate_contDiffOn  
     (hF : ContDiffOn ℝ n F (Φ0 r)) t :
    ContDiffOn ℝ n (localConformalRotate F t) (Φ0 r) :=
  hF.comp (localConformalRotation_contDiff t).contDiffOn
    (fun z hz => (localConformalRotation_mem_ball t z r).mpr hz)

theorem localConformalRotate_holomorphic  
    (hF : DifferentiableOn ℂ F (Φ0 r)) t :
    DifferentiableOn ℂ (localConformalRotate F t) (Φ0 r) :=
  hF.comp (fun z _ => (localConformalRotation_hasDerivAt t z).differentiableAt.differentiableWithinAt)
    (fun z hz => (localConformalRotation_mem_ball t z r).mpr hz)

theorem localConformalRotate_injOn_closedBall  
    (hF : InjOn F (closedBall 0 r)) t :
    InjOn (localConformalRotate F t) (closedBall 0 r) := by
  intro z hz w hw hzw
  have h_inl z : localConformalRotation (-t) (localConformalRotation t z) = z := by
    unfold localConformalRotation
    rw [← mul_assoc, circleMap_zero_mul, one_mul, neg_add_cancel]
    simp [circleMap]
  exact (Function.LeftInverse.injective h_inl) (hF
    ((localConformalRotation_mem_closedBall t z r).mpr hz)
    ((localConformalRotation_mem_closedBall t w r).mpr hw) hzw)

theorem localConformalRotate_deriv_norm  
    (hF : DifferentiableOn ℂ F (Φ0 r)) t
     (hz : z ∈ Φ0 r) :
    ‖deriv (localConformalRotate F t) z‖ = ‖deriv F (localConformalRotation t z)‖ := by
  rw [(show HasDerivAt (localConformalRotate F t) (deriv F (localConformalRotation t z) * circleMap 0 1 t) z from ((hF.differentiableAt (isOpen_ball.mem_nhds ((localConformalRotation_mem_ball t z r).mpr hz))).hasDerivAt.comp z (localConformalRotation_hasDerivAt t z))).deriv]
  simp

local notation "Φ1" => ball 0 1

theorem localConformalRotate_lower_deriv_bound  
    (hhol : DifferentiableOn ℂ F (Φ1))
    (hC : ∀ z ∈ Φ1, 1 ≤ C * ‖deriv F z‖ ^ 2) t :
    ∀ z ∈ Φ1, 1 ≤ C * ‖deriv (localConformalRotate F t) z‖ ^ 2 := by
  intro z hz
  rw [localConformalRotate_deriv_norm hhol t hz]
  exact hC _ ((localConformalRotation_mem_ball t z 1).mpr hz)

theorem localConformalRotate_upper_differential_bound  (hR : 1 < R)
    F (hFs : ContDiffOn ℝ ∞ F (Φ0 R))
    (hhol : DifferentiableOn ℂ F (Φ1)) 
    (hK : ∀ z ∈ Φ1, ‖fderiv ℝ F z 1‖ ≤ K) t :
    ∀ z ∈ Φ1, ‖fderiv ℝ (localConformalRotate F t) z 1‖ ≤ K := by
  intro z hz
  rw [show ‖fderiv ℝ (localConformalRotate F t) z 1‖ = ‖fderiv ℝ F (localConformalRotation t z) 1‖ by
    have hzt := (localConformalRotation_mem_closedBall t z 1).mpr (ball_subset_closedBall hz)
    have h_inl v : fderiv ℝ (localConformalRotate F t) z v = fderiv ℝ F (localConformalRotation t z) (localConformalRotation t v) := by
      change fderiv ℝ (F ∘ localConformalRotation t) z v = _
      rw [(((hFs.contDiffAt (isOpen_ball.mem_nhds (closedBall_subset_ball hR hzt))).differentiableAt (by simp)).hasFDerivAt.comp z (by
        have h : HasFDerivAt (localConformalRotationLIE t)
            (localConformalRotationLIE t : ℂ →L[ℝ] ℂ) z :=
          (localConformalRotationLIE t : ℂ →L[ℝ] ℂ).hasFDerivAt
        rw [localConformalRotationLIE_coe] at h
        exact h)).fderiv]
      simp only [ContinuousLinearMap.comp_apply]
      change fderiv ℝ F (localConformalRotation t z) (localConformalRotationLIE t v) = _
      rw [localConformalRotationLIE_apply]
    rw [h_inl,
      localConformal_fderiv_closedDisk hR F hFs hhol hzt]
    simp [localConformalRotation]]
  exact hK _ ((localConformalRotation_mem_ball t z 1).mpr hz)

/-- The actual new boundary origin is the old point at parameter `t`. -/
theorem physicalCircleTrace_localConformalRotate F t θ :
    physicalCircleTrace (localConformalRotate F t) θ = physicalCircleTrace F (θ + t) := by
  simp [physicalCircleTrace, circleMap_zero_mul, add_comm t θ]

theorem physicalCircleTrace_localConformalRotate_lipschitz
      (hΓ : LipschitzWith K (physicalCircleTrace F)) t :
    LipschitzWith K (physicalCircleTrace (localConformalRotate F t)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa [physicalCircleTrace_localConformalRotate, Real.dist_eq] using
    hΓ.dist_le_mul (x + t) (y + t)


def localConformalRotatePartialHomeomorph (e : OpenPartialHomeomorph ℂ ℂ) (t : ℝ) :
    OpenPartialHomeomorph ℂ ℂ :=
  (localConformalRotationLIE t).toHomeomorph.transOpenPartialHomeomorph e

theorem localConformalRotatePartialHomeomorph_source
    e t :
    (localConformalRotatePartialHomeomorph e t).source =
      localConformalRotation t ⁻¹' e.source := by
  ext z
  change localConformalRotationLIE t z ∈ e.source ↔ _
  rw [localConformalRotationLIE_apply]
  rfl

@[simp] theorem localConformalRotatePartialHomeomorph_target
    e t :
    (localConformalRotatePartialHomeomorph e t).target = e.target := rfl

theorem localConformalRotatePartialHomeomorph_coe 
    e (he : ↑e = F) t :
    (localConformalRotatePartialHomeomorph e t : ℂ → ℂ) = localConformalRotate F t := by
  funext z
  have h_inl e t z : localConformalRotatePartialHomeomorph e t z = e (localConformalRotation t z) := by
    change e (localConformalRotationLIE t z) = _
    rw [localConformalRotationLIE_apply]
  rw [h_inl, he]
  rfl

theorem localConformalRotatePartialHomeomorph_closedDisk_source
    e
    (hsource : closedBall 0 1 ⊆ e.source) t :
    closedBall 0 1 ⊆ (localConformalRotatePartialHomeomorph e t).source := by
  rw [localConformalRotatePartialHomeomorph_source]
  intro z hz
  exact hsource ((localConformalRotation_mem_closedBall t z 1).mpr hz)

theorem localConformalRotatePartialHomeomorph_smoothInverse
    e
    (hes : ContDiffOn ℝ ∞ e.symm e.target) t :
    ContDiffOn ℝ ∞ (localConformalRotatePartialHomeomorph e t).symm
      (localConformalRotatePartialHomeomorph e t).target := by
  have h_inl w : (localConformalRotatePartialHomeomorph e t).symm w = localConformalRotation (-t) (e.symm w) := by
    change (localConformalRotationLIE t).symm (e.symm w) = _
    have h_inl t : (localConformalRotationLIE t).symm = localConformalRotationLIE (-t) := by simp [localConformalRotationLIE]
    rw [h_inl, localConformalRotationLIE_apply]
  rw [localConformalRotatePartialHomeomorph_target, funext h_inl]
  exact (localConformalRotation_contDiff (-t)).comp_contDiffOn hes

/-- The smooth inverse forces the actual closed-disk real differential to
be nonzero, including at the boundary. -/
theorem localConformalRotation_closedDifferential_ne_zero_of_inverse
     (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ ∞ F (Φ0 R))
    (e : OpenPartialHomeomorph ℂ ℂ) (he : e = F)
    (hsource : closedBall 0 1 ⊆ e.source)
    (hes : ContDiffOn ℝ ∞ e.symm e.target) :
    ∀ z ∈ closedBall 0 1, fderiv ℝ F z 1 ≠ 0 := by
  intro z hz
  have hzs := hsource hz
  have hid : HasFDerivAt (fun x => x)
      ((fderiv ℝ e.symm (F z)).comp (fderiv ℝ F z)) z := by
    apply ((((hes.contDiffAt (e.open_target.mem_nhds (by
      rw [← he]
      exact e.mapsTo hzs))).differentiableAt (by simp)).hasFDerivAt).comp z (((hFs.contDiffAt (isOpen_ball.mem_nhds (closedBall_subset_ball hR hz))).differentiableAt (by simp)).hasFDerivAt)).congr_of_eventuallyEq
    filter_upwards [e.open_source.mem_nhds hzs] with x hx
    rw [← he]
    exact (e.left_inv hx).symm
  have hval := congrArg (fun A : ℂ →L[ℝ] ℂ => A 1) (hid.unique (hasFDerivAt_id z))
  change fderiv ℝ e.symm (F z) (fderiv ℝ F z 1) = 1 at hval
  intro hzero
  rw [hzero, map_zero] at hval
  exact zero_ne_one hval

/-- Rebase the genuine parameter lift at the selected conformal origin. -/
def localConformalRotateTraceReparam (τ : ℝ → ℝ) (t : ℝ) (θ : ℝ) : ℝ :=
  τ (θ + t) - τ t

theorem localConformalRotateTraceReparam_deriv  
    (hτ : IsC1TraceReparam τ c) t θ :
    deriv (localConformalRotateTraceReparam τ t) θ = deriv τ (θ + t) :=
  (show HasDerivAt (localConformalRotateTraceReparam τ t) (deriv τ (θ + t)) θ by
    show HasDerivAt (fun θ => τ (θ + t) - τ t) _ θ
    simpa [Function.comp_def] using
      (((hτ.contDiff.differentiable_one (θ + t)).hasDerivAt.comp θ
        ((hasDerivAt_id θ).add_const t)).sub_const (τ t))).deriv

/-- C¹ continuity upgrades the original AE lower bound on its closed cut
interval to a true pointwise bound on that interval. -/
theorem IsC1TraceReparam.lower_pointwise  
    (hτ : IsC1TraceReparam τ c) :
    ∀ θ ∈ Icc 0 (2 * Real.pi), c ≤ deriv τ θ := by
  have heq : EqOn (fun θ => max c (deriv τ θ)) (deriv τ)
      (Icc 0 (2 * Real.pi)) := by
    apply Measure.eqOn_of_ae_eq
      (hτ.lower_ae.mono (fun θ hθ => max_eq_right hθ))
      (continuous_const.max hτ.contDiff.continuous_deriv_one).continuousOn
      hτ.contDiff.continuous_deriv_one.continuousOn
    simp [closure_interior_Icc (ne_of_lt Real.two_pi_pos)]
  intro θ hθ
  rw [← heq hθ]
  exact le_max_left _ _

theorem IsC1TraceReparam.deriv_periodic_of_add_period  
    (hτ : IsC1TraceReparam τ c)
    (hper : ∀ θ, τ (θ + 2 * Real.pi) = τ θ + 2 * Real.pi) :
    Function.Periodic (deriv τ) (2 * Real.pi) := by
  intro θ
  have hd : HasDerivAt (fun x => τ (x + 2 * Real.pi))
      (deriv τ (θ + 2 * Real.pi)) θ := by
    simpa [Function.comp_def] using
      (hτ.contDiff.differentiable_one (θ + 2 * Real.pi)).hasDerivAt.comp θ
        ((hasDerivAt_id θ).add_const (2 * Real.pi))
  rw [funext hper] at hd
  exact hd.unique ((hτ.contDiff.differentiable_one θ).hasDerivAt.add_const (2 * Real.pi))

/-- The period increment transports the original lower bound to the whole
real line, rather than introducing a new global Jacobian premise. -/
theorem IsC1TraceReparam.lower_global_of_add_period  
    (hτ : IsC1TraceReparam τ c)
    (hper : ∀ θ, τ (θ + 2 * Real.pi) = τ θ + 2 * Real.pi) θ :
    c ≤ deriv τ θ := by
  let θ' := toIcoMod Real.two_pi_pos 0 θ
  rw [← (show deriv τ θ' = deriv τ θ by
    dsimp only [θ']
    rw [toIcoMod, (hτ.deriv_periodic_of_add_period hper).sub_zsmul_eq])]
  exact hτ.lower_pointwise θ' (Ico_subset_Icc_self (by
    simpa [θ'] using toIcoMod_mem_Ico Real.two_pi_pos 0 θ))

theorem localConformalRotateTraceReparam_isC1  
    (hτ : IsC1TraceReparam τ c)
    (hper : ∀ θ, τ (θ + 2 * Real.pi) = τ θ + 2 * Real.pi) t :
    IsC1TraceReparam (localConformalRotateTraceReparam τ t) c := by
  obtain ⟨K, hK⟩ := hτ.lipschitz
  refine ⟨?_, ⟨K, ?_⟩, ?_, show localConformalRotateTraceReparam τ t 0 = 0 by
    simp [localConformalRotateTraceReparam], ?_,
    hτ.lower_pos, ?_⟩
  · intro x y hxy
    exact sub_le_sub_right (hτ.monotone (add_le_add hxy (le_refl t))) (τ t)
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa [localConformalRotateTraceReparam, Real.dist_eq] using
      hK.dist_le_mul (x + t) (y + t)
  · exact (hτ.contDiff.comp (contDiff_id.add contDiff_const)).sub contDiff_const
  · dsimp only [localConformalRotateTraceReparam]
    rw [add_comm (2 * Real.pi) t, hper]
    ring
  · apply Eventually.of_forall
    intro θ
    rw [localConformalRotateTraceReparam_deriv hτ]
    exact hτ.lower_global_of_add_period hper (θ + t)

theorem localConformalRotateTraceReparam_add_period 
    (hper : ∀ θ, τ (θ + 2 * Real.pi) = τ θ + 2 * Real.pi) t θ :
    localConformalRotateTraceReparam τ t (θ + 2 * Real.pi) =
      localConformalRotateTraceReparam τ t θ + 2 * Real.pi := by
  dsimp only [localConformalRotateTraceReparam]
  rw [show θ + 2 * Real.pi + t = θ + t + 2 * Real.pi by ring, hper]
  ring

end PolyaNeumann
end
