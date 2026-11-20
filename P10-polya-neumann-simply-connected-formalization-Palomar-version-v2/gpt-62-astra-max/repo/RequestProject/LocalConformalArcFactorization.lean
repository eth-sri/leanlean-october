module

public import RequestProject.LocalConformalArcReparam
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Topology.Order.MonotoneContinuity
public import RequestProject.PlanarNotation

/-!
# Exact factorization through normalized arclength

The precise `normalizedArcReparam` is shown to be an increasing order
isomorphism of the real line. Its period increment and fixed endpoints prove
surjectivity. Composing the actual curve with its genuine inverse constructs
the constant-speed curve and proves the exact factorization.

Nonvanishing velocity gives a pointwise inverse derivative, hence pointwise
constant speed, rather than only an almost-everywhere speed statement. The
supplied-coordinate corollary preserves the actual circle image and proves
interval injectivity from closed-disk injectivity. Boundary orientation and
matching to an arbitrary different parametrization remain separate questions.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped Topology

theorem normalizedArcReparam_strictMono {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ)
    (hnz : ∀ θ, deriv γ θ ≠ 0) : StrictMono (normalizedArcReparam γ) := by
  apply strictMono_of_deriv_pos
  intro θ
  rw [deriv_normalizedArcReparam hγ]
  exact mul_pos (div_pos Real.two_pi_pos (arcLen_period_pos_of_regular hγ hnz))
    (norm_pos_iff.mpr (hnz θ))

/-- The period increment prevents either end of the normalized arclength map
from remaining bounded, and continuity then proves actual surjectivity. -/
theorem normalizedArcReparam_surjective {γ : ℝ → ℂ}
    (hγ : ContDiff ℝ 1 γ) (hper : Function.Periodic γ anglePeriod)
    (hnz : ∀ θ, deriv γ θ ≠ 0) : Function.Surjective (normalizedArcReparam γ) := by
  obtain ⟨c, hτ, _, hperiod⟩ := exists_isC1TraceReparam_normalizedArc hγ hper hnz
  have hbound : ∀ θ, |normalizedArcReparam γ θ - θ| ≤ anglePeriod := by
    refine abs_le_of_periodic
       (fun θ => ?_) (fun x hx => ?_)
    · simp [hperiod]
    · have h0 := hτ.monotone hx.1
      have h2 := hτ.monotone hx.2.le
      rw [hτ.zero] at h0
      rw [hτ.endpoint] at h2
      rw [abs_le]
      grind
  refine hτ.continuous.surjective ?_ ?_
  · refine tendsto_atTop_mono (fun θ => ?_)
      (tendsto_atTop_add_const_right _ (-anglePeriod) tendsto_id)
    have h := hbound θ
    rw [abs_le] at h
    simp only [id]
    linarith
  · refine tendsto_atBot_mono (fun θ => ?_)
      (tendsto_atBot_add_const_right _ anglePeriod tendsto_id)
    have h := hbound θ
    rw [abs_le] at h
    simp
    linarith

section RegularCurve

variable {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ)
    (hper : Function.Periodic γ anglePeriod) (hnz : ∀ θ, deriv γ θ ≠ 0)

/-- The genuine increasing order isomorphism whose forward map is exactly τ. -/
def normalizedArcOrderIso : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective (normalizedArcReparam γ)
    (normalizedArcReparam_strictMono hγ hnz) (normalizedArcReparam_surjective hγ hper hnz)

@[simp] theorem normalizedArcOrderIso_zero : normalizedArcOrderIso hγ hper hnz 0 = 0 :=
  normalizedArcReparam_zero γ

@[simp] theorem normalizedArcOrderIso_endpoint :
    normalizedArcOrderIso hγ hper hnz anglePeriod = anglePeriod :=
  normalizedArcReparam_endpoint (arcLen_period_pos_of_regular hγ hnz)

@[simp] theorem normalizedArcOrderIso_symm_zero :
    (normalizedArcOrderIso hγ hper hnz).symm 0 = 0 := by
  apply (normalizedArcOrderIso hγ hper hnz).injective
  rw [OrderIso.apply_symm_apply, normalizedArcOrderIso_zero]

@[simp] theorem normalizedArcOrderIso_symm_endpoint :
    (normalizedArcOrderIso hγ hper hnz).symm anglePeriod = anglePeriod := by
  apply (normalizedArcOrderIso hγ hper hnz).injective
  rw [OrderIso.apply_symm_apply, normalizedArcOrderIso_endpoint]

section

variable (θ t : ℝ)

theorem normalizedArcOrderIso_add_period :
    normalizedArcOrderIso hγ hper hnz (θ + anglePeriod) =
      normalizedArcOrderIso hγ hper hnz θ + anglePeriod := by
  obtain ⟨c, _, _, hperiod⟩ := exists_isC1TraceReparam_normalizedArc hγ hper hnz
  exact hperiod θ

theorem normalizedArcOrderIso_symm_add_period :
    (normalizedArcOrderIso hγ hper hnz).symm (t + anglePeriod) =
      (normalizedArcOrderIso hγ hper hnz).symm t + anglePeriod := by
  apply (normalizedArcOrderIso hγ hper hnz).injective
  rw [OrderIso.apply_symm_apply, normalizedArcOrderIso_add_period,
    OrderIso.apply_symm_apply]

include t in
/-- The actual curve in its normalized arclength parameter. -/
def normalizedArcCurve : ℂ := γ ((normalizedArcOrderIso hγ hper hnz).symm t)

/-- Exact recovery of the original curve with the precise normalized τ. -/
theorem normalizedArcCurve_factorization :
    γ θ = normalizedArcCurve hγ hper hnz (normalizedArcReparam γ θ) := by
  change γ θ = γ ((normalizedArcOrderIso hγ hper hnz).symm
    (normalizedArcOrderIso hγ hper hnz θ))
  simp

theorem normalizedArcCurve_periodic :
    Function.Periodic (normalizedArcCurve hγ hper hnz) anglePeriod := by
  intro t
  simp [normalizedArcCurve, normalizedArcOrderIso_symm_add_period]
  exact hper _

/-- The true derivative of the inverse map, obtained from its proved inverse
identity and continuity, not assumed as an auxiliary transfer formula. -/
theorem normalizedArcOrderIso_symm_hasDerivAt :
    HasDerivAt (normalizedArcOrderIso hγ hper hnz).symm
      (((anglePeriod / arcLen γ anglePeriod) *
        ‖deriv γ ((normalizedArcOrderIso hγ hper hnz).symm t)‖)⁻¹) t := by
  have hL := arcLen_period_pos_of_regular hγ hnz
  
  apply HasDerivAt.of_local_left_inverse
    (by fun_prop)
    (hasDerivAt_normalizedArcReparam hγ _) (mul_pos (div_pos Real.two_pi_pos hL) (norm_pos_iff.mpr (hnz _))).ne'
  exact Eventually.of_forall (normalizedArcOrderIso hγ hper hnz).apply_symm_apply

theorem normalizedArcCurve_hasDerivAt :
    HasDerivAt (normalizedArcCurve hγ hper hnz)
      ((((anglePeriod / arcLen γ anglePeriod) *
        ‖deriv γ ((normalizedArcOrderIso hγ hper hnz).symm t)‖)⁻¹) •
        deriv γ ((normalizedArcOrderIso hγ hper hnz).symm t)) t :=
  (hγ.differentiable_one _).hasDerivAt.scomp t
    (normalizedArcOrderIso_symm_hasDerivAt hγ hper hnz t)

/-- Constant speed holds at every parameter because the initial velocity is
nonzero everywhere; this is stronger than the usual almost-everywhere statement. -/
theorem normalizedArcCurve_speed :
    ‖deriv (normalizedArcCurve hγ hper hnz) t‖ = arcLen γ anglePeriod / anglePeriod := by
  have hL := arcLen_period_pos_of_regular hγ hnz
  have hv : 0 < ‖deriv γ ((normalizedArcOrderIso hγ hper hnz).symm t)‖ :=
    norm_pos_iff.mpr (hnz _)
  have hp  :=
    inv_pos.mpr (mul_pos (div_pos Real.two_pi_pos hL) hv)
  rw [(normalizedArcCurve_hasDerivAt hγ hper hnz t).deriv, norm_smul,
    Real.norm_eq_abs, abs_of_pos hp]
  grind

end

theorem normalizedArcCurve_lipschitz :
    LipschitzWith (Real.toNNReal (arcLen γ anglePeriod / anglePeriod))
      (normalizedArcCurve hγ hper hnz) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun t => (normalizedArcCurve_hasDerivAt hγ hper hnz t).differentiableAt)
  intro t
  apply NNReal.coe_le_coe.mp
  
  rw [Real.coe_toNNReal _ (div_pos (arcLen_period_pos_of_regular hγ hnz) Real.two_pi_pos).le]
  exact le_of_eq (normalizedArcCurve_speed hγ hper hnz t)

theorem normalizedArcCurve_image_Icc :
    normalizedArcCurve hγ hper hnz '' angleInterval = γ '' angleInterval := by
  change (γ ∘ (normalizedArcOrderIso hγ hper hnz).symm) '' angleInterval = _
  rw [image_comp, OrderIso.image_Icc, normalizedArcOrderIso_symm_zero,
    normalizedArcOrderIso_symm_endpoint]

theorem normalizedArcCurve_injOn (hinj : InjOn γ angleIco) :
    InjOn (normalizedArcCurve hγ hper hnz) angleIco := by
  have hm : ∀ x ∈ angleIco,
      (normalizedArcOrderIso hγ hper hnz).symm x ∈ angleIco := by
    intro x hx
    constructor
    · simpa using (normalizedArcOrderIso hγ hper hnz).symm.monotone hx.1
    · simpa using (normalizedArcOrderIso hγ hper hnz).symm.strictMono hx.2
  intro x hx y hy hxy
  exact (normalizedArcOrderIso hγ hper hnz).symm.injective (hinj (hm x hx) (hm y hy) hxy)

end RegularCurve

/-- Closed-disk injectivity of the actual supplied F proves circle-trace
injectivity on one half-open period by genuine circle-map injectivity. -/
theorem physicalCircleTrace_injOn_of_closedDisk_inj (F : ℂ → ℂ)
    (hinj : InjOn F closedDisk) :
    InjOn (physicalCircleTrace F) angleIco := by
  intro x hx y hy hxy
  have hz := hinj (circleMap_mem_closedBall 0 (by norm_num) x)
    (circleMap_mem_closedBall 0 (by norm_num) y) hxy
  exact injOn_circleMap_of_abs_sub_le' (by positivity)
    (by simp : anglePeriod - 0 ≤ anglePeriod) hx hy hz

end PolyaNeumann

end
