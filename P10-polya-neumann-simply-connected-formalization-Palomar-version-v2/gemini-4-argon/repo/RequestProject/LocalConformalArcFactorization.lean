module

public import RequestProject.LocalConformalArcReparam
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Topology.Order.MonotoneContinuity

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


noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped Topology

theorem normalizedArcReparam_surjective 
    (hγ : ContDiff ℝ 1 γ) (hper : Function.Periodic γ (2 * Real.pi))
    (hnz : ∀ θ, deriv γ θ ≠ 0) : Function.Surjective (normalizedArcReparam γ) := by
  obtain ⟨c, hτ, _, hperiod⟩ := exists_isC1TraceReparam_normalizedArc hγ hper hnz
  have hbound : ∀ θ, |normalizedArcReparam γ θ - θ| ≤ 2 * Real.pi := by
    refine abs_le_of_periodic
      (g := fun θ => normalizedArcReparam γ θ - θ) (fun θ => ?_) (fun x hx => ?_)
    · simp only
      rw [hperiod]
      ring
    · have h0 := hτ.monotone hx.1
      have h2 := hτ.monotone hx.2.le
      rw [hτ.zero] at h0
      rw [hτ.endpoint] at h2
      rw [abs_le]
      constructor <;> linarith [hx.1, hx.2]
  refine hτ.continuous.surjective ?_ ?_
  · refine tendsto_atTop_mono (fun θ => ?_)
      (tendsto_atTop_add_const_right _ (-(2 * Real.pi)) tendsto_id)
    have h := hbound θ
    rw [abs_le] at h
    simp
    linarith
  · refine tendsto_atBot_mono (fun θ => ?_)
      (tendsto_atBot_add_const_right _ (2 * Real.pi) tendsto_id)
    have h := hbound θ
    rw [abs_le] at h
    simp
    linarith

section RegularCurve

variable {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ)
    (hper : Function.Periodic γ (2 * Real.pi)) (hnz : ∀ θ, deriv γ θ ≠ 0)

/-- The genuine increasing order isomorphism whose forward map is exactly τ. -/
def normalizedArcOrderIso : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective (normalizedArcReparam γ)
    (show StrictMono (normalizedArcReparam γ) by
      apply strictMono_of_deriv_pos
      intro θ
      rw [deriv_normalizedArcReparam hγ]
      exact mul_pos (div_pos Real.two_pi_pos (arcLen_period_pos_of_regular hγ hnz))
        (norm_pos_iff.mpr (hnz θ))) (normalizedArcReparam_surjective hγ hper hnz)


@[simp] theorem normalizedArcOrderIso_zero : normalizedArcOrderIso hγ hper hnz 0 = 0 :=
  normalizedArcReparam_zero γ

local notation "Φ0" => normalizedArcOrderIso hγ hper hnz

@[simp] theorem normalizedArcOrderIso_endpoint :
    Φ0 (2 * Real.pi) = 2 * Real.pi :=
  normalizedArcReparam_endpoint (arcLen_period_pos_of_regular hγ hnz)

@[simp] theorem normalizedArcOrderIso_symm_zero :
    (Φ0).symm 0 = 0 := by
  apply (Φ0).injective
  rw [OrderIso.apply_symm_apply, normalizedArcOrderIso_zero]

@[simp] theorem normalizedArcOrderIso_symm_endpoint :
    (Φ0).symm (2 * Real.pi) = 2 * Real.pi := by
  apply (Φ0).injective
  rw [OrderIso.apply_symm_apply, normalizedArcOrderIso_endpoint]

theorem normalizedArcOrderIso_add_period θ :
    Φ0 (θ + 2 * Real.pi) =
      Φ0 θ + 2 * Real.pi := by
  obtain ⟨c, _, _, hperiod⟩ := exists_isC1TraceReparam_normalizedArc hγ hper hnz
  exact hperiod θ

theorem normalizedArcOrderIso_symm_add_period t :
    (Φ0).symm (t + 2 * Real.pi) =
      (Φ0).symm t + 2 * Real.pi := by
  apply (Φ0).injective
  rw [OrderIso.apply_symm_apply, normalizedArcOrderIso_add_period,
    OrderIso.apply_symm_apply]

/-- The actual curve in its normalized arclength parameter. -/
def normalizedArcCurve (t : ℝ) : ℂ := γ ((Φ0).symm t)

/-- Exact recovery of the original curve with the precise normalized τ. -/
local notation "Φ1" => normalizedArcCurve hγ hper hnz

theorem normalizedArcCurve_factorization θ :
    γ θ = Φ1 (normalizedArcReparam γ θ) := by
  change γ θ = γ ((Φ0).symm
    (Φ0 θ))
  rw [OrderIso.symm_apply_apply]

theorem normalizedArcCurve_periodic :
    Function.Periodic (Φ1) (2 * Real.pi) := by
  intro t
  simp [normalizedArcCurve, normalizedArcOrderIso_symm_add_period]
  exact hper _

/-- The true derivative of the inverse map, obtained from its proved inverse
identity and continuity, not assumed as an auxiliary transfer formula. -/
theorem normalizedArcCurve_hasDerivAt t :
    HasDerivAt (Φ1)
      ((((2 * Real.pi / arcLen γ (2 * Real.pi)) *
        ‖deriv γ ((Φ0).symm t)‖)⁻¹) •
        deriv γ ((Φ0).symm t)) t :=
  (hγ.differentiable_one _).hasDerivAt.scomp t
    (show HasDerivAt (Φ0).symm (((2 * Real.pi / arcLen γ (2 * Real.pi)) * ‖deriv γ ((Φ0).symm t)‖)⁻¹) t by
      apply HasDerivAt.of_local_left_inverse
        (Φ0).symm.continuous.continuousAt
        (hasDerivAt_normalizedArcReparam hγ _) (mul_pos (div_pos Real.two_pi_pos (arcLen_period_pos_of_regular hγ hnz)) (norm_pos_iff.mpr (hnz _))).ne'
      exact Eventually.of_forall (Φ0).apply_symm_apply)

/-- Constant speed holds at every parameter because the initial velocity is
nonzero everywhere; this is stronger than the usual almost-everywhere statement. -/
theorem normalizedArcCurve_speed t :
    ‖deriv (Φ1) t‖ = arcLen γ (2 * Real.pi) / (2 * Real.pi) := by
  have hL := arcLen_period_pos_of_regular hγ hnz
  have hv : 0 < ‖deriv γ ((Φ0).symm t)‖ :=
    norm_pos_iff.mpr (hnz _)
  rw [(normalizedArcCurve_hasDerivAt hγ hper hnz t).deriv, norm_smul,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (mul_pos (div_pos Real.two_pi_pos hL) hv))]
  field_simp [hL.ne', hv.ne', Real.two_pi_pos.ne']

theorem normalizedArcCurve_lipschitz :
    LipschitzWith (Real.toNNReal (arcLen γ (2 * Real.pi) / (2 * Real.pi)))
      (Φ1) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun t => (normalizedArcCurve_hasDerivAt hγ hper hnz t).differentiableAt)
  intro t
  apply NNReal.coe_le_coe.mp
  change ‖deriv (Φ1) t‖ ≤ _
  rw [Real.coe_toNNReal _ (div_pos (arcLen_period_pos_of_regular hγ hnz) Real.two_pi_pos).le]
  exact le_of_eq (normalizedArcCurve_speed hγ hper hnz t)

theorem normalizedArcCurve_image_Icc :
    Φ1 '' Icc 0 (2 * Real.pi) = γ '' Icc 0 (2 * Real.pi) := by
  change (γ ∘ (Φ0).symm) '' Icc 0 (2 * Real.pi) = _
  rw [image_comp, OrderIso.image_Icc, normalizedArcOrderIso_symm_zero,
    normalizedArcOrderIso_symm_endpoint]

theorem normalizedArcCurve_injOn (hinj : InjOn γ (Ico 0 (2 * Real.pi))) :
    InjOn (Φ1) (Ico 0 (2 * Real.pi)) := by
  have hm : ∀ x ∈ Ico 0 (2 * Real.pi),
      (Φ0).symm x ∈ Ico 0 (2 * Real.pi) := by
    intro x hx
    constructor
    · simpa using
        (Φ0).symm.monotone hx.1
    · simpa using
        (Φ0).symm.strictMono hx.2
  intro x hx y hy hxy
  exact (Φ0).symm.injective (hinj (hm x hx) (hm y hy) hxy)

end RegularCurve

/-- Closed-disk injectivity of the actual supplied F proves circle-trace
injectivity on one half-open period by genuine circle-map injectivity. -/
theorem physicalCircleTrace_injOn_of_closedDisk_inj F
    (hinj : InjOn F (closedBall 0 1)) :
    InjOn (physicalCircleTrace F) (Ico 0 (2 * Real.pi)) := by
  intro x hx y hy hxy
  exact injOn_circleMap_of_abs_sub_le' (by norm_num : (1 : ℝ) ≠ 0)
    (by simp : 2 * Real.pi - 0 ≤ 2 * Real.pi) hx hy (hinj (circleMap_mem_closedBall 0 (by norm_num) x) (circleMap_mem_closedBall 0 (by norm_num) y) hxy)

end PolyaNeumann

end
