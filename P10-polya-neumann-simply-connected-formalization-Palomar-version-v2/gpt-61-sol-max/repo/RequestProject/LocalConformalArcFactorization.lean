module

public import RequestProject.PlanarTypes

public import RequestProject.PlanarGeometry

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

theorem normalizedArcReparam_strictMono  (hγ : ContDiff ℝ 1 γ)
    (hnz : ∀ θ, deriv γ θ ≠ 0) : StrictMono (normalizedArcReparam γ) := by
  apply strictMono_of_deriv_pos
  intro θ
  rw [deriv_normalizedArcReparam hγ]
  exact mul_pos (div_pos Real.two_pi_pos (arcLen_period_pos_of_regular hγ hnz))
    (norm_pos_iff.mpr (hnz θ))

/-- The period increment prevents either end of the normalized arclength map
from remaining bounded, and continuity then proves actual surjectivity. -/
theorem normalizedArcReparam_surjective 
    (hγ : ContDiff ℝ 1 γ) (hper : Function.Periodic γ circlePeriod)
    (hnz : ∀ θ, deriv γ θ ≠ 0) : Function.Surjective (normalizedArcReparam γ) := by
  obtain ⟨c, hτ, _, hperiod⟩ := exists_isC1TraceReparam_normalizedArc hγ hper hnz
  have hbound : ∀ θ, |normalizedArcReparam γ θ - θ| ≤ 2 * Real.pi := by
    refine abs_le_of_periodic
      (g := fun θ => normalizedArcReparam γ θ - θ) (fun θ => ?_) (fun x hx => ?_)
    · simp 
      rw [hperiod]
      ring
    · have h0 := hτ.monotone hx.1
      have h2 := hτ.monotone hx.2.le
      rw [hτ.zero] at h0
      rw [hτ.endpoint] at h2
      grind
  refine hτ.continuous.surjective ?_ ?_
  · refine tendsto_atTop_mono (fun θ => ?_)
      (tendsto_atTop_add_const_right _ (-circlePeriod) tendsto_id)
    grind
  · refine tendsto_atBot_mono (fun θ => ?_)
      (tendsto_atBot_add_const_right _ circlePeriod tendsto_id)
    grind

section RegularCurve

variable {γ : ComplexCurve} (hγ : ContDiff ℝ 1 γ)
    (hper : Function.Periodic γ circlePeriod) (hnz : ∀ θ, deriv γ θ ≠ 0)

/-- The genuine increasing order isomorphism whose forward map is exactly τ. -/
def normalizedArcOrderIso  :=
  StrictMono.orderIsoOfSurjective (normalizedArcReparam γ)
    (normalizedArcReparam_strictMono hγ hnz) (normalizedArcReparam_surjective hγ hper hnz)
local notation "normalizedArcOrderIsoFixed" => normalizedArcOrderIso hγ hper hnz




@[simp] theorem normalizedArcOrderIso_zero : normalizedArcOrderIsoFixed 0 = 0 :=
  normalizedArcReparam_zero γ

@[simp] theorem normalizedArcOrderIso_endpoint :
    normalizedArcOrderIsoFixed circlePeriod = 2 * Real.pi :=
  normalizedArcReparam_endpoint (arcLen_period_pos_of_regular hγ hnz)

@[simp] theorem normalizedArcOrderIso_symm_zero :
    (normalizedArcOrderIsoFixed).symm 0 = 0 := by
  apply (normalizedArcOrderIsoFixed).injective
  norm_num

@[simp] theorem normalizedArcOrderIso_symm_endpoint :
    (normalizedArcOrderIsoFixed).symm circlePeriod = 2 * Real.pi := by
  apply (normalizedArcOrderIsoFixed).injective
  rw [OrderIso.apply_symm_apply, normalizedArcOrderIso_endpoint]

theorem normalizedArcOrderIso_add_period θ :
    normalizedArcOrderIsoFixed (θ + 2 * Real.pi) =
      normalizedArcOrderIsoFixed θ + 2 * Real.pi := by
  obtain ⟨c, _, _, hperiod⟩ := exists_isC1TraceReparam_normalizedArc hγ hper hnz
  exact hperiod θ

theorem normalizedArcOrderIso_symm_add_period t :
    (normalizedArcOrderIsoFixed).symm (t + 2 * Real.pi) =
      (normalizedArcOrderIsoFixed).symm t + 2 * Real.pi := by
  apply (normalizedArcOrderIsoFixed).injective
  rw [OrderIso.apply_symm_apply, normalizedArcOrderIso_add_period,
    OrderIso.apply_symm_apply]

/-- The actual curve in its normalized arclength parameter. -/
def normalizedArcCurve (t : ℝ) : ℂ := γ ((normalizedArcOrderIsoFixed).symm t)
local notation "normalizedArcCurveFixed" => normalizedArcCurve hγ hper hnz


/-- Exact recovery of the original curve with the precise normalized τ. -/
theorem normalizedArcCurve_factorization θ :
    γ θ = normalizedArcCurveFixed (normalizedArcReparam γ θ) := by
  change γ θ = γ ((normalizedArcOrderIsoFixed).symm
    (normalizedArcOrderIsoFixed θ))
  rw [OrderIso.symm_apply_apply]

theorem normalizedArcCurve_periodic :
    Function.Periodic normalizedArcCurveFixed circlePeriod := by
  intro t
  simp  [normalizedArcCurve, normalizedArcOrderIso_symm_add_period]
  exact hper _

/-- The true derivative of the inverse map, obtained from its proved inverse
identity and continuity, not assumed as an auxiliary transfer formula. -/
theorem normalizedArcOrderIso_symm_hasDerivAt t :
    HasDerivAt (normalizedArcOrderIsoFixed).symm
      (((2 * Real.pi / arcLen γ circlePeriod) *
        ‖deriv γ ((normalizedArcOrderIsoFixed).symm t)‖)⁻¹) t := (HasDerivAt.of_local_left_inverse (Continuous.continuousAt (OrderIso.continuous (normalizedArcOrderIsoFixed).symm)) (hasDerivAt_normalizedArcReparam hγ ((normalizedArcOrderIsoFixed).symm t)) (LT.lt.ne' (mul_pos (div_pos Real.two_pi_pos (arcLen_period_pos_of_regular hγ hnz)) (norm_pos_iff.mpr (hnz ((normalizedArcOrderIsoFixed).symm t))))) (Eventually.of_forall (OrderIso.apply_symm_apply normalizedArcOrderIsoFixed)))

theorem normalizedArcCurve_hasDerivAt t :
    HasDerivAt normalizedArcCurveFixed
      ((((2 * Real.pi / arcLen γ circlePeriod) *
        ‖deriv γ ((normalizedArcOrderIsoFixed).symm t)‖)⁻¹) •
        deriv γ ((normalizedArcOrderIsoFixed).symm t)) t :=
  (hγ.differentiable_one _).hasDerivAt.scomp t
    (normalizedArcOrderIso_symm_hasDerivAt hγ hper hnz t)

/-- Constant speed holds at every parameter because the initial velocity is
nonzero everywhere; this is stronger than the usual almost-everywhere statement. -/
theorem normalizedArcCurve_speed t :
    ‖deriv normalizedArcCurveFixed t‖ = arcLen γ circlePeriod / circlePeriod := by
  have hL := arcLen_period_pos_of_regular hγ hnz
  have hv : 0 < ‖deriv γ ((normalizedArcOrderIsoFixed).symm t)‖ :=
    norm_pos_iff.mpr (hnz _)
  have hp  :=
    inv_pos.mpr (mul_pos (div_pos Real.two_pi_pos hL) hv)
  rw [(normalizedArcCurve_hasDerivAt hγ hper hnz t).deriv, norm_smul,
    Real.norm_eq_abs, abs_of_pos hp]
  field_simp 

theorem normalizedArcCurve_lipschitz :
    LipschitzWith (Real.toNNReal (arcLen γ circlePeriod / circlePeriod))
      normalizedArcCurveFixed := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun t => (normalizedArcCurve_hasDerivAt hγ hper hnz t).differentiableAt)
  intro t
  apply NNReal.coe_le_coe.mp
  simp_all [normalizedArcCurve_speed]

theorem normalizedArcCurve_image_Icc :
    normalizedArcCurveFixed '' boundaryInterval = γ '' boundaryInterval := by
  change (γ ∘ (normalizedArcOrderIsoFixed).symm) '' boundaryInterval = _
  rw [image_comp, OrderIso.image_Icc, normalizedArcOrderIso_symm_zero,
    normalizedArcOrderIso_symm_endpoint]

theorem normalizedArcCurve_injOn (hinj : InjOn γ (Ico 0 circlePeriod)) :
    InjOn normalizedArcCurveFixed (Ico 0 circlePeriod) := by
  have hm : ∀ x ∈ Ico 0 circlePeriod,
      (normalizedArcOrderIsoFixed).symm x ∈ Ico 0 circlePeriod := by
    intro x hx
    constructor
    · simpa   using
        (normalizedArcOrderIsoFixed).symm.monotone hx.1
    · simpa   using
        (normalizedArcOrderIsoFixed).symm.strictMono hx.2
  intro x hx y hy hxy
  exact (normalizedArcOrderIsoFixed).symm.injective (hinj (hm x hx) (hm y hy) hxy)

end RegularCurve

/-- Closed-disk injectivity of the actual supplied F proves circle-trace
injectivity on one half-open period by genuine circle-map injectivity. -/
theorem physicalCircleTrace_injOn_of_closedDisk_inj F
    (hinj : InjOn F closedUnitDisk) :
    InjOn (physicalCircleTrace F) (Ico 0 circlePeriod) := by
  intro x hx y hy hxy
  have hz := hinj (circleMap_mem_closedBall 0 (by norm_num) x)
    (circleMap_mem_closedBall 0 (by norm_num) y) hxy
  exact injOn_circleMap_of_abs_sub_le' (by norm_num)
    (by simp) hx hy hz

end PolyaNeumann

end
