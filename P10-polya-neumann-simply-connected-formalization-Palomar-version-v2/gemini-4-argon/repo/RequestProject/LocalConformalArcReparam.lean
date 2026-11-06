module

public import RequestProject.PhysicalHardySupport
public import RequestProject.LocalConformalInverse
public import RequestProject.TraceReparam
public import RequestProject.ArcLength
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Normalized arclength of the actual supplied circle trace

The map is exactly `τ θ = (2π / arcLen γ (2π)) * arcLen γ θ`.
For a regular periodic C¹ curve its speed has genuine positive lower and finite
upper bounds, derived from compactness on one period. The fundamental theorem
of calculus proves every pointwise derivative of τ. These facts construct the
existing `IsC1TraceReparam` witness, including its actual endpoints.

For supplied smooth conformal coordinates, the real boundary differential gives
the actual nonvanishing circle velocity. Holomorphicity is required only inside
the disk. No constant-speed hypothesis for the circle trace, boundary image or
orientation hypothesis, or synchronization with another parametrization is
assumed or concluded here.
-/

@[expose] public section


noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped Topology ContDiff

variable {γ : ℝ → ℂ}

/-- The precise normalized arclength change of parameter. -/
def normalizedArcReparam (γ : ℝ → ℂ) (θ : ℝ) : ℝ :=
  (2 * Real.pi / arcLen γ (2 * Real.pi)) * arcLen γ θ

@[simp] theorem normalizedArcReparam_zero γ :
    normalizedArcReparam γ 0 = 0 := by
  simp [normalizedArcReparam, arcLen]

/-- Actual pointwise FTC, including the endpoints and every other real input. -/
local notation "Φ0" => deriv γ

local notation "Φ1" => normalizedArcReparam γ

theorem hasDerivAt_normalizedArcReparam  (hγ : ContDiff ℝ 1 γ) θ :
    HasDerivAt (Φ1)
      ((2 * Real.pi / arcLen γ (2 * Real.pi)) * ‖Φ0 θ‖) θ :=
  ((hγ.continuous_deriv_one.norm.integral_hasStrictDerivAt 0 θ).hasDerivAt).const_mul _

theorem deriv_normalizedArcReparam  (hγ : ContDiff ℝ 1 γ) θ :
    deriv (Φ1) θ =
      (2 * Real.pi / arcLen γ (2 * Real.pi)) * ‖Φ0 θ‖ :=
  (hasDerivAt_normalizedArcReparam hγ θ).deriv

/-- Compactness supplies true lower and upper velocity bounds on the whole
real line, using exact periodicity to extend one period's bounds. -/
theorem exists_regular_periodic_speed_bounds 
    (hγ : ContDiff ℝ 1 γ) (hper : Function.Periodic γ (2 * Real.pi))
    (hnz : ∀ θ, Φ0 θ ≠ 0) :
    ∃ m M : ℝ, 0 < m ∧ 0 ≤ M ∧
      ∀ θ, m ≤ ‖Φ0 θ‖ ∧ ‖Φ0 θ‖ ≤ M := by
  have hs := hγ.continuous_deriv_one.norm
  obtain ⟨m, hm, hmlocal⟩ := isCompact_Icc.exists_forall_le' hs.continuousOn
    (fun θ _ => norm_pos_iff.mpr (hnz θ))
  obtain ⟨θ₀, hθ₀, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (⟨0, le_refl 0, Real.two_pi_pos.le⟩) hs.continuousOn
  refine ⟨m, ‖Φ0 θ₀‖, hm, norm_nonneg _, fun θ => ?_⟩
  let θ' := toIcoMod Real.two_pi_pos 0 θ
  have hθ' : θ' ∈ Ico 0 (2 * Real.pi) := by
    simpa [θ'] using toIcoMod_mem_Ico Real.two_pi_pos 0 θ
  rw [← (show ‖Φ0 θ'‖ = ‖Φ0 θ‖ by
    dsimp only [θ']
    rw [toIcoMod, (show Function.Periodic (fun θ => ‖Φ0 θ‖) (2 * Real.pi) by
      intro θ
      change ‖Φ0 (θ + 2 * Real.pi)‖ = _
      rw [deriv_periodic hper θ]).sub_zsmul_eq])]
  exact ⟨hmlocal θ' (Ico_subset_Icc_self hθ'), hmax (Ico_subset_Icc_self hθ')⟩

theorem arcLen_period_pos_of_regular 
    (hγ : ContDiff ℝ 1 γ) (hnz : ∀ θ, Φ0 θ ≠ 0) :
    0 < arcLen γ (2 * Real.pi) := by
  apply intervalIntegral.integral_pos Real.two_pi_pos hγ.continuous_deriv_one.norm.continuousOn
    (fun _ _ => norm_nonneg _)
  exact ⟨0, ⟨le_refl 0, Real.two_pi_pos.le⟩, norm_pos_iff.mpr (hnz 0)⟩

theorem normalizedArcReparam_endpoint 
    (hL : 0 < arcLen γ (2 * Real.pi)) :
    Φ1 (2 * Real.pi) = 2 * Real.pi := by
  unfold normalizedArcReparam
  exact div_mul_cancel₀ _ hL.ne'

theorem normalizedArcReparam_add_period  
    (hK : LipschitzWith K γ) (hper : Function.Periodic γ (2 * Real.pi))
    (hL : 0 < arcLen γ (2 * Real.pi)) θ :
    Φ1 (θ + 2 * Real.pi) =
      Φ1 θ + 2 * Real.pi := by
  simp [normalizedArcReparam]
  rw [arcLen_add_period hK hper, mul_add, div_mul_cancel₀ _ hL.ne']

/-- Construction of all seven fields of the genuine trace-reparametrization
structure. The returned lower bound also holds pointwise on the whole line. -/
theorem exists_isC1TraceReparam_normalizedArc 
    (hγ : ContDiff ℝ 1 γ) (hper : Function.Periodic γ (2 * Real.pi))
    (hnz : ∀ θ, Φ0 θ ≠ 0) :
    ∃ c : ℝ, IsC1TraceReparam (Φ1) c ∧
      (∀ θ, c ≤ deriv (Φ1) θ) ∧
      (∀ θ, Φ1 (θ + 2 * Real.pi) =
        Φ1 θ + 2 * Real.pi) := by
  obtain ⟨m, M, hm, hM, hbounds⟩ := exists_regular_periodic_speed_bounds hγ hper hnz
  have hγlip : LipschitzWith (Real.toNNReal M) γ := by
    apply lipschitzWith_of_nnnorm_deriv_le hγ.differentiable_one
    intro θ
    apply NNReal.coe_le_coe.mp
    change ‖Φ0 θ‖ ≤ _
    rw [Real.coe_toNNReal _ hM]
    exact (hbounds θ).2
  have hL := arcLen_period_pos_of_regular hγ hnz
  let a := 2 * Real.pi / arcLen γ (2 * Real.pi)
  have ha := div_pos Real.two_pi_pos hL
  have hlower θ : a * m ≤ deriv (Φ1) θ := by
    rw [deriv_normalizedArcReparam hγ]
    exact mul_le_mul_of_nonneg_left (hbounds θ).1 ha.le
  refine ⟨a * m, ?_, hlower, normalizedArcReparam_add_period hγlip hper hL⟩
  exact ⟨(strictMono_of_deriv_pos fun θ => (mul_pos ha hm).trans_le (hlower θ)).monotone, ⟨_, (show LipschitzWith (Real.toNNReal a * Real.toNNReal M) (Φ1) by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have h := (arcLen_lipschitz hγlip).dist_le_mul x y
    rw [Real.dist_eq] at h ⊢
    change |a * arcLen γ x - a * arcLen γ y| ≤ _
    rw [← mul_sub, abs_mul, abs_of_pos ha, NNReal.coe_mul,
      Real.coe_toNNReal _ ha.le, mul_assoc]
    exact mul_le_mul_of_nonneg_left h ha.le)⟩, show ContDiff ℝ 1 (Φ1) by
    apply contDiff_one_iff_deriv.mpr
    refine ⟨fun θ => (hasDerivAt_normalizedArcReparam hγ θ).differentiableAt, ?_⟩
    rw [funext (deriv_normalizedArcReparam hγ)]
    exact continuous_const.mul hγ.continuous_deriv_one.norm,
    normalizedArcReparam_zero γ, normalizedArcReparam_endpoint hL,
    mul_pos ha hm, Eventually.of_forall hlower⟩

section SuppliedCoordinates

variable {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ ∞ F (ball 0 R))
    (hhol : DifferentiableOn ℂ F (ball 0 1))

include hR hFs hhol in
/-- The actual real boundary chain rule, with complex linearity extended from
the interior to the closed disk by the existing smooth-coordinate theorem. -/
theorem localConformal_circleTrace_hasDerivAt θ :
    HasDerivAt (physicalCircleTrace F)
      (fderiv ℝ F (circleMap 0 1 θ) 1 * (circleMap 0 1 θ * Complex.I)) θ := by
  have hz : circleMap 0 1 θ ∈ closedBall 0 1 :=
    circleMap_mem_closedBall 0 (by norm_num) θ
  have hd := (((hFs.contDiffAt (isOpen_ball.mem_nhds (closedBall_subset_ball hR hz))).differentiableAt (by simp)).hasFDerivAt).comp_hasDerivAt θ (hasDerivAt_circleMap 0 1 θ)
  rw [localConformal_fderiv_closedDisk hR F hFs hhol hz] at hd
  exact hd

include hR hFs hhol in
theorem localConformal_circleTrace_deriv θ :
    deriv (physicalCircleTrace F) θ =
      fderiv ℝ F (circleMap 0 1 θ) 1 * (circleMap 0 1 θ * Complex.I) :=
  (localConformal_circleTrace_hasDerivAt hR F hFs hhol θ).deriv

include hR hFs hhol in
theorem localConformal_circleTrace_deriv_ne_zero
    (hnz : ∀ z ∈ sphere 0 1, fderiv ℝ F z 1 ≠ 0) (θ : ℝ) :
    deriv (physicalCircleTrace F) θ ≠ 0 := by
  rw [localConformal_circleTrace_deriv hR F hFs hhol]
  exact mul_ne_zero (hnz _ (circleMap_mem_sphere 0 (by norm_num) θ))
    (mul_ne_zero (circleMap_ne_center (by norm_num)) Complex.I_ne_zero)

end SuppliedCoordinates

end PolyaNeumann

end
