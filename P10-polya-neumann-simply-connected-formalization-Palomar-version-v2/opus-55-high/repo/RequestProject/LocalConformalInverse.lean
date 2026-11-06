module

public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import RequestProject.LocalSmoothInverse
public import RequestProject.LocalConformalPullback

/-!
# The actual inverse of given closed-disk conformal coordinates

Holomorphicity in the open disk and smoothness near its closure imply
complex linearity of the real differential even on the boundary. With
closed-disk injectivity and a nonzero differential this gives a smooth
inverse on a neighborhood of the closed image. No global plane
homeomorphism is required. Existence of the initial conformal map remains
a separate obligation.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Set Metric
open scoped Topology

variable {R : ℝ}

theorem localConformal_fderiv_closedDisk (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball 0 R))
    (hhol : DifferentiableOn ℂ F (ball 0 1))
    {z : ℂ} (hz : z ∈ closedBall 0 1) (v : ℂ) :
    fderiv ℝ F z v = fderiv ℝ F z 1 * v := by
  have hc := hFs.continuousOn_fderiv_of_isOpen isOpen_ball (by simp)
  have heq : EqOn (fun w => fderiv ℝ F w v)
      (fun w => fderiv ℝ F w 1 * v) (ball 0 1) := by
    intro w hw
    have hfd (a : ℂ) : fderiv ℝ F w a = deriv F w * a := by
      rw [(hhol.differentiableAt (isOpen_ball.mem_nhds hw)).fderiv_restrictScalars ℝ]
      exact fderiv_eq_deriv_mul
    simp_all
  exact heq.of_subset_closure
    ((hc.clm_apply continuousOn_const).mono (closedBall_subset_ball hR))
    (((hc.clm_apply continuousOn_const).mul continuousOn_const).mono
      (closedBall_subset_ball hR)) ball_subset_closedBall
    (by simp [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)]) hz

theorem exists_localConformalInverse (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball 0 R))
    (hhol : DifferentiableOn ℂ F (ball 0 1))
    (hinj : InjOn F (closedBall 0 1))
    (hnz : ∀ z ∈ closedBall 0 1, fderiv ℝ F z 1 ≠ 0) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, e = F ∧
      closedBall 0 1 ⊆ e.source ∧ e.source ⊆ ball 0 R ∧
      ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target := by
  apply exists_localSmoothInverse_of_compact_differential
    (isCompact_closedBall 0 1) isOpen_ball (closedBall_subset_ball hR)
    F hFs hinj
  intro z hz
  let D  :=
    ContinuousLinearEquiv.equivOfInverse
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (fderiv ℝ F z 1)).restrictScalars ℝ)
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (fderiv ℝ F z 1)⁻¹).restrictScalars ℝ)
      (fun x => by
        simp_all)
      (fun x => by
        simp_all)
  have hDeq : D = fderiv ℝ F z := by
    apply ContinuousLinearMap.ext
    intro v
    rw [localConformal_fderiv_closedDisk hR F hFs hhol hz v]
    exact mul_comm _ _
  refine ⟨D, ?_⟩
  rw [hDeq]
  exact ((hFs.contDiffAt (isOpen_ball.mem_nhds (closedBall_subset_ball hR hz))).differentiableAt (by simp)).hasFDerivAt

end PolyaNeumann

end
