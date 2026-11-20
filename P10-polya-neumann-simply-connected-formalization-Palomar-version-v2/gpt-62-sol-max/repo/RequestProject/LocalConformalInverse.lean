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

section

variable {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ) (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R)) (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
include R hR F hFs hhol

theorem localConformal_fderiv_closedDisk 
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) (v : ℂ) :
    fderiv ℝ F z v = fderiv ℝ F z 1 * v := by
  have hc := hFs.continuousOn_fderiv_of_isOpen isOpen_ball (by simp)
  have heq : EqOn (fun w => fderiv ℝ F w v)
      (fun w => fderiv ℝ F w 1 * v) (ball (0 : ℂ) 1) := by
    intro w hw
    have hfd (a : ℂ) : fderiv ℝ F w a = deriv F w * a := by
      rw [(hhol.differentiableAt (isOpen_ball.mem_nhds hw)).fderiv_restrictScalars ℝ]
      change fderiv ℂ F w a = _
      exact fderiv_eq_deriv_mul
    dsimp 
    rw [hfd v, hfd 1, mul_one]
  exact heq.of_subset_closure
    ((hc.clm_apply continuousOn_const).mono (closedBall_subset_ball hR))
    (((hc.clm_apply continuousOn_const).mul continuousOn_const).mono
      (closedBall_subset_ball hR)) ball_subset_closedBall
    (by simpa only [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] using
      (subset_rfl : closedBall (0 : ℂ) 1 ⊆ closedBall (0 : ℂ) 1)) hz


end

end PolyaNeumann

end
