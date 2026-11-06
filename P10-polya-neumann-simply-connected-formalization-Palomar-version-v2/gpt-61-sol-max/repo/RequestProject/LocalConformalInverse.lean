module

public import RequestProject.PlanarTypes

public import RequestProject.PlanarGeometry

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

public section

open scoped ContDiff



namespace PolyaNeumann

open Set Metric

section
variable {R } (hR : 1 < R) (F : PlaneMap) (hFs : RealSmoothOnBall F R) (hhol : DifferentiableOn ℂ F unitDisk)
include R hR F hFs hhol

theorem localConformal_fderiv_closedDisk
     (hz : z ∈ closedUnitDisk) v :
    fderiv ℝ F z v = fderiv ℝ F z 1 * v := by
  have hc := hFs.continuousOn_fderiv_of_isOpen isOpen_ball (by simp)
  have heq : EqOn (fun w => fderiv ℝ F w v)
      (fun w => fderiv ℝ F w 1 * v) unitDisk := by
    intro w hw
    have hfd (a : ℂ) : fderiv ℝ F w a = deriv F w * a := by
      rw [(hhol.differentiableAt (isOpen_ball.mem_nhds hw)).fderiv_restrictScalars ℝ]
      exact fderiv_eq_deriv_mul
    simp_all
  exact heq.of_subset_closure
    ((hc.clm_apply continuousOn_const).mono (closedBall_subset_ball hR))
    (((hc.clm_apply continuousOn_const).mul continuousOn_const).mono
      (closedBall_subset_ball hR)) ball_subset_closedBall
    (by simpa  [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] using
      subset_rfl) hz

theorem exists_localConformalInverse
    (hinj : InjOn F closedUnitDisk)
    (hnz : ∀ z ∈ closedUnitDisk, fderiv ℝ F z 1 ≠ 0) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, (e : PlaneMap) = F ∧
      closedUnitDisk ⊆ e.source ∧ e.source ⊆ ball (0 : ℂ) R ∧
      RealSmoothOn e.symm e.target := by
  apply exists_localSmoothInverse_of_compact_differential
    (isCompact_closedBall 0 1) isOpen_ball (closedBall_subset_ball hR)
    F hFs hinj
  intro z hz
  let D  :=
    ContinuousLinearEquiv.equivOfInverse
      ((ContinuousLinearMap.smulRight (1 : ComplexEnd ℂ) (fderiv ℝ F z 1)).restrictScalars ℝ)
      ((ContinuousLinearMap.smulRight (1 : ComplexEnd ℂ) (fderiv ℝ F z 1)⁻¹).restrictScalars ℝ)
      (fun x => by
        simp_all)
      (fun x => by
        simp_all)
  have hDeq : (D : ℂ →L[ℝ] ℂ) = fderiv ℝ F z := by
    apply ContinuousLinearMap.ext
    intro v
    change v * fderiv ℝ F z 1 = fderiv ℝ F z v
    grind only [localConformal_fderiv_closedDisk]
  refine ⟨D, ?_⟩
  rw [hDeq]
  have hsd := hFs.contDiffAt (isOpen_ball.mem_nhds (closedBall_subset_ball hR hz))
  exact (hsd.differentiableAt (by simp)).hasFDerivAt

end


end PolyaNeumann
