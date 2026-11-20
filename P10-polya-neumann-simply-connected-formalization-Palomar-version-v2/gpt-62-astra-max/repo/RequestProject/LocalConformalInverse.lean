module

public import RequestProject.DiskCoordinates

public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import RequestProject.LocalSmoothInverse
public import RequestProject.LocalConformalPullback
public import RequestProject.PlanarNotation

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

open scoped ContDiff

namespace PolyaNeumann

open Set Metric
open scoped Topology

section

variable (Φ : SmoothDiskMap) (hhol : DifferentiableOn ℂ Φ.map unitDisk)
include hhol

theorem localConformal_fderiv_closedDisk {z : ℂ} (hz : z ∈ closedDisk) (v : ℂ) :
    fderiv ℝ Φ.map z v = fderiv ℝ Φ.map z 1 * v := by
  have hc := Φ.smooth.continuousOn_fderiv_of_isOpen isOpen_ball (by simp)
  have heq : EqOn (fun w => fderiv ℝ Φ.map w v)
      (fun w => fderiv ℝ Φ.map w 1 * v) unitDisk := by
    intro w hw
    have hfd (a : ℂ) : fderiv ℝ Φ.map w a = deriv Φ.map w * a := by
      rw [(hhol.differentiableAt (isOpen_ball.mem_nhds hw)).fderiv_restrictScalars ℝ]
      exact fderiv_eq_deriv_mul
    simp [*]
  exact heq.of_subset_closure
    ((hc.clm_apply continuousOn_const).mono (closedBall_subset_ball Φ.one_lt_radius))
    (((hc.clm_apply continuousOn_const).mul continuousOn_const).mono
      (closedBall_subset_ball Φ.one_lt_radius)) ball_subset_closedBall
    (by simpa only [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] using
      (subset_rfl : closedDisk ⊆ closedDisk)) hz

theorem exists_localConformalInverse (hinj : InjOn Φ.map closedDisk)
    (hnz : ∀ z ∈ closedDisk, fderiv ℝ Φ.map z 1 ≠ 0) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, (e : ℂ → ℂ) = Φ.map ∧
      closedDisk ⊆ e.source ∧ e.source ⊆ ball (0 : ℂ) Φ.radius ∧
      ContDiffOn ℝ ∞ e.symm e.target := by
  apply exists_localSmoothInverse_of_compact_differential
    (isCompact_closedBall (0 : ℂ) 1) isOpen_ball (closedBall_subset_ball Φ.one_lt_radius)
    Φ.map Φ.smooth hinj
  intro z hz
  let D  :=
    ContinuousLinearEquiv.equivOfInverse
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (fderiv ℝ Φ.map z 1)).restrictScalars ℝ)
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (fderiv ℝ Φ.map z 1)⁻¹).restrictScalars ℝ)
      (fun x => by
        simp [*])
      (fun x => by
        simp [*])
  have hDeq : (D : ℂ →L[ℝ] ℂ) = fderiv ℝ Φ.map z := by
    apply ContinuousLinearMap.ext
    intro v
    
    rw [localConformal_fderiv_closedDisk Φ hhol hz v]
    exact mul_comm _ _
  refine ⟨D, ?_⟩
  rw [hDeq]
  have hsd := Φ.smooth.contDiffAt (isOpen_ball.mem_nhds (closedBall_subset_ball Φ.one_lt_radius hz))
  exact (hsd.differentiableAt (by simp)).hasFDerivAt

end

end PolyaNeumann

end
