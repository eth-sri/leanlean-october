module

public import RequestProject.PlanarTypes

public import RequestProject.PlanarGeometry

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic.Linarith
public import RequestProject.Defs

/-!
# Smooth disk tests from maps defined near the closed disk

A function smooth on a disk of radius greater than one has a global
compactly supported smooth representative agreeing with it near the closed
unit disk. This avoids requiring a conformal coordinate map to be smooth
on the entire plane when constructing the actual disk H¹ representative.
No extension of a conformal map as a homeomorphism is asserted here.
-/

@[expose] public section

open scoped ContDiff

noncomputable section

namespace PolyaNeumann

open Set Filter Metric
open scoped Topology

/-- Both cutoff radii lie strictly between one and the given radius. -/
def smoothDiskCutoffBump (R : ℝ) (hR : 1 < R) : ContDiffBump (0 : ℂ) :=
  ⟨(R + 1) / 2, (3 * R + 1) / 4, by linarith, by linarith⟩

def smoothDiskCutoff R hR (φ : PlaneMap) z  :=
  (smoothDiskCutoffBump R hR z : ℂ) * φ z

theorem smoothDiskCutoffBump_tsupport_subset R hR :
    tsupport (smoothDiskCutoffBump R hR) ⊆ ball (0 : ℂ) R := by
  rw [ContDiffBump.tsupport_eq]
  exact closedBall_subset_ball (show (3 * R + 1) / 4 < R by linarith)

section
variable {R } (hR : 1 < R) {φ : PlaneMap} (hφ : RealSmoothOnBall φ R)
include R hR φ hφ

/-- Smoothness is needed only where the cutoff can be nonzero. -/
theorem contDiff_smoothDiskCutoff :
    RealSmooth (smoothDiskCutoff R hR φ) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ ball 0 R
  · exact (Complex.ofRealCLM.contDiff.comp
      (smoothDiskCutoffBump R hR).contDiff).contDiffAt.mul
        (hφ.contDiffAt (isOpen_ball.mem_nhds hz))
  · have hz'  :=
      fun h => hz (smoothDiskCutoffBump_tsupport_subset R hR h)
    apply (contDiffAt_const (c := 0)).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hz'] with w hw
    simp_all [smoothDiskCutoff]

theorem smoothDiskCutoff_testFunction :
    TestFunction univ (smoothDiskCutoff R hR φ) := by
  refine ⟨contDiff_smoothDiskCutoff hR hφ, ?_, subset_univ _⟩
  exact ((smoothDiskCutoffBump R hR).hasCompactSupport.comp_left
    (g := fun x : ℝ => (x : ℂ)) Complex.ofReal_zero).mul_right

end


section
variable {R : ℝ} (hR : 1 < R) (φ : PlaneMap) {z : ℂ}
include R hR φ z

theorem smoothDiskCutoff_eventuallyEq (hz : z ∈ ball (0 : ℂ) ((R + 1) / 2)) :
    smoothDiskCutoff R hR φ =ᶠ[𝓝 z] φ := by
  filter_upwards [isOpen_ball.mem_nhds hz] with w hw
  simp  [smoothDiskCutoff, (smoothDiskCutoffBump R hR).one_of_mem_closedBall (ball_subset_closedBall hw)]

theorem smoothDiskCutoff_eq_closedDisk (hz : z ∈ closedUnitDisk) :
    smoothDiskCutoff R hR φ z = φ z := (smoothDiskCutoff_eventuallyEq hR φ
    (closedBall_subset_ball (show 1 < (R + 1) / 2 by linarith) hz)).self_of_nhds

theorem fderiv_smoothDiskCutoff_eq (hz : z ∈ closedUnitDisk) :
    fderiv ℝ (smoothDiskCutoff R hR φ) z = fderiv ℝ φ z :=
  (smoothDiskCutoff_eventuallyEq hR φ
    (closedBall_subset_ball (show (1 : ℝ) < (R + 1) / 2 by linarith) hz)).fderiv_eq

end


end PolyaNeumann

end
