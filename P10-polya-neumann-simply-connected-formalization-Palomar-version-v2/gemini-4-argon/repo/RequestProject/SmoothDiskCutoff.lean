module

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

noncomputable section

namespace PolyaNeumann

open Set Filter Metric
open scoped Topology ContDiff

variable {R : ℝ}

/-- Both cutoff radii lie strictly between one and the given radius. -/
def smoothDiskCutoffBump (R : ℝ) (hR : 1 < R) : ContDiffBump (0 : ℂ) :=
  ⟨(R + 1) / 2, (3 * R + 1) / 4, by linarith, by linarith⟩

def smoothDiskCutoff (R : ℝ) (hR : 1 < R) (φ : ℂ → ℂ) (z : ℂ) : ℂ :=
  (smoothDiskCutoffBump R hR z : ℂ) * φ z

/-- Smoothness is needed only where the cutoff can be nonzero. -/
theorem contDiff_smoothDiskCutoff  hR 
    (hφ : ContDiffOn ℝ ∞ φ (ball 0 R)) :
    ContDiff ℝ ∞ (smoothDiskCutoff R hR φ) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ ball 0 R
  · exact (Complex.ofRealCLM.contDiff.comp
      (smoothDiskCutoffBump R hR).contDiff).contDiffAt.mul
        (hφ.contDiffAt (isOpen_ball.mem_nhds hz))
  · have hz' : z ∉ tsupport (smoothDiskCutoffBump R hR) :=
      fun h => hz ((show tsupport (smoothDiskCutoffBump R hR) ⊆ ball 0 R by
        rw [ContDiffBump.tsupport_eq]
        exact closedBall_subset_ball (show (3 * R + 1) / 4 < R by linarith)) h)
    apply (contDiffAt_const (c := 0)).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hz'] with w hw
    simp [smoothDiskCutoff, hw]

theorem smoothDiskCutoff_testFunction  hR 
    (hφ : ContDiffOn ℝ ∞ φ (ball 0 R)) :
    TestFunction univ (smoothDiskCutoff R hR φ) := by
  refine ⟨contDiff_smoothDiskCutoff hR hφ, ?_, subset_univ _⟩
  exact ((smoothDiskCutoffBump R hR).hasCompactSupport.comp_left
    (g := fun x : ℝ => (x : ℂ)) Complex.ofReal_zero).mul_right

theorem smoothDiskCutoff_eventuallyEq  hR φ
     (hz : z ∈ ball 0 ((R + 1) / 2)) :
    smoothDiskCutoff R hR φ =ᶠ[𝓝 z] φ := by
  filter_upwards [isOpen_ball.mem_nhds hz] with w hw
  simp [smoothDiskCutoff, (smoothDiskCutoffBump R hR).one_of_mem_closedBall (ball_subset_closedBall hw)]

theorem smoothDiskCutoff_eq_closedDisk  hR φ
     (hz : z ∈ closedBall 0 1) :
    smoothDiskCutoff R hR φ z = φ z := by
  exact (smoothDiskCutoff_eventuallyEq hR φ
    (closedBall_subset_ball (by linarith) hz)).self_of_nhds

theorem fderiv_smoothDiskCutoff_eq  hR φ
     (hz : z ∈ closedBall 0 1) :
    fderiv ℝ (smoothDiskCutoff R hR φ) z = fderiv ℝ φ z :=
  (smoothDiskCutoff_eventuallyEq hR φ
    (closedBall_subset_ball (show 1 < (R + 1) / 2 by linarith) hz)).fderiv_eq

end PolyaNeumann

end
