module
public import TaoTrudgianYang2025.BProcessBaseline
public import TaoTrudgianYang2025.BetaLegendreAnchoring
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

@[expose] public section

/-!
# Smooth cutoffs on retained real intervals

The plateau and support are constructed from strict endpoint buffers.
Multiplication by the cutoff turns a function smooth near its support
into a globally smooth correction, without extending the original function.
-/



open Filter
open scoped Topology ContDiff

namespace TaoTrudgianYang2025


theorem smoothCutoff_mul_contDiff {χ H : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ)
    (hH : ∀ x ∈ tsupport χ, ContDiffAt ℝ ∞ H x) :
    ContDiff ℝ ∞ (fun x => χ x * H x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport χ
  · exact hχ.contDiffAt.mul (hH x hx)
  · have he : (fun y => χ y * H y) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      simp only [hy, zero_mul, Pi.zero_apply]
    exact contDiffAt_const.congr_of_eventuallyEq he


