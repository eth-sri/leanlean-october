module
/-
Selected proof slices adapted from Scott McColm, MIT-0,
commit 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
See ../../../../third_party/twelfth/SOURCE_IMPORTS.json and LICENSE-MIT-0.
No upstream project or Architect module is imported.
-/
public import MathCollab.Density.Stronger.TruncatedLayerCake
public import Mathlib.NumberTheory.LSeries.RiemannZeta

@[expose] public section

open MeasureTheory Filter Set
open scoped Interval ENNReal Topology
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger

def zetaMomentCriticalNorm (t : ℝ) : ℝ :=
  ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖

theorem continuous_zetaMomentCriticalNorm : Continuous zetaMomentCriticalNorm := by
  unfold zetaMomentCriticalNorm
  apply Continuous.norm
  rw [continuous_iff_continuousAt]
  intro t
  have hne : (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) ≠ 1 := by
    intro h
    have hreal := congrArg Complex.re h
    norm_num at hreal
  apply ContinuousAt.comp (g := riemannZeta)
    (f := fun u : ℝ => (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * Complex.I))
  · exact (differentiableAt_riemannZeta hne).continuousAt
  · fun_prop














