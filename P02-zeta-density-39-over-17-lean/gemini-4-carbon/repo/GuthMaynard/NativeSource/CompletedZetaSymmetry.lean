module
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

open Complex

noncomputable section

namespace GuthMaynard.NativeMomentBase

/-- Horizontal/vertical parametrization of complex points s(σ, t) = σ + i * t for σ, t ∈ ℝ. -/
def point (σ t : ℝ) : ℂ :=
  (σ : ℂ) + (t : ℂ) * I

@[simp]
lemma point_re (σ t : ℝ) : (point σ t).re = σ := by
  simp [point]

@[simp]
lemma point_im (σ t : ℝ) : (point σ t).im = t := by
  simp [point]

end GuthMaynard.NativeMomentBase
