module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-! Shared notation for the function spaces and regularity classes used throughout the
planar-domain and boundary-transport arguments. The notation expands to the original types. -/

@[expose] public section

open scoped ContDiff

namespace PolyaNeumann

scoped notation "PlanarSet" => Set ℂ
scoped notation "Coord" => Fin 2
scoped notation "FourierSeq" => (ℤ → ℂ)
scoped notation "ComplexSeq" => (ℕ → ℂ)
scoped notation "PlaneMap" => (ℂ → ℂ)
scoped notation "ComplexCurve" => (ℝ → ℂ)
scoped notation "RealMap" => (ℝ → ℝ)
scoped notation "RealSmooth" => ContDiff ℝ ∞
scoped notation "RealSmoothOn" => ContDiffOn ℝ ∞
scoped notation "RealSmoothAt" => ContDiffAt ℝ ∞
scoped notation "ComplexEnd" V:arg => (V →L[ℂ] V)

/-- Smoothness on the centered complex ball used by the conformal collars. -/
scoped notation "RealSmoothOnBall" F:arg R:arg =>
  ContDiffOn ℝ (⊤ : ℕ∞) F (Metric.ball (0 : ℂ) R)

end PolyaNeumann
