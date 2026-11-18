module

public import PDEFoundation.Ambient.EuclideanNorm
public import PDEFoundation.Measure.AffineVolume
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Restricted and normalized `L^p` norms

This file defines raw extended-real `L^p` norms on restricted volume and on
normalized restricted volume. Real-valued facades require a `MemLp` proof, so
an infinite extended-real norm can never be silently converted to zero.

Vector-field norms are scalarized with `PDE.vecEuclideanNorm`; they do not use
the inherited finite-product supremum norm on `PDE.Vec`.
-/

@[expose] public section

open scoped ENNReal

namespace PDE

open MeasureTheory






/-- The raw extended-real `L^p` norm with respect to volume restricted to `U`. -/
noncomputable def eLpNormOn
    {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (U : Set (Vec d)) (p : ℝ≥0∞) (f : Vec d → E) : ℝ≥0∞ :=
  eLpNorm f p (volumeOn U)










end PDE
