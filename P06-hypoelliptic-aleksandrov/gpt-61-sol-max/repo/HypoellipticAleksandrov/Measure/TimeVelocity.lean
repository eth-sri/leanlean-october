module

public import HypoellipticAleksandrov.Parabolic.Geometry
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Measures and norms on time--velocity space

This module records the product Lebesgue normalization on time--velocity
space, identifies cylinders differing only by their terminal time slice, and
defines the exact `L^(d + 1)` norms used by the parabolic ABP estimate.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal

namespace HypoellipticAleksandrov.Parabolic

noncomputable section

/-- Product Lebesgue measure on time--velocity space. -/
abbrev timeVelocityVolume (d : ℕ) : Measure (TimeVelocity d) := volume

/-- Product Lebesgue volume is an additive Haar measure on time--velocity space. -/
instance timeVelocityVolumeIsAddHaar (d : ℕ) :
    Measure.IsAddHaarMeasure (volume : Measure (TimeVelocity d)) := by
  rw [Measure.volume_eq_prod]
  exact Measure.prod.instIsAddHaarMeasure _ _

variable (d : ℕ)

/-- Product Lebesgue volume on time--velocity space has its exact factorization. -/
theorem volume_timeVelocity_eq_prod  :
    (volume : Measure (TimeVelocity d)) =
      (volume : Measure ℝ).prod (volume : Measure (PDE.Vec d)) :=
  Measure.volume_eq_prod ℝ (PDE.Vec d)

/-- The finite exponent `d + 1` in the parabolic ABP estimate. -/
def parabolicExponent  : ℝ≥0∞ := d + 1

variable (f : TimeVelocity d → ℝ)

/-- The extended-real `L^(d + 1)` norm on all time--velocity space. -/
def parabolicELpNorm   : ℝ≥0∞ :=
  eLpNorm f (parabolicExponent d)

/-- The `ENNReal.toReal` encoding of the extended-real `L^(d + 1)` norm on all
time--velocity space. It agrees with the usual finite real `L^(d + 1)` norm whenever
`parabolicELpNorm d f ≠ ∞`, in particular under `MemLp f (parabolicExponent d) volume`. -/
def parabolicLpNorm   : ℝ :=
  (parabolicELpNorm d f).toReal

variable (s : Set (TimeVelocity d))

/-- The extended-real `L^(d + 1)` norm restricted to a time--velocity set. -/
def parabolicELpNormOn
     : ℝ≥0∞ :=
  eLpNorm f (parabolicExponent d) (volume.restrict s)

/-- The `ENNReal.toReal` encoding of the extended-real `L^(d + 1)` norm restricted to a
time--velocity set. It agrees with the usual finite real `L^(d + 1)` norm whenever
`parabolicELpNormOn d f s ≠ ∞`, in particular under
`MemLp f (parabolicExponent d) (volume.restrict s)`. -/
def parabolicLpNormOn
     : ℝ :=
  (parabolicELpNormOn d f s).toReal

end

end HypoellipticAleksandrov.Parabolic
