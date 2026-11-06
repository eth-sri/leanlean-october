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

/-- Product Lebesgue volume is an additive Haar measure on time--velocity space. -/
instance timeVelocityVolumeIsAddHaar (d : ℕ) :
    Measure.IsAddHaarMeasure (volume : Measure (TimeVelocity d)) := by
  rw [Measure.volume_eq_prod]
  exact Measure.prod.instIsAddHaarMeasure _ _

/-- Product Lebesgue volume on time--velocity space has its exact factorization. -/
theorem volume_timeVelocity_eq_prod (d : ℕ) :
    (volume : Measure (TimeVelocity d)) =
      (volume : Measure ℝ).prod (volume : Measure (PDE.Vec d)) :=
  Measure.volume_eq_prod ℝ (PDE.Vec d)

/-- The finite exponent `d + 1` in the parabolic ABP estimate. -/
def parabolicExponent (d : ℕ) : ℝ≥0∞ := d + 1

@[simp] theorem parabolicExponent_ne_zero (d : ℕ) : parabolicExponent d ≠ 0 := by
  simp [parabolicExponent]

@[simp] theorem parabolicExponent_ne_top (d : ℕ) : parabolicExponent d ≠ ∞ := by
  simp [parabolicExponent]

@[simp] theorem parabolicExponent_toReal (d : ℕ) :
    (parabolicExponent d).toReal = (d : ℝ) + 1 := by
  unfold parabolicExponent
  rw [show (d : ℝ≥0∞) + 1 = ((d + 1 : ℕ) : ℝ≥0∞) by norm_num,
    ENNReal.toReal_natCast]
  norm_num

theorem parabolicExponent_one_le (d : ℕ) : 1 ≤ parabolicExponent d := by
  simp [parabolicExponent]

/-- The extended-real `L^(d + 1)` norm on all time--velocity space. -/
def parabolicELpNorm (d : ℕ) (f : TimeVelocity d → ℝ) : ℝ≥0∞ :=
  eLpNorm f (parabolicExponent d) volume

/-- The `ENNReal.toReal` encoding of the extended-real `L^(d + 1)` norm on all
time--velocity space. It agrees with the usual finite real `L^(d + 1)` norm whenever
`parabolicELpNorm d f ≠ ∞`, in particular under `MemLp f (parabolicExponent d) volume`. -/
def parabolicLpNorm (d : ℕ) (f : TimeVelocity d → ℝ) : ℝ :=
  (parabolicELpNorm d f).toReal

/-- The extended-real `L^(d + 1)` norm restricted to a time--velocity set. -/
def parabolicELpNormOn (d : ℕ) (f : TimeVelocity d → ℝ)
    (s : Set (TimeVelocity d)) : ℝ≥0∞ :=
  eLpNorm f (parabolicExponent d) (volume.restrict s)

/-- The `ENNReal.toReal` encoding of the extended-real `L^(d + 1)` norm restricted to a
time--velocity set. It agrees with the usual finite real `L^(d + 1)` norm whenever
`parabolicELpNormOn d f s ≠ ∞`, in particular under
`MemLp f (parabolicExponent d) (volume.restrict s)`. -/
def parabolicLpNormOn (d : ℕ) (f : TimeVelocity d → ℝ)
    (s : Set (TimeVelocity d)) : ℝ :=
  (parabolicELpNormOn d f s).toReal

end

end HypoellipticAleksandrov.Parabolic
