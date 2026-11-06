module

public import HypoellipticAleksandrov.Parabolic.Geometry
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Shared abbreviations for time--velocity types

These abbreviations keep repeated set, function and measure types over
`TimeVelocity d` short.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure

namespace HypoellipticAleksandrov.Parabolic

/-- Subsets of time--velocity space. -/
abbrev TVSet (d : ℕ) : Type := Set (TimeVelocity d)

/-- Measures on time--velocity space. -/
abbrev TVMeasure (d : ℕ) : Type := MeasureTheory.Measure (TimeVelocity d)

/-- Product Lebesgue volume on time--velocity space. -/
noncomputable abbrev TVVolume (d : ℕ) : MeasureTheory.Measure (TimeVelocity d) := volume

/-- Product Lebesgue volume restricted to a time--velocity set. -/
noncomputable abbrev TVRestrict (d : ℕ) (S : Set (TimeVelocity d)) : MeasureTheory.Measure (TimeVelocity d) :=
  (volume : MeasureTheory.Measure (TimeVelocity d)).restrict S

end HypoellipticAleksandrov.Parabolic
