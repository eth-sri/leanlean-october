module

public import HypoellipticAleksandrov.Ambient.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Shared abbreviations for ambient vector types

These abbreviations keep repeated set and measure types over `PDE.Vec d` short.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure

namespace HypoellipticAleksandrov

/-- Subsets of the ambient vector space. -/
abbrev VecSet (d : ℕ) : Type := Set (PDE.Vec d)

/-- Measures on the ambient vector space. -/
abbrev VecMeasure (d : ℕ) : Type := MeasureTheory.Measure (PDE.Vec d)

/-- Product Lebesgue volume on the ambient vector space. -/
noncomputable abbrev VecVolume (d : ℕ) : MeasureTheory.Measure (PDE.Vec d) := volume

end HypoellipticAleksandrov
