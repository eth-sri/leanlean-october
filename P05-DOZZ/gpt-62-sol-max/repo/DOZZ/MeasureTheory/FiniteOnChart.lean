/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-! Local finiteness on an open part of the plane. -/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal

namespace DOZZ.Proofs

/-- Finiteness of a measure on the compact subsets of an open chart. -/
abbrev FiniteOnChart {E : Type*} [TopologicalSpace E] [MeasurableSpace E] (U : Set E) (μ : Measure E) : Prop :=
  ∀ K, IsCompact K → K ⊆ U → μ K < ⊤

end DOZZ.Proofs
