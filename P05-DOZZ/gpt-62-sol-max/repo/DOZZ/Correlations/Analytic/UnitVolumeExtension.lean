/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.ExtendedSeiberg3
public import DOZZ.Statements.Defs.UnitVolumeStructureConstant
public import DOZZ.Statements.Correlations.ComplexifyNCharges
public import Mathlib.Analysis.Calculus.FDeriv.Basic

@[expose] public section

namespace DOZZ.Proofs

open MeasureTheory

/-- Holomorphic extension of the unit-volume constant across the real extended Seiberg domain. -/
structure IsUnitVolumeExtension {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (M : Ω → Measure ℂ) (γ : ℝ) (V : Set (Fin 3 → ℂ)) (f : (Fin 3 → ℂ) → ℂ) : Prop where
  isOpen : IsOpen V
  mem (α : Fin 3 → ℝ) : ExtendedSeiberg3 γ (α 0) (α 1) (α 2) → complexifyNCharges α ∈ V
  holomorphic : DifferentiableOn ℂ f V
  value (α : Fin 3 → ℝ) : ExtendedSeiberg3 γ (α 0) (α 1) (α 2) →
    f (complexifyNCharges α) = (unitVolumeStructureConstant P M γ (α 0) (α 1) (α 2) : ℂ)

end DOZZ.Proofs
