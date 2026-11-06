/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import InfinitaryLogic.Descriptive.Polish
public import InfinitaryLogic.Lomega1omega.Semantics

/-!
# Generic Satisfaction Measurability for Carrier-Parametric Structure Spaces

This file proves that satisfaction of Lω₁ω formulas is measurable on
`StructureSpaceOn L α` for any encodable carrier α. This generalizes the
ℕ-specific results in `SatisfactionBorel.lean`.

## Main Definitions

- `ModelsOfBoundedOn`: The set of codes in `StructureSpaceOn L α` where a bounded
  formula is realized.
- `ModelsOfOn`: The set of codes where a sentence is realized.

## Main Results

- `modelsOfBoundedOn_measurableSet`: Satisfaction of any bounded Lω₁ω formula is
  measurable on `StructureSpaceOn L α`.
- `modelsOfOn_measurableSet`: Satisfaction of any Lω₁ω sentence is measurable.
-/

@[expose] public section

universe u v u'

namespace FirstOrder

namespace Language

open Structure MeasureTheory

variable {L : Language.{u, v}}

section Measurability

variable [L.IsRelational] {α : Type*}

/-- The set of codes in `StructureSpaceOn L α` where a bounded formula is realized,
given variable assignments. -/
def ModelsOfBoundedOn
    {β : Type u'} {n}
    (φ : L.BoundedFormulaω β n) (v : β → α) (xs : Fin n → α) :
    Set (StructureSpaceOn L α) :=
  {c | @BoundedFormulaω.Realize L α (StructureSpaceOn.toStructure c) β n φ v xs}

/-- The set of codes in `StructureSpaceOn L α` where a sentence is realized. -/
def ModelsOfOn (φ : L.Sentenceω) : Set (StructureSpaceOn L α) :=
  ModelsOfBoundedOn φ Empty.elim Fin.elim0

end Measurability

end Language

end FirstOrder
