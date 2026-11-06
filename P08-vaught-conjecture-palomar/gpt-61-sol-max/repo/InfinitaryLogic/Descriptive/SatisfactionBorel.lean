/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import InfinitaryLogic.Descriptive.SatisfactionBorelOn
import Architect

/-!
# Satisfaction of Lω₁ω Formulas is Borel

This file proves that for a countable relational language L, the set of codes in
`StructureSpace L` satisfying a given Lω₁ω sentence is measurable (Borel).

## Main Definitions

- `ModelsOfBounded`: The set of codes where a bounded formula is realized.
- `ModelsOf`: The set of codes where a sentence is realized.

## Main Results

- `modelsOfBounded_measurableSet`: Satisfaction of any bounded Lω₁ω formula is measurable.
- `modelsOf_measurableSet`: Satisfaction of any Lω₁ω sentence is measurable.
- `mem_modelsOf_iff_realize`: membership in `ModelsOf` is realization in the decoded structure.
- `modelsOf_mem_iff_of_equiv`: membership in `ModelsOf` is invariant under isomorphism of the
  decoded structures.
-/

universe u v u'

namespace FirstOrder

namespace Language


variable {L : Language.{u, v}}

section

variable [L.IsRelational] [Countable (Σ l, L.Relations l)]

/-- The set of codes where a bounded formula is realized, given variable assignments. -/
def ModelsOfBounded
    {α : Type u'} {n : ℕ}
    (φ : L.BoundedFormulaω α n) (v : α → ℕ) (xs : Fin n → ℕ) :
    Set (StructureSpace L) :=
  {c | @BoundedFormulaω.Realize L ℕ c.toStructure α n φ v xs}

/-- The set of codes where a sentence is realized. -/
def ModelsOf (φ : L.Sentenceω) : Set (StructureSpace L) :=
  ModelsOfBounded φ Empty.elim Fin.elim0

omit [Countable (Σ l, L.Relations l)] in
/-- Membership in `ModelsOf` is realization of the sentence in the decoded structure (the empty
valuation is unique).  No countability of the relation symbols is needed. -/
theorem mem_modelsOf_iff_realize c φ :
    c ∈ ModelsOf φ ↔ @Sentenceω.Realize L φ ℕ c.toStructure := Iff.rfl




