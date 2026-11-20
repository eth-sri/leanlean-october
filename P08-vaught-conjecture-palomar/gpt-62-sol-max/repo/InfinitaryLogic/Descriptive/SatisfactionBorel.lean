/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import InfinitaryLogic.Descriptive.SatisfactionBorelOn
public import Architect

@[expose] public section

universe u v u'

namespace FirstOrder

namespace Language

open Structure MeasureTheory

variable {L : Language.{u, v}}

section Measurability

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
theorem mem_modelsOf_iff_realize (c : StructureSpace L) (φ : L.Sentenceω) :
    c ∈ ModelsOf φ ↔ @Sentenceω.Realize L φ ℕ c.toStructure := by aesop

end Measurability

end Language

end FirstOrder
