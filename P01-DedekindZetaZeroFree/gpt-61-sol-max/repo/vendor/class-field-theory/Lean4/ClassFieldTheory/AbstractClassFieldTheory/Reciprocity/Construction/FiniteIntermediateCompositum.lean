module

public import Mathlib

public import ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.ReciprocityIndependence

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

namespace ClassFormation

open CyclicCohomology

/-!
# Finite intermediate fields: composita and absolute finiteness

These are the finite-stage closure facts used in the proof of the universal norm-descent lemma.  The compositum of two finite intermediate fields is their
intersection on the Galois-group side.
-/

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace FiniteIntermediateField

section
variable {E K : ClosedSubgroup G}
    (M N : FiniteIntermediateField E K)
include E K M N
/-- The compositum of two finite intermediate fields of `E / K`. -/
def compositum   :
    FiniteIntermediateField E K where
  field := M.field ⊓ N.field
  above := fun x hx => ⟨M.above hx, N.above hx⟩
  below := (inf_le_left :
    (M.field ⊓ N.field).toSubgroup ≤ M.field.toSubgroup).trans M.below
  finite := by
    let  := N.finite
    exact M.compositumWith_finite_over_base N.field N.below

/-- Proves the bound `(M.compositum N).field.toSubgroup ≤ M.field.toSubgroup`. -/
theorem compositum_le_left   :
    (M.compositum N).field.toSubgroup ≤ M.field.toSubgroup :=
  inf_le_left

/-- Proves the bound `(M.compositum N).field.toSubgroup ≤ N.field.toSubgroup`. -/
theorem compositum_le_right   :
    (M.compositum N).field.toSubgroup ≤ N.field.toSubgroup :=
  inf_le_right
end















end FiniteIntermediateField

end
end ClassFormation
