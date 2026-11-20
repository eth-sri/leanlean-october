/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RequestAttachment
public import VaughtConjecture.Knight.CountedRecoding
public import VaughtConjecture.Knight.ReferenceContext
public import VaughtConjecture.Knight.CappedLocalityRecoding
public import VaughtConjecture.Knight.Semantics
public import VaughtConjecture.Knight.Reduction
public import VaughtConjecture.Knight.VisibilityAlgebra
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import VaughtConjecture.Knight.FullScopeBountiful
public import VaughtConjecture.Knight.CoupledGradeOne

@[expose] public section

namespace VaughtConjecture.Knight

open AmalgamationPlan CellScheme Transform Value ExtOrd

open CellScheme.restrictFace (pushGraded)

section Inventory

/-- The constantly-`⊥` labelling respects every semantics on every lower set. -/
theorem respectsBelow_bot {ι₀ : Type*} [DecidableEq ι₀] {A₀ : Finset ι₀} {D₀ : CellScheme A₀}
    (sem : Semantics D₀) (BJ : Finset ι₀ × ℕ) :
    RespectsSemanticsBelow sem BJ (fun _ => (⊥ : ExtOrd)) :=
  RespectsSemanticsBelow.bot sem BJ

end Inventory

end VaughtConjecture.Knight
