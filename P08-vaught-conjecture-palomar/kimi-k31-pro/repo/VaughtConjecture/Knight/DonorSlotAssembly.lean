/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SlotControllerFamily
public import VaughtConjecture.Knight.DonorFreshSlots

/-! # A jointly consistent slot layer retaining actual old occurrences

All slot controllers are supplied simultaneously, with literal old readings
and one fresh column. Every old occurrence remains a distinct occurrence even
when sources coincide. The common old profile respects the unchanged old rows.
Every lawful old input and independent fresh value has a joint whole-layer
section. Arbitrary row-layer ambients have an actual dominating controller.

This does not add intermediate mixed scopes or prove a bountiful cell scheme.
Full-index availability is proved; proper-index availability and original-cap
lifting are separate obligations.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.DonorSlotAssembly

open Transform Value ExtOrd FreshSourceSlots

variable {X : Type*} [Fintype X]

abbrev Occ (X : Type*) [Fintype X] := Option X ⊕ Fin (Fintype.card X + 1)

def old (d : X) : Occ X := .inl (some d)
def fresh : Occ X := .inl none
def controller (j : Fin (Fintype.card X + 1)) : Occ X := .inr j

open Classical in
/-- This map is only a proof device. The carrier remains `Occ X`, not its image. -/
noncomputable def position (E : X → ExtOrd) : Occ X → SlotControllerFamily.Point (Fintype.card X)
  | .inl none => SlotControllerFamily.fresh
  | .inl (some d) => if E d = ⊥ then SlotControllerFamily.bottomPoint
      else SlotControllerFamily.old ⟨rank E d, rank_lt_card E d⟩
  | .inr j => SlotControllerFamily.controller j

noncomputable def row (E : X → ExtOrd) (q : Fin (Fintype.card X + 1))
    (d : Occ X) : ExtOrd := SlotControllerFamily.row q (position E d)

def Joint (E : X → ExtOrd) (p : Occ X → ExtOrd) : Prop :=
  (∀ d, SelfVis 1 (p d)) ∧
  (∀ c, TransformsTo (fun _ : Occ X => 1) (row E c)
    (fun d => min (p d) (p (controller c)))) ∧
  ∀ d, ∃ c, p d ≤ p (controller c)

theorem pull_joint (E : X → ExtOrd) {p : SlotControllerFamily.Point (Fintype.card X) → ExtOrd}
    (hp : SlotControllerFamily.Joint p) : Joint E (fun d => p (position E d)) := by
  refine ⟨fun d => hp.1 _, ?_, ?_⟩
  · intro c
    exact (hp.2.2.1 c).reindex (position E)
  · intro d
    exact hp.2.2.2 (position E d)

theorem rows_joint (E : X → ExtOrd) (q : Fin (Fintype.card X + 1)) : Joint E (row E q) :=
  pull_joint E (SlotControllerFamily.rows_joint q)

section ActualDonor

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  {sem : Semantics D} {o : Cell D} [Fintype (D.below (D.cell o))]

end ActualDonor

end VaughtConjecture.Knight.DonorSlotAssembly
