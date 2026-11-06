/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ThreePointSlotBoundary
public import VaughtConjecture.Knight.FiniteProfileControllers

/-! # A finite controller family covering every lawful three-point boundary

Profiles code all nine proper-face occurrences, including the two mute zeros,
and are normalized by occurrence rank rather than allowing arbitrary code gaps.
Every lawful boundary has an order- and bottom-preserving profile in this
fixed finite family, and therefore a whole joint row-layer section. No old
source order is chosen uniformly across inputs. Normalization here supplies
sections, not original-cap lifting for the new full-scope controllers.

This is a row-family construction. The two mute coordinates are zero
coordinates in the grade-one layer; an actual full-scope scheme and its
higher-grade lower domains still have to be installed.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.ThreePointSlotProfiles

open Transform Value ExtOrd SlotControllerFamily ThreePointSlotBoundary

open Classical in
noncomputable def code (p : Fin 9 → ExtOrd) (d : Fin 9) : ℕ :=
  if p d = ⊥ then 0 else FreshSourceSlots.rank p d + 1

/-- This family is fixed before prescribing any boundary labels. The rank
condition excludes extraneous gaps, without assuming a common source order. -/
def Profile := {p : Fin 9 → Fin 10 // Lawful (fun d => value (p d).val) ∧
  ∀ d, code (fun e => value (p e).val) d = (p d).val}

instance : Finite Profile := by unfold Profile; infer_instance

end VaughtConjecture.Knight.ThreePointSlotProfiles
