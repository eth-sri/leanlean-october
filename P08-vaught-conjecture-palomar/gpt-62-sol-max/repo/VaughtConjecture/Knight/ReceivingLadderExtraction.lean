/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ReceivingLadderLowerRows

set_option linter.privateModule false

/-! # Whole lower-coordinate extraction from actual receiving sections

Availability at a mixed grade-one index chooses an actual rung or shadow.
Its parent dominates it, and a maximal parent leaf therefore dominates every
present original field, the request and both eligible ladder copies. The
faithful witness of that leaf recovers all those coordinates simultaneously.

This is an arbitrary target-local input theorem conditional only on the
literal lower-row formula. No selected-display coverage, normalized ambient,
or extension of the ambient to the whole scheme is assumed. Upper rows and
the lawfulness of a newly constructed output remain separate obligations.

Ported unchanged from the reviewer's branch `rounded-meet-extension` at `78e0bf8` (the mixed
receiving candidate, its recognition, readouts, caps, constructed localities and availability;
V-C discharges the private-projection premise of `mixed_lift_of_private`).
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.ReceivingLadderCarrier

open Transform Value ExtOrd

variable {L : ℕ} {X Q U : Type*} [Fintype X] [Fintype Q] [Fintype U]
  (C : CellScheme (ι := Fin 2) Finset.univ) (hC : C.plan = privatePlan)
  (field : Cell C → X) (request : X) (profile : Q → X → ℕ)

local notation "D" => scheme (L := L) (X := X) (Q := Q) (U := U) C hC
local notation "T" => SupportLadderRows.Point L X Q

end VaughtConjecture.Knight.ReceivingLadderCarrier
