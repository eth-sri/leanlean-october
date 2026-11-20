/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ReceivingLadderExtraction
public import VaughtConjecture.Knight.SharpWitnessComposition

set_option linter.privateModule false

/-! # The active grade-one cut on the installed long ladder

An arbitrary lawful lower ambient supplies a faithful whole-coordinate chart.
An active original coordinate puts the first reaching rank strictly below the
spare tip. Thus every reading below the cut is short, although the complete
leaf row is not. No canonical-ambient or selected-display hypothesis is used.

This is the low/high receipt part of the grade-one base, not its replacement
anchor construction or a scope-raising lifting theorem.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.ReceivingLadderBaseCut
open Transform Value ExtOrd ReceivingLadderCarrier SharpWitnessComposition
noncomputable section

variable {L : ℕ} {X Q U : Type*} [Fintype X] [Fintype Q] [Fintype U]
  (C : CellScheme (ι := Fin 2) Finset.univ) (hC : C.plan = privatePlan)
  (field : Cell C → X) (request : X) (profile : Q → X → ℕ)

local notation "D" => scheme (L := L) (X := X) (Q := Q) (U := U) C hC
local notation "idx" => lowerIndex (L := L) (U := U) C hC field request profile
local notation "src" => fun a d => SupportLadderRows.source L (idx a d)

end
end VaughtConjecture.Knight.ReceivingLadderBaseCut
