/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeOneSelectedSections

/-! # The finite normalized family of an actual grade-one boundary

No abstract order-closure or section-supply contract is assumed. A
bottom-reflecting finite interpolation transports the actual semantics,
including the higher-threshold source-block conditions. The family is the
finite set of lawful, rank-normalized boundary profiles.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.GradeOneBoundaryFamily

open Transform Value ExtOrd SlotControllerFamily
open FullRowLifting NormalizedProfileFamily

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D)

local notation "rankCode" => NormalizedProfileFamily.code

/-- Every family member is an actual respecting normalized boundary profile. -/
def Profile := {p : Cell D → Fin (D.card + 1) //
  RespectsSemantics sem (fun d => value (p d).val) ∧
    ∀ d, rankCode (fun e => value (p e).val) d = (p d).val}

instance : Finite (Profile sem) := by unfold Profile; infer_instance
noncomputable instance : Fintype (Profile sem) := Fintype.ofFinite (Profile sem)

end VaughtConjecture.Knight.GradeOneBoundaryFamily
