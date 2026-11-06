/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeOneInputEncoding
public import VaughtConjecture.Knight.NormalizedProfileFamily
public import VaughtConjecture.Knight.SourcePrefixRows

/-! # Explicit selected grade-one sections

The decoder is a finite right-filled table, not a chosen transformation.
It returns the first represented value above a source index, or the supplied
ceiling. Consequently its whole range has literal boundary/ceiling support.
All ordinals, bottom and literal top are permitted as boundary values.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.GradeOneSelectedSections

open Transform Value ExtOrd SlotControllerFamily
open NormalizedProfileFamily (code_le code_zero code_order)

local notation "rankCode" => NormalizedProfileFamily.code

variable {X : Type*} [Fintype X]

open Classical in
noncomputable def decode (p : X → ExtOrd) (C : ExtOrd) (i : ℕ) : ExtOrd :=
  if i = 0 then ⊥ else min C ((Finset.univ.filter (fun d => i ≤ rankCode p d)).inf p)

@[simp] theorem decode_zero (p : X → ExtOrd) (C : ExtOrd) : decode p C 0 = ⊥ := by
  simp only [decode, ↓reduceIte]

variable {Q : Type*}

end VaughtConjecture.Knight.GradeOneSelectedSections
