/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LadderScalarRendering
public import VaughtConjecture.Knight.SourcePrefixRows

/-! # Constructed complete sources on the mixed receiving carrier

The first upper layer of new16 is evaluated on actual occurrences. Original
fields are literal, all ladder rungs and shadows use the constructed
ceiling-filled renderer, and upper leaves and numerical nodes use weighted
common-grid cuts. Both mixed copies remain distinct.

Scalar prefix agreement now implies agreement of the entire source, including
every unused rung and every weighted column. Its supported range also makes
prefix-fixing decoding preserve every coordinate. Neither theorem assumes a
completed lower vector. These are source-construction theorems, not a claim
that the complete semantics has been installed or is bountiful.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.ReceivingLadderSources

open Transform Value ExtOrd ReceivingLadderCarrier
open LadderScalarRendering
noncomputable section

variable {L : ℕ} {X Q U : Type*} [Fintype X] [Fintype Q] [Fintype U]
  (C : CellScheme (ι := Fin 2) Finset.univ) (hC : C.plan = privatePlan)
  (field : Cell C → X) (request high : X) (profile : Q → X → ℕ)
  (fields : U → X → ExtOrd) (anchor : U → Q) (G : Finset ExtOrd) (H : ExtOrd)

local notation "D" => scheme (L := L) (X := X) (Q := Q) (U := U) C hC

/-- Every auxiliary reading is computed from the scalar profile and fixed
catalogues. The reserved grade-three apex has a separate bottom default. -/
def source (a : U) (d : Cell D) : ExtOrd :=
  match view C hC d with
  | .inl c => fields a (field c)
  | .inr .request => fields a request
  | .inr (.ladder _ v) => render profile (anchor a) (fields a) H v
  | .inr (.upper _ b node) =>
      min (SourcePrefixRows.cut G (fields a) (fields b)) (if node then fields b high else H)
  | .inr .apex => ⊥

local notation "src" => source (L := L) C hC field request high profile fields anchor G H

@[simp] theorem source_old (a : U) (d : Cell C) : src a (old C hC d) = fields a (field d) := by
  simp only [source, view_old]

@[simp] theorem source_request (a : U) : src a (added C hC .request) = fields a request := by
  simp only [source, view_added]

@[simp] theorem source_ladder (a : U) (b : Bool) (v : SupportLadderRows.Point L X Q) :
    src a (added C hC (.ladder b v)) = render profile (anchor a) (fields a) H v := by
  simp only [source, view_added]

@[simp] theorem source_upper (a b : U) (full node : Bool) :
    src a (added C hC (.upper full b node)) =
      min (SourcePrefixRows.cut G (fields a) (fields b)) (if node then fields b high else H) := by
  simp only [source, view_added]

end
end VaughtConjecture.Knight.ReceivingLadderSources
