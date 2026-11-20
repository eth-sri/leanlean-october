/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CappedDonorSource
public import VaughtConjecture.Knight.PairedSlotIncoming

/-! # Canonical normalization of the receiving family on the complete field inventory

The paired point/orbit normalization of the reviewer's `PairedSlotEncoding` /
`PairedSlotIncoming` (ported with attribution) instantiated on the **complete receiving-field
inventory** `Field P C` — every request field, every private field (present or future) and the
gate — at the current cutoff `j`.

* The **inventory** of a state is the set of ordinal values of its single source vector
  (`State.inventory`); the **canonical incoming encoder** is the paired-slot encoder of that
  inventory at grade `j` (`State.encoder`), a bottom-reflecting normalized witness with suppressor
  `gTop j` that leaves literal top literally.  **Normalization** applies it to every field
  (`normalizeState`); on the source vector it is exactly the paired-slot `normalize`
  (`sourceProfile_normalizeState`).
* **Preservation.**  Normalization preserves admissibility (`normalizeState_admissible`) and
  synchronization (`normalizeState_synchronized`) — this is `Admissible.map` at the *current*
  grade `j`, not the private arity: the encoder commutes with replacement through the grades
  present, and through `N` exactly when the cap is present.
* **Coded, short, literal top.**  Every normalized source value other than literal top lies in the
  coded alphabet with block bound `2·|Field P C|` (`normalizeState_coded`, the inventory count of
  the complete field vector, no boundary-cardinality substitute); every normalized source value
  is `j`-short (`normalizeState_short`); literal top and bottom are preserved
  (`normalizeState_top`, `normalizeState_bot_iff`).
* **Relative prefix preservation.**  Two states agreeing on every source field below a
  `j`-visible cut `h` have the same normalized value at every field whose value lies below `h`
  (`normalizeState_prefix`): the codes below the cut are determined by the prefix.
* **Normalized repairs stay in the catalogue.**  Both same-grade fibres on source profiles
  compose with normalization: the lift and its normalization are admissible and synchronized,
  the normalized lift is coded and short, and the cap receipts of the lift are those of the
  source-profile fibres (`exists_private_lift_normalized`, `exists_request_lift_normalized`).

Nothing here extracts a source profile from a physical section; the physical decoder side
(`PairedSlotDecoder`) is not used. -/

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd AmalgamationPlan

namespace CappedDonor

variable {nP J : ℕ} {P : SemScheme (nP + 1)} {C : SemScheme J}

/-- The field inventory as a sum type. -/
def Field.equivSum : Field P C ≃ Cell P.scheme ⊕ Cell C.scheme ⊕ Unit where
  toFun
    | .req d => Sum.inl d
    | .priv d => Sum.inr (Sum.inl d)
    | .gate => Sum.inr (Sum.inr ())
  invFun
    | Sum.inl d => .req d
    | Sum.inr (Sum.inl d) => .priv d
    | Sum.inr (Sum.inr _) => .gate
  left_inv f := by cases f <;> rfl
  right_inv s := by rcases s with d | d | ⟨⟩ <;> rfl

instance : Fintype (Field P C) := Fintype.ofEquiv _ Field.equivSum.symm

end CappedDonor

end VaughtConjecture.Knight
