/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CappedDonorSource
public import VaughtConjecture.Knight.PairedSlotIncoming

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
  right_inv s := by aesop

instance : Fintype (Field P C) := Fintype.ofEquiv _ Field.equivSum.symm

namespace Ref

variable {I : Type*} [Fintype I] {N : ℕ} {R : Ref I nP N J P C}

/-- The receiving inventory of a state: the ordinal values of its source vector. -/
noncomputable def State.inventory {j : ℕ} (st : R.State j) : Finset Ordinal.{0} :=
  PairedSlotEncoding.values st.sourceProfile

/-- The canonical incoming encoder of a state at its cutoff. -/
noncomputable def State.encoder {j : ℕ} (st : R.State j) : ExtOrd → ExtOrd :=
  PairedSlotIncoming.encoder j st.inventory

theorem State.encoder_witness {j : ℕ} (st : R.State j) : Witness (gTop j) st.encoder :=
  PairedSlotIncoming.encoder_witness j st.inventory

theorem State.encoder_reflects_bottom {j : ℕ} (st : R.State j) (x : ExtOrd)
    (h : st.encoder x = ⊥) : x = ⊥ :=
  PairedSlotIncoming.encoder_reflects_bottom j st.inventory x h

/-- **Canonical normalization** of a state: the encoder applied to every field. -/
noncomputable def normalizeState {j : ℕ} (st : R.State j) : R.State j := mapState st.encoder st

/-- On the source vector, normalization is the paired-slot normalization. -/
theorem sourceProfile_normalizeState {j : ℕ} (st : R.State j) (f : Field P C) :
    (normalizeState st).sourceProfile f = PairedSlotEncoding.normalize j st.sourceProfile f := by
  rw [normalizeState, sourceProfile_map]
  exact PairedSlotIncoming.encoder_profile j st.sourceProfile f

/-- Normalization preserves admissibility, at the current grade. -/
theorem normalizeState_admissible {j : ℕ} (hj : 1 ≤ j) {st : R.State j}
    (hst : R.Admissible st) : R.Admissible (normalizeState st) :=
  hst.map st.encoder_witness (min_le_left j J) hj st.encoder_reflects_bottom

/-- Normalization preserves synchronization. -/
theorem normalizeState_synchronized {j : ℕ} (hj : 1 ≤ j) {st : R.State j}
    (hs : Synchronized st) : Synchronized (normalizeState st) :=
  hs.map st.encoder_witness hj

end Ref

end CappedDonor

end VaughtConjecture.Knight
