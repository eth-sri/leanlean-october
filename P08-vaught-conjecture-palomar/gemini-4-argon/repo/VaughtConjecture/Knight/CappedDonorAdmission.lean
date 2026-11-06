/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CappedDonorLowHighNormalization

/-! # Concrete source admission: complete-vector restriction and downward admission

The recursive physical construction (newapproach8/9) consumes a *scalar source family*
`S_j ⊆ (TField P C → ExtOrd)` with six closure properties.  This file instantiates that family
by the repository's actual two-threshold predicate — not by an unspecified family whose closure is
postulated — and banks the closure results that follow from the existing normalization theorems
(new19 §§1.1–1.3):

* `SourceAdmitted j a`: some two-threshold state at cutoff `j` is `TAdmissible` for the low
  reference, synchronized, and has complete source vector `a`.
* `sourceProfile_eq_persistent`: in an admissible synchronized state every persistent value *is*
  the source value — present numerical values are already `1`-visible (positive grade), future
  values are persistent by definition.  No equality between distinct future root channels is
  imposed.
* **Complete-vector restriction** (`sourceProfile_restrict_of_sync`, `profile_restrictT`):
  restricting a synchronized admissible state to a lower cutoff keeps the *entire* source vector,
  including the fields that cross from numerical to future status.  Synchronization is what
  justifies this; restriction of an arbitrary state can change a crossing field's source read.
* **Downward admission** (`SourceAdmitted.restrict`): `Adm_j a → Adm_i a` for `i ≤ j`.  Any LOW or
  HIGH obligation active at `i` was active at `j` with the same readings (the low frontier, the
  cap and the request tops are present at both cutoffs).
* **Closure under bottom-reflecting normalized maps, permissible positive caps and canonical
  normalization** (`SourceAdmitted.map`, `.positive_cap`, `.normalize`), from
  `LowRef.TAdmissible.map`, `capWitness` and `normalizeT_*`; at cap `⊥` the zero state is used
  instead (`SourceAdmitted.zero`), never a false bottom-reflection hypothesis.
* `SourceAdmitted.restrict_normalize`: the predecessor call `Norm_i a ∈ Q_i` for `i ≤ j`.

**Upward admission is deliberately absent**: `Adm_{K-1} a` does not imply `Adm_K a`, nor
`Adm_{N-1} a` implies `Adm_N a` (new19 §1.5 retains explicit failures); activation adds new
admitted layers and never re-admits old profiles at a higher grade.  Nothing here asserts that an
arbitrary lawful physical output is admitted or synchronized.  Grade-one positive monotone
interpolation (new19 §1.4) is not banked here. -/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.CappedDonor.Ref

open Transform Value ExtOrd AmalgamationPlan

variable {I : Type*} [Fintype I] {nP N J : ℕ} {P : SemScheme (nP + 1)} {C : SemScheme J}
  {R : Ref I nP N J P C}

/-! ## Synchronization identifies the persistent and source vectors -/

/-! ## Complete-vector restriction -/

/-! ## Closure under maps, permissible caps and normalization -/

/-! ## The zero state is admitted at every cutoff -/

/-- The all-bottom section of any lower set is lawful: the zero witness at every owner and the
target cell itself for availability. -/
theorem respectsBelow_bot {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
    (sem : Semantics D) (BJ : Finset ι × ℕ) :
    RespectsSemanticsBelow sem BJ (fun _ => (⊥ : ExtOrd)) :=
  RespectsSemanticsBelow.bot sem BJ

/-- The all-bottom receiving state. -/
def zeroState (R : Ref I nP N J P C) (j : ℕ) : R.State j where
  u _ := ⊥
  v _ := ⊥
  gate := ⊥
  shadowP _ := ⊥
  shadowC _ := ⊥

theorem zeroState_admissible (j : ℕ) : R.Admissible (zeroState R j) where
  u_respects := respectsBelow_bot _ _
  v_respects := respectsBelow_bot _ _
  face _ _ := rfl
  gate_vis := extVisibilityReplace_bot _ _
  shadowP_vis _ := extVisibilityReplace_bot _ _
  shadowC_vis _ := extVisibilityReplace_bot _ _
  shadowP_iff _ := Iff.rfl
  shadowC_iff _ := Iff.rfl
  support hg := absurd rfl hg
  relation _ hg := absurd rfl hg

theorem zeroState_sourceProfile (j : ℕ) (f : Field P C) :
    (zeroState R j).sourceProfile f = ⊥ := by
  by_cases hf : f.grade ≤ j
  · rw [State.sourceProfile_of_present _ hf]
    cases f <;> rfl
  · rw [State.sourceProfile_of_future _ hf]
    cases f <;> rfl

theorem zeroState_synchronized (j : ℕ) : Synchronized (zeroState R j) := by
  intro f
  rw [zeroState_sourceProfile, extVisibilityReplace_bot]
  cases f <;> rfl
