/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CappedDonorLowHighNormalization

@[expose] public section

namespace VaughtConjecture.Knight.CappedDonor.Ref

open Transform Value ExtOrd AmalgamationPlan

noncomputable section

variable {I : Type*} [Fintype I] {nP N J : ℕ} {P : SemScheme (nP + 1)} {C : SemScheme J}
  {R : Ref I nP N J P C}

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

end

end VaughtConjecture.Knight.CappedDonor.Ref
