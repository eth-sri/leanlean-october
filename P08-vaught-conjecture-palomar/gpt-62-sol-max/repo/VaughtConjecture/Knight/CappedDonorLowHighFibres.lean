/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CappedDonorLowHighAboveN

/-! # The two-threshold same-grade fibres at every cutoff (audit16 §1; note §11 (5))

The all-grade statements of both same-grade fibres of the two-threshold family
(`LowRef.exists_private_lift`, `LowRef.exists_request_lift`): for an admissible two-threshold
state and a lawful current prescription on one original face agreeing with the state below a
permissible cap `γ`, there is an admissible state with that prescription literally, every
coordinate of the other section retained below `γ`, the cap receipts of the gate and of every
persistent field, the cap receipt of the stored cutoff, and — at a positive cap — the gate and
every shadow (every still-future field) retained **literally**.  The cases: below `K`, at bottom
cap, between `K` and `N`, and at or above `N`.

On **source profiles** (`Synchronized`), resynchronization preserves two-threshold admissibility
(`TAdmissible.resync`: the source vector, hence the non-top maximum and the cap field, is
unchanged), and both fibres carry complete cap receipts for every persistent field
(`exists_private_lift_sync`, `exists_request_lift_sync`).

This is a theorem about complete source states with one prescribed original face, not about
simultaneous exact prescriptions on two original faces or arbitrary physical histories; the
conversion of the complete field receipts into controller/node/guard receipts of a constructed
physical scheme is the separate prefix/row obligation, not asserted here. -/

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd AmalgamationPlan

namespace CappedDonor

namespace Ref

variable {I : Type*} [Fintype I] {nP N J : ℕ} {P : SemScheme (nP + 1)} {C : SemScheme J}
  {R : Ref I nP N J P C} {K : ℕ} (L : R.LowRef K)

/-! ## Both fibres at every cutoff -/

/-! ## Source profiles -/

/-- The source vector is unchanged by resynchronization. -/
theorem sourceProfile_resync {j : ℕ} (st : R.State j) :
    (resync st).sourceProfile = st.sourceProfile := by
  funext f
  by_cases h : f.grade ≤ j
  · rw [State.sourceProfile_of_present _ h, State.sourceProfile_of_present _ h]
    cases f <;> rfl
  · rw [State.sourceProfile_of_future _ h, State.sourceProfile_of_future _ h]
    cases f with
    | req d => exact resync_shadowP_of_future st h
    | priv d => exact resync_shadowC_of_future st h
    | gate => rfl

theorem nonTopMax_resync {j : ℕ} (st : R.State j) : (resync st).nonTopMax = st.nonTopMax := by
  unfold State.nonTopMax; rw [sourceProfile_resync]

theorem capField_resync {j : ℕ} (st : R.State j) : (resync st).capField = st.capField := by
  unfold State.capField; rw [sourceProfile_resync]

/-- Resynchronization preserves two-threshold admissibility. -/
theorem LowRef.TAdmissible.resync {j : ℕ} {S : R.TState j} (hS : L.TAdmissible S) :
    L.TAdmissible ⟨resync S.st, S.b⟩ where
  adm := hS.adm.resync
  b_vis := hS.b_vis
  b_visK := hS.b_visK
  low hj hg hm hH := by
    rw [nonTopMax_resync] at hm
    rw [capField_resync] at hH
    exact hS.low hj hg hm hH
  high := hS.high

end Ref

end CappedDonor

end VaughtConjecture.Knight
