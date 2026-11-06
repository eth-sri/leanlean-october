/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.LowOnlyDonorFibre

/-! # Both all-cap gate-free fibres and independent bottom supply

All current grades, empty roots, bottom and literal top are allowed. Bottom
supply starts from a constructed zero source, not positive-cap transport.
-/

namespace VaughtConjecture.Knight.LowOnly.Family

open     CappedDonor



variable {n K : ℕ} {P C : SemScheme n} (F : Family P C K)

/-- Private-prescribed repair on the complete inventory at every permitted cap. -/
theorem private_lift {j} {S} (hS : F.Admissible j S)
    {v}
    (hv : RespectsSemanticsBelow C.rows (effC n j) v) {γ}
    (hγ : SelfVis (effC n j).2 γ)
    (hag : ∀ d, min (v d) γ = min (S.lowerC j d) γ) :
    ∃ S', F.Admissible j S' ∧ S'.lowerC j = v ∧ S.CapEq γ S' ∧ S.FutureEq j S' := by
  by_cases hj : K ≤ j
  · exact?
  obtain ⟨u, hQ, hucap⟩ := hS.toSource.install_private F hv hγ hag
  refine ⟨S.replace u v (min S.b γ), ⟨hQ, ?_, fun h => (hj h).elim⟩,
    S.replace_lowerC _ _ _, S.replace_caps hucap hag (clipped_cutoff_cap),
    S.replace_future _ _ _⟩
  exact selfVis_min hS.cutoff (hγ.mono
    (le_min (min_le_left _ _) ((min_le_right _ _).trans F.gap.K_le)))

/-- Donor-prescribed repair; no exchange-symmetry of LOW is used. -/
theorem donor_lift {j} {S} (hS : F.Admissible j S)
    {u}
    (hu : RespectsSemanticsBelow P.rows (effC n j) u) {γ}
    (hγ : SelfVis (effC n j).2 γ)
    (hag : ∀ d, min (u d) γ = min (S.lowerP j d) γ) :
    ∃ S', F.Admissible j S' ∧ S'.lowerP j = u ∧ S.CapEq γ S' ∧ S.FutureEq j S' := by
  by_cases hj : K ≤ j
  · exact?
  obtain ⟨v, hQ, hvcap⟩ := hS.toSource.install_donor F hu hγ hag
  refine ⟨S.replace u v (min S.b γ), ⟨hQ, ?_, fun h => (hj h).elim⟩,
    S.replace_lowerP _ _ _, S.replace_caps hag hvcap (clipped_cutoff_cap),
    S.replace_future _ _ _⟩
  exact selfVis_min hS.cutoff (hγ.mono
    (le_min (min_le_left _ _) ((min_le_right _ _).trans F.gap.K_le)))

def zero : State P C := ⟨fun _ => ⊥, fun _ => ⊥, ⊥⟩

theorem zero_admissible j : F.Admissible j (zero : State P C) where
  lawfulP := RespectsSemanticsBelow.bot _ _
  lawfulC := RespectsSemanticsBelow.bot _ _
  shared _ := rfl
  futureP _ _ := selfVis_bot
  futureC _ _ := selfVis_bot
  cutoff := selfVis_bot
  low _ h := (not_lt_bot h).elim

/-- Independent private section supply, including literal-top prescriptions.
The opposite old face is extended at bottom using its own bountifulness. -/
theorem private_bottom_supply {j} {v}
    (hv : RespectsSemanticsBelow C.rows (effC n j) v) :
    ∃ S , F.Admissible j S ∧ S.lowerC j = v ∧ S.b = ⊥ ∧
      (zero : State P C).FutureEq j S := by
  obtain ⟨u, hQ, -⟩ := (F.zero_admissible j).toSource.install_private F hv
    (selfVis_bot) (fun _ => by simp  )
  refine ⟨(zero).replace u v ⊥, ⟨?_, selfVis_bot, ?_⟩,
    State.replace_lowerC _ _ _ _, rfl, State.replace_future _ _ _ _⟩
  · exact hQ
  · simp_all [VaughtConjecture.Knight.LowOnly.State.replace]

/-- Independent donor section supply with the free cutoff switched off. -/
theorem donor_bottom_supply {j} {u}
    (hu : RespectsSemanticsBelow P.rows (effC n j) u) :
    ∃ S , F.Admissible j S ∧ S.lowerP j = u ∧ S.b = ⊥ ∧
      (zero : State P C).FutureEq j S := by
  obtain ⟨v, hQ, -⟩ := (F.zero_admissible j).toSource.install_donor F hu
    (selfVis_bot) (fun _ => by simp  )
  refine ⟨(zero).replace u v ⊥, ⟨?_, selfVis_bot, ?_⟩,
    State.replace_lowerP _ _ _ _, rfl, State.replace_future _ _ _ _⟩
  · exact hQ
  · simp_all [VaughtConjecture.Knight.LowOnly.State.replace]


