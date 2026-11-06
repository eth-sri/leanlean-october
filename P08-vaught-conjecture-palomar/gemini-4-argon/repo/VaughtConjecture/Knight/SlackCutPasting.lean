/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CoupledGradeOne

/-! # Pasting with one grade of slack

A monotone operation fixing a cut commutes with capped pasting without input agreement
if it preserves the strict lower half of the cut. Visibility replacement has this property
when the cut is self-visible one grade higher than the thresholds in use.

This is a locality tool, not a general bountifulness theorem: sections must still be
constructed, and availability involves a choice of dominating controller. Separate
existential domination is not, by itself, preserved by coordinatewise pasting.

For actual respecting inputs, `paste_iff_high_controller_overlap` isolates the exact
availability condition. Unique graded indices suffice, but are not imposed on the
existing constructions, which genuinely have multiple cells at some indices. The
fixed repaired three-level scheme also pastes at slack cuts by its exact classification.

The extra visibility is essential for unrestricted operation commutation. It cannot
be substituted for the externally supplied cap in unrestricted bountifulness, nor
confused with the limit stage used for reduction.
-/

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

/-- The useful part of controller capping, with the bottom-controller case included:
an exact shifter with bounded-threshold commutation and all-threshold bottom propagation. -/
theorem exists_exact_capped_shifter {D : Type*} {grade : D → ℕ} {E p : D → ExtOrd} {c : D}
    (hmax : ∀ d, grade d ≤ grade c) (hvis : SelfVis (grade c) (p c))
    (hloc : TransformsTo grade E (fun d => min (p d) (p c))) :
    ∃ τ : ExtOrd → ExtOrd, τ ⊥ = ⊥ ∧ Monotone τ ∧
      (∀ d, τ (E d) = min (p d) (p c)) ∧
      (∀ x k i, k ≤ grade c → i ≤ k →
        τ (extVisibilityReplace x k i) = extVisibilityReplace (τ x) k i) ∧
      (∀ x, τ x = ⊥ → ∀ k i, i ≤ k → τ (extVisibilityReplace x k i) = ⊥) := by
  by_cases hb : p c = ⊥
  · refine ⟨fun _ => ⊥, rfl, monotone_const, ?_, ?_, ?_⟩
    · intro d
      simp only [hb, min_bot_right]
    · intro x k i _ _
      exact (extVisibilityReplace_bot k i).symm
    · intros
      rfl
  · obtain ⟨_, τ, _, _, hbot, hmono, _, _, _, hsrc, hcomm, hprop⟩ :=
      exists_cappedWitness grade E p c hmax hvis hb hloc
    exact ⟨τ, hbot, hmono, hsrc, hcomm, hprop⟩
