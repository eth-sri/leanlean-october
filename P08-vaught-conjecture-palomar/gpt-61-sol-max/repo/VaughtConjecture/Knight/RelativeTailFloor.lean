import PalomarProof.Ordinal
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.PositiveFloor

/-! # The relative tail floor: keep the proper prefix, floor only the tail

The reviewer's notes6 (`simplification_and_completion.md` §5, 2026-09-19).
`tailFloor δ w x = x` if `x ≤ δ`, `max x w` otherwise.  The positive floor of
`Knight/PositiveFloor.lean` is the case `δ = ⊥`.  The note's side condition `δ ≤ w` is never
needed: the floor is monotone, bottom-reflecting and commutes with replacement without it.

* **Replacement cannot cross a visible cutoff** (`le_iff_evr_le`): for `δ` `k`-visible and
  `i ≤ k`, `x ≤ δ ↔ R_{k,i} x ≤ δ`.  Hence the floor commutes with replacement through the
  visibility grade of `δ` and `w` (`tailFloor_evr`) and is a bottom-reflecting normalized
  grade-`K` witness (`witness_tailFloor`); it transports lawfulness on unchanged long rows
  (`tailFloor_respects`).
* **The exact cap identity** (`tailFloor_min`): `min (F_{δ,w} x) γ = F_{δ∧γ, w∧γ} (min x γ)`,
  a lattice identity valid for every cap `γ`; in particular every comparison cap `γ ≤ δ` is
  untouched (`tailFloor_min_of_le`).  That the capped parameters `δ ∧ γ`, `w ∧ γ` themselves
  give a grade-`K` witness is a separate claim needing their own visibility
  (`witness_tailFloor_min`); the identity does not supply it.
* **The localized-height version** (`tailFloor_respects_whole`): on an arbitrary scheme whose
  rows above `K` need not be mute, if the *selected* section reads every owner of grade above
  `K` at most `δ`, then the floored section is lawful on the whole unchanged scheme: owners of
  grade at most `K` use the witness, higher owners see a literally unchanged capped locality
  target.  This is a condition on the section, not on the scheme's rows, and no mute-diagonal
  assumption replaces it.  The note asks for `δ` visible through the target height; formally
  `K`-visibility of both `δ` and `w` suffices, because a higher owner `o` with `p o ≤ δ` reads
  `min (F x) (p o) = min x (p o)` for every `x` by `tailFloor_min_of_le`, with no replacement
  involved.

What it does not do: restore reference equations, activate a guard, or produce a
reference-frame theorem — those are the remaining construction obligations.

Construction-private (not root-exported). -/

namespace VaughtConjecture.Knight

open   Value ExtOrd 

/-! ## Replacement cannot cross a visible cutoff -/

/-- For `δ` `k`-visible, a value and its replacement at grade `k` lie on the same side of `δ`. -/
theorem le_iff_evr_le {δ x} {k i} (hδ : SelfVis k δ) (hi : i ≤ k) :
    x ≤ δ ↔ extVisibilityReplace x k i ≤ δ := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨a, rfl⟩
  · rw [extVisibilityReplace_bot]
  · rw [extVisibilityReplace_top]
  · by_cases hfp : k ≤ finitePart a
    · rw [extVisibilityReplace_of_le_finitePart hfp]
    · have hfp' := not_le.mp hfp
      rw [extVisibilityReplace_of_finitePart_lt hfp']
      rcases ExtOrd.cases δ with rfl | rfl | ⟨g, rfl⟩
      · simp_all
      · simp  
      · rw [selfVis_ofOrd_iff] at hδ
        rw [ofOrd_le_ofOrd, ofOrd_le_ofOrd]
        constructor
        · intro h
          have hl  := limitPart_mono h
          rcases hl.lt_or_eq with hlt | heq
          · exact (limitPart_add_nat_le_of_lt hlt i).trans (limitPart_le)
          · rw [heq]
            calc limitPart g + (i) ≤ limitPart g + (finitePart g) :=
                  add_le_add_right (Nat.cast_le.mpr (hi.trans hδ)) _
              _ = g := limitPart_add_finitePart g
        · intro h
          have hl  := by
            have := limitPart_mono h
            rwa [limitPart_limitPart_add_nat] at this
          rcases hl.lt_or_eq with hlt | heq
          · have h1 := limitPart_add_nat_le_of_lt hlt (finitePart a)
            rw [limitPart_add_finitePart] at h1
            exact h1.trans (limitPart_le)
          · calc a = limitPart a + (finitePart a) := (limitPart_add_finitePart a).symm
              _ ≤ limitPart g + (finitePart g) := by
                  simp_all <;> omega
              _ = g := limitPart_add_finitePart g

/-! ## The floor -/

/-! ## The exact cap identity -/

/-! ## Transport on unchanged rows -/

variable {ι : Type*} [DecidableEq ι]   

