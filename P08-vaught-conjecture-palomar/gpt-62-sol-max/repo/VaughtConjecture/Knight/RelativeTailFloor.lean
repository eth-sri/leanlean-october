/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.PositiveFloor

@[expose] public section

namespace VaughtConjecture.Knight

open AmalgamationPlan Transform Value ExtOrd SharpWitnessComposition

/-- For `δ` `k`-visible, a value and its replacement at grade `k` lie on the same side of `δ`. -/
theorem le_iff_evr_le {δ x : ExtOrd} {k i : ℕ} (hδ : SelfVis k δ) (hi : i ≤ k) :
    x ≤ δ ↔ extVisibilityReplace x k i ≤ δ := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨a, rfl⟩
  · rw [extVisibilityReplace_bot]
  · rw [extVisibilityReplace_top]
  · by_cases hfp : k ≤ finitePart a
    · rw [extVisibilityReplace_of_le_finitePart hfp]
    · have hfp' := not_le.mp hfp
      rw [extVisibilityReplace_of_finitePart_lt hfp']
      rcases ExtOrd.cases δ with rfl | rfl | ⟨g, rfl⟩
      · aesop
      · simp only [le_top]
      · rw [selfVis_ofOrd_iff] at hδ
        rw [ofOrd_le_ofOrd, ofOrd_le_ofOrd]
        constructor
        · intro h
          have hl : limitPart a ≤ limitPart g := limitPart_mono h
          rcases hl.lt_or_eq with hlt | heq
          · exact (limitPart_add_nat_le_of_lt hlt i).trans (limitPart_le g)
          · rw [heq]
            calc limitPart g + (i : Ordinal.{0}) ≤ limitPart g + (finitePart g : Ordinal.{0}) :=
                  add_le_add_right (Nat.cast_le.mpr (hi.trans hδ)) _
              _ = g := limitPart_add_finitePart g
        · intro h
          have hl : limitPart a ≤ limitPart g := by
            have := limitPart_mono h
            rwa [limitPart_limitPart_add_nat] at this
          rcases hl.lt_or_eq with hlt | heq
          · have h1 := limitPart_add_nat_le_of_lt hlt (finitePart a)
            rw [limitPart_add_finitePart] at h1
            exact h1.trans (limitPart_le g)
          · calc a = limitPart a + (finitePart a : Ordinal.{0}) := (limitPart_add_finitePart a).symm
              _ ≤ limitPart g + (finitePart g : Ordinal.{0}) := by (simp_all <;> omega)
              _ = g := limitPart_add_finitePart g

end VaughtConjecture.Knight
