/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import VaughtConjecture.Knight.SlackCutPasting
import VaughtConjecture.Knight.WitnessAlgebra

/-! # A free diagonal beyond a finite source inventory

Normalize an actual maximal-grade controller locality to its capped shifter, then take
its maximum with a bottom-to-high step at a fresh limit block. This retains all old
capped targets literally and assigns any larger self-visible value to the new diagonal.
The old cap may be bottom; the new value may be top. Clause 5 holds at every threshold.

The new source is chosen from the finite coded source inventory before the labelling,
locality witness, or desired high value. This is a row extension only: it establishes
neither joint consistency with other controller rows nor availability or bountifulness.
-/

namespace VaughtConjecture.Knight

open  Value 

namespace FreeDiagonal

/-- With the normalized suppressor, clipping the shifter at a visible value preserves
the full witness. This is not an assertion about arbitrary suppressors. -/
theorem clip_witness {τ} {K} {C}
    (hτ : Witness (gTop K) τ) (hC : SelfVis K C) :
    Witness (gTop K) (fun x => min (τ x) C) where
  anti := hτ.anti
  vis := hτ.vis
  bot := by rw [hτ.bot, min_bot_left]
  mono := fun _ _ h => min_le_min (hτ.mono h) le_rfl
  clause5 := by
    intro x k hact i hi
    by_cases hk : k ≤ K
    · have hm : Monotone (fun a => extVisibilityReplace a k i) := fun _ _ h => evr_mono h hi
      rw [hτ.clause5 x k (by rw [gTop_of_le hk]; exact le_top) i hi,
        hm.map_min, evr_eq_self_of_selfVis (hC.mono hk)]
    · rw [gTop_of_gt (not_le.mp hk)] at hact
      by_cases hCb : C = ⊥
      · simp  [hCb,  ]
      · have hxb : τ x = ⊥ := by
          rcases le_total (τ x) C with h | h
          · rwa [min_eq_left h, le_bot_iff] at hact
          · exact False.elim (hCb (le_bot_iff.mp (by rwa [min_eq_right h] at hact)))
        rw [hτ.clause5 x k (by rw [hxb]; exact bot_le) i hi, hxb,
          extVisibilityReplace_bot, min_bot_left, extVisibilityReplace_bot]


