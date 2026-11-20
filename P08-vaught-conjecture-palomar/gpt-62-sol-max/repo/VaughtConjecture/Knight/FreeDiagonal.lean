/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CoupledGradeOne
public import VaughtConjecture.Knight.WitnessAlgebra

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

namespace FreeDiagonal

/-- With the normalized suppressor, clipping the shifter at a visible value preserves
the full witness. This is not an assertion about arbitrary suppressors. -/
theorem clip_witness {τ : ExtOrd → ExtOrd} {K : ℕ} {C : ExtOrd}
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
      rw [hτ.comm x hk hi,
        hm.map_min, evr_eq_self_of_selfVis (hC.mono hk)]
    · rw [gTop_of_gt (not_le.mp hk)] at hact
      by_cases hCb : C = ⊥
      · simp_all
      · have hxb : τ x = ⊥ := by
          aesop
        rw [hτ.clause5 x k (by rw [hxb]; exact bot_le) i hi, hxb,
          extVisibilityReplace_bot, min_bot_left, extVisibilityReplace_bot]

end FreeDiagonal

end VaughtConjecture.Knight
