/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SourceOnlyCompositionRepair

/-! # Finite interpolation preserving an entire faithful prefix

Two normalized witnesses agreeing at a grade-visible source cut can be joined,
keeping the first witness on the entire closed prefix. No extra visibility grade
is required: the cut itself belongs to the retained side. Combining this with
source-only interpolation gives an exact finite test for retaining an old prefix
while satisfying new literal source reads. It constructs witnesses, not rows.
-/

@[expose] public section

namespace VaughtConjecture.Knight.SharpWitnessComposition

open Transform Value ExtOrd

/-- The bottom fibre of any faithful witness is constant on source blocks. -/
theorem witness_bot_of_same_block {g : ℕ → ExtOrd} {τ : ExtOrd → ExtOrd}
    (hτ : Witness g τ) {x y : ExtOrd} (hb : blockFloor x = blockFloor y)
    (hx : τ x = ⊥) : τ y = ⊥ := by
  apply bot_of_same_block (f := τ) _ hb hx
  intro z hz k i hi
  have h := hτ.clause5 z k (by rw [hz]; exact bot_le) i hi
  rwa [hz, extVisibilityReplace_bot] at h

/-- Bounded replacements do not bring an input above a visible cut back to the prefix. -/
theorem replace_gt_visible_cut {m k i : ℕ} {a x : ExtOrd}
    (ha : SelfVis m a) (hk : k ≤ m) (hx : a < x) :
    a < extVisibilityReplace x k i := by
  rcases ExtOrd.cases a with rfl | rfl | ⟨b, rfl⟩
  · exact bot_lt_iff_ne_bot.mpr (extVisibilityReplace_ne_bot (ne_of_gt hx) k i)
  · exact False.elim (not_lt_of_ge le_top hx)
  · rcases ExtOrd.cases x with rfl | rfl | ⟨c, rfl⟩
    · exact False.elim (not_lt_of_ge bot_le hx)
    · exact hx
    · rw [extVisibilityReplace_ofOrd, ofOrd_lt_ofOrd]
      exact visReplace_gt_of_gt (hk.trans (selfVis_ofOrd_iff.mp ha)) (ofOrd_lt_ofOrd.mp hx)

/-- The entire closed prefix is invariant under bounded replacements. -/
theorem replace_le_visible_cut_iff {m k i : ℕ} {a x : ExtOrd}
    (ha : SelfVis m a) (hk : k ≤ m) (hi : i ≤ k) :
    extVisibilityReplace x k i ≤ a ↔ x ≤ a := by
  constructor
  · intro h
    by_contra hx
    exact not_lt_of_ge h (replace_gt_visible_cut ha hk (not_le.mp hx))
  · intro h
    exact (extVisibilityReplace_mono k i hi h).trans_eq
      (evr_eq_self_of_selfVis (selfVis_mono ha hk) i)
