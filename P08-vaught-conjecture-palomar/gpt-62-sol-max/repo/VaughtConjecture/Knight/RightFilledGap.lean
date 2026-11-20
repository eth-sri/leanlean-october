/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OrbitPrefixSupport

@[expose] public section

namespace VaughtConjecture.Knight.RightFilledGap

open Transform Value ExtOrd

/-- The greatest grid value below the next floor, or bottom if none qualifies. -/
noncomputable def floor (G : Finset ExtOrd) (B : ExtOrd) : ExtOrd :=
  G.sup (fun z => if z ≤ B then z else ⊥)

theorem floor_le (G : Finset ExtOrd) (B : ExtOrd) : floor G B ≤ B := by
  apply Finset.sup_le
  aesop

theorem le_floor {G : Finset ExtOrd} {h B : ExtOrd} (hh : h ∈ G) (hle : h ≤ B) :
    h ≤ floor G B := by
  unfold floor
  apply Finset.le_sup_of_le hh
  simp_all

/-- A finite maximum creates no extra value between the grid points. -/
theorem floor_eq_bot_or_mem (G : Finset ExtOrd) (B : ExtOrd) :
    floor G B = ⊥ ∨ floor G B ∈ G := by
  apply Finset.sup_induction (p := fun z => z = ⊥ ∨ z ∈ G)
  all_goals grind

end VaughtConjecture.Knight.RightFilledGap
