/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RelabelWitness

/-! # The orbit-block witness

A `gTop 2`-witness that reproduces the grade-two replacement orbit of one value `a` on one block:
`⊥` below the block floor `ω·b`, the orbit `R₂ⁱ a` at the point `ω·b + i` of the block (with
`i` clipped at `2`), and the orbit's top `R₂² a` from the next block floor on
(`orbitBlock a b`, `witness_orbitBlock`; `a` self-visible at grade one).  This is the shape a
witness table must have at a source block carrying two labels that clause 5 couples — the proper
label `ω + 1` and a request `ω + 2` — so it is the generic piece of every level-two table of the
lift.  Constants are spliced above it at limit cuts (`witness_spliceAt`).

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

/-! ## Replacement orbits of a grade-one self-visible value -/

theorem evr_eq_bot_iff {a : ExtOrd} (k i : ℕ) : extVisibilityReplace a k i = ⊥ ↔ a = ⊥ := by
  constructor
  · intro h; by_contra ha; exact extVisibilityReplace_ne_bot ha k i h
  · rintro rfl; exact extVisibilityReplace_bot _ _

/-! ## The orbit-block map -/

end VaughtConjecture.Knight
