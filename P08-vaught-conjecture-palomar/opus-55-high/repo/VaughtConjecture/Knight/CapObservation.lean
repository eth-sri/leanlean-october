/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.Value

/-! # Finite-cut observations

Capping at an ordinal and strict truncation record exactly the same information:
the literal value below the cutoff, and one common value at or above it. Their
kernels coincide (`min_eq_min_iff_truncExt_eq`). Observing a lower cutoff commutes
with higher truncation, so capped agreement is both preserved and reflected by
stage reduction.

These are scalar order identities, including cutoff zero. No visibility, limit
stage or lawfulness premise is used. In particular, this file does **not** assert
that a section capped at an arbitrary cutoff remains lawful.
-/

@[expose] public section

namespace VaughtConjecture.Knight.Value
open ExtOrd

section
variable {α : Ordinal.{0}}

/-- Truncation does not change an observation at or below its cutoff. -/
theorem min_truncExt_of_le {γ}
    (hγ : γ ≤ ofOrd α) x :
    min (truncExt α x) γ = min x γ := by
  rcases lt_or_ge x (ofOrd α) with hx | hx
  · rw [truncExt_id_of_lt hx]
  · rw [truncExt_eq_top_of_ge hx, min_eq_right le_top, min_eq_right (hγ.trans hx)]

/-- Capping and strict truncation have the same equality kernel. -/
theorem min_eq_min_iff_truncExt_eq {x y} :
    min x (ofOrd α) = min y (ofOrd α) ↔ truncExt α x = truncExt α y := by
  constructor
  · intro h
    have h' := congrArg (truncExt α) h
    simpa only [truncExt_min, truncExt_ofOrd_of_le le_rfl, min_eq_left le_top] using h'
  · intro h
    simpa only [min_truncExt_of_le le_rfl] using congrArg (fun z => min z (ofOrd α)) h

end

end VaughtConjecture.Knight.Value
