/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.FullScopeBountiful
import VaughtConjecture.Knight.Domain

/-! # Pullback semantics along a graded retraction, with mute cells

A scheme `D'` whose cells retract onto the cells of a scheme `D` carrying a semantics `sem`:
`ret : Cell D' → Cell D` preserves grades and scope inclusions on the non-mute cells.  The
**pullback semantics** (`Semantics.pullback`) gives a non-mute cell `x` the row of `ret x` read
through `ret`, and a mute cell the row `⊥`.

* It is **coded** when `sem` is, and **consistent** when `sem` is, provided mute cells never lie
  below non-mute cells and `ret` has **sections over graded indices**: for every non-mute cell `Xi₀`
  and old cell `Xi'` of the graded index of `ret Xi₀`, some cell of the graded index of `Xi₀`
  retracts to `Xi'` (availability witnesses lift; `Semantics.pullback_isConsistent`).
* **Respect transports** both ways along a bijective retraction of lower sets
  (`RespectsSemanticsBelow.of_pullback`, `RespectsSemanticsBelow.pullback`), and the pullback of a
  respecting labelling along a retraction with sections respects (`pullback_of_sect`).
* **Bountifulness transports** along bijective retractions of both lower sets
  (`bountiful_pullback_of_bij`).
* **Controller probes** (`RespectsSemanticsBelow.eq_of_controller_probes`): two cells of the same
  grade at which every full-scope controller of that grade reads the same value carry the same
  label under every respecting labelling.  For a pullback along a retraction this gives
  **uniqueness of extension over a fixed old labelling**: respecting labellings factor through the
  retraction (`Knight/FourPointDuplication.lean`).

Construction-private (not root-exported). -/

namespace VaughtConjecture.Knight



/-- Antisymmetry of the scope/grade order. -/
def GradedLe.antisymm' {κ : Type*} {X Y : GradedIndex κ} (h₁ : GradedLe X Y)
    (h₂ : GradedLe Y X) :=
  Prod.ext (Finset.Subset.antisymm h₁.1 h₂.1) (le_antisymm h₁.2 h₂.2)

