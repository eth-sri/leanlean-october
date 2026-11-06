/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FullScopeBountiful
public import VaughtConjecture.Knight.Domain

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

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

section Pullback

variable {ι ι' : Type*} [DecidableEq ι] [DecidableEq ι'] {A : Finset ι} {A' : Finset ι'}
  {D : CellScheme A} {D' : CellScheme A'} (sem : Semantics D) (ret : Cell D' → Cell D)
  (mute : Cell D' → Prop) [DecidablePred mute]
  (hgrade : ∀ x, ¬ mute x → D'.grade x = D.grade (ret x))
  (hscope : ∀ x y, ¬ mute x → ¬ mute y → D'.scope x ⊆ D'.scope y →
    D.scope (ret x) ⊆ D.scope (ret y))
  (hmute_below : ∀ x d, ¬ mute x → GradedLe (D'.cell d) (D'.cell x) → ¬ mute d)

variable {sem ret mute hgrade hscope hmute_below}

/-! ### Transport of respect and bountifulness along a bijective retraction of lower sets -/

theorem GradedLe.antisymm' {κ} {X Y : Finset κ × ℕ} (h₁ : GradedLe X Y)
    (h₂ : GradedLe Y X) :
    X = Y :=
  Prod.ext (Finset.Subset.antisymm h₁.1 h₂.1) (le_antisymm h₁.2 h₂.2)

end Pullback

end VaughtConjecture.Knight
