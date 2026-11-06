/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Sec4.Lemma27_28

/-!
# The boxes of an output string, from its leaves of order exactly `t` (Section 4.2)

Let `η` be an output string (the paper's w) with inner set `Q` of `m` levels. The boxes of `η` are
the cubes of the sets `𝓑_V`, over all `V ⊆ Q` with `|V| = m - t`. This file proves two passages of
the running text of Section 4.2 about them.

* *Every box of `η` has exactly `m - t` symbols that are `P₀` or stars*
  (`card_starLevels_add_card_P0Levels`).
* *The second description.* Take a leaf of order exactly `t` contributing to `η` and replace its
  `P₀` by a star at every level of `Q` below the lowest level of `Q` at which it chooses another
  term, or at every level of `Q` if `t = 0` (`starBelow`). For such a leaf this is the box of the
  leaf (`boxOfLeaf_eq_starBelow`), so it is a box of `η` (`starBelow_mem`). Replacing the stars with
  `P₀` gives the leaf back (`starsToP0_starBelow`), and it turns every box of `η` into a leaf of
  order exactly `t` contributing to `η` (`starsToP0_of_mem`). So each box of `η` arises exactly once
  (`existsUnique_starBelow_eq`).
-/


open Finset

namespace ThreeSumApsp

variable {L m t : ℕ} {η : OutStr L} {τ : Leaf L}

/-- Section 4.2, for a leaf `τ` of order exactly `t` contributing to `η`: "consider the lowest level
of Q at which it chooses a term other than P₀, and replace its P₀ by a star at every lower level of
Q (or at every level of Q, if t = 0)." With `Z` the set of the levels of `Q` at which `τ` chooses
`P₀`, these lower levels are those of `F_Z`, which is all of `Q` if `Z = Q`. -/
def starBelow (η : OutStr L) (τ : Leaf L) : Cube L :=
  Cube.starAt (FV (innerSetO η) (Zof (innerSetO η) τ)) τ

/-- A leaf of order exactly `t` contributing to `η` chooses `P₀` at exactly `m - t` levels. -/
lemma card_Zof_eq (hτ : Leaf.Contributes τ η) (hord : order m τ = t) :
    (Zof (innerSetO η) τ).card = m - t := by
  grind [order_eq_sub_card_Zof]

/-- A set `Z` of `m - t` levels needs no padding: `V = Z`. -/
lemma Vof_eq_self (Q Z : Finset (Fin L)) (hZ : Z.card = m - t) : Vof m t Q Z = Z := by
  grind [Vof, lowest]

/-- For a leaf of order exactly `t` contributing to `η`, the cube of the second description is the
box of the leaf. -/
theorem boxOfLeaf_eq_starBelow (hτ : Leaf.Contributes τ η) (hord : order m τ = t) :
    boxOfLeaf m t η τ = starBelow η τ := by
  grind [boxOfLeaf, starBelow, Vof_eq_self, card_Zof_eq]

/-- Section 4.2: "The result is a box of w". -/
theorem starBelow_mem (hτ : Leaf.Contributes τ η) (hord : order m τ = t) :
    starBelow η τ ∈ (Vsets m t η).biUnion (BV η) := by
  have hmem := boxOfLeaf_mem_BV m t hτ
  rw [boxOfLeaf_eq_starBelow hτ hord, Vof_eq_self _ _ (card_Zof_eq hτ hord)] at hmem
  exact mem_biUnion.2 ⟨_, mem_powersetCard.2 ⟨filter_subset _ _, card_Zof_eq hτ hord⟩, hmem⟩
