/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Sec2.Lemma6

/-!
# Strings, vertices and the coefficients of the encoding

Section 2.3.1. The recursion `Full` works on arrays indexed by strings of variables. This file has
the counts that the later cost estimates use: `7^L` left strings and `7^L` right strings of length
`L`, `10^k` vertices at depth `k` of the recursion tree, and coefficients `φ_λ(s)` and `ψ_λ(t)` in
`{0, ±1}`. The first three follow from the sizes of the alphabets; the last is a finite check. So is
the sentence that each form has at most three nonzero coefficients (`card_support_phi_le`,
`card_support_psi_le`), which no later proof uses. The example in the caption of Figure 3 is
`figure_3`.
-/

public section

open Finset

namespace ThreeSumApsp

/-- Section 2.3.1: an array on the left strings of length `L` "has 7^L entries in total". -/
theorem card_leftStr (L : ℕ) : Fintype.card (LeftStr L) = 7 ^ L := by
  rw [Fintype.card_fun, card_leftVar, Fintype.card_fin]

/-- Section 2.3.1: an array on the right strings of length `L` has `7^L` entries. -/
theorem card_rightStr (L : ℕ) : Fintype.card (RightStr L) = 7 ^ L := by
  rw [Fintype.card_fun, card_rightVar, Fintype.card_fin]

/-- Section 2.3.1: "φ_λ(s) ∈ {0, ±1}". -/
theorem abs_phi_le_one (lam : Term) (s : LeftVar) : |phi lam s| ≤ 1 := by
  decide +revert

/-- Section 2.3.1: `ψ_λ(t) ∈ {0, ±1}`. -/
theorem abs_psi_le_one (lam : Term) (t : RightVar) : |psi lam t| ≤ 1 := by
  decide +revert

end ThreeSumApsp
