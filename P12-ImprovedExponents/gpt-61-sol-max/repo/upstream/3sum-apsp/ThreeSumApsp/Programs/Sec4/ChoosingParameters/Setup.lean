/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Util.Types
public import Mathlib.Tactic
public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Contracts
public import ThreeSumApsp.Programs.Sec4.Theorem30.Memory
public import ThreeSumApsp.Sec4.Corollary31
public import ThreeSumApsp.Util.Ceil

/-!
# Corollaries 26 and 31 in the light language: m, the places of the padded matrices, the query

m = ⌈log₄ D⌉ (`logFour`), the places of the padded matrices and of the block of Theorem 30 behind
the free pointer (`paddedXAt`, `paddedYAt`, `blockAt`), the text of the query, and the bounds on the
entries of the padded matrices. The text of the query serves all rational parameters; its
specification is `QuerySpec31`, proved in `query31_meets`.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp

/-! ## Parameters and map -/

/-- m = ⌈log₄ D⌉. -/
def logFour D₀ := Nat.clog 4 D₀
/-- The address of the padded X. -/
def paddedXAt fr := fr + 3
/-- The address of the padded Y. -/
def paddedYAt N D₀ fr := fr + 3 + N * D (logFour D₀)
/-- The base address of the block of Theorem 30. -/
def blockAt N D₀ fr := fr + 3 + N * D (logFour D₀) + N * D (logFour D₀)
/-! ## The query -/


/-- query31(I, J, N, D, aX, aY, fr): if the flag is 1, the query of Theorem 30, and otherwise the
inner product. -/
def query31Body : Stmt :=
  .ite (M (v 6) =' k 1) (.call Proc.queryAt [v 0, v 1, M (v 6 +' k 1)] 0)
    (.call 63 [v 0, v 1, v 2, v 3, v 4, v 5] 0)

theorem abs_padInnerCols_le {N D₀ D'} {X : ThreeSumApsp.IntMatrix N D₀} {U}
    (h : ∀ i j, |X i j| ≤ U) (hU : 0 ≤ U) i j :
    |padInnerCols D' X i j| ≤ U := by
  grind [padInnerCols]

theorem abs_padInnerRows_le {N D₀ D'} {Y : ThreeSumApsp.IntMatrix D₀ N} {U}
    (h : ∀ i j, |Y i j| ≤ U) (hU : 0 ≤ U) i j :
    |padInnerRows D' Y i j| ≤ U := by
  grind [padInnerRows]

theorem le_D_logFour D₀ : D₀ ≤ D (logFour D₀) := Nat.le_pow_clog (by norm_num) D₀

/-- The ceiling ⌈log₄ D⌉ in natural numbers. -/
theorem ceil_logb_four (D₀ : ℕ) : ⌈Real.logb 4 D₀⌉₊ = logFour D₀ := by
  have := Real.natCeil_logb_natCast 4 D₀
  simpa [logFour] using this

/-- m ≤ 4 D, because m ≤ 4^m ≤ 4 D. -/
def logFour_le_four_mul {D₀} (hD : 1 ≤ D₀) :=
  le_trans (Nat.lt_pow_self (by norm_num)).le (Nat.pow_clog_le_mul (b := 4) (by norm_num) hD)

/-- m ≥ 1 means D ≥ 2. -/
theorem two_le_of_clog {D₀} (h : 1 ≤ logFour D₀) : 2 ≤ D₀ := by
  by_contra hc
  have : logFour D₀ = 0 := Nat.clog_of_right_le_one (by omega) 4
  omega

end Light.Sec4
