/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec2.Theorem5.Instance
public import Mathlib.Data.Nat.Log

/-!
# The regime of Theorem 5

"Let D ≥ 4 be a power of four and N ≥ D^18 … a set W of at most N²/√D positions".  The procedure
regime(N, D, w), where w is the number of positions in W, tests whether the sizes of an instance are
in this regime.  It returns the exponent m with D = 4^m if they are, and 0 if they are not.  With
√D = 2^m, the condition on W reads w 2^m ≤ N².

The program has these parts, each with its own lemma.  regimeExp multiplies by four until D is
reached, which gives the only candidate m = ⌈log₄ D⌉ together with 4^m and 2^m = √D.  regimePow
compares D^18 with N by at most eighteen multiplications, none of which exceeds N D (but for the
first product, which is D).  regimeTests combines the four tests, the last two of which are
regimeSizes.  That the candidate is the only one is RegimeAnswer.zero.
-/

@[expose] public section

namespace Light.Sec2

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The local variables -/

namespace RegimeLocal

/-- The argument N. -/
abbrev Rows : ℕ := 0
/-- The argument D. -/
abbrev Cols : ℕ := 1
/-- The argument w. -/
abbrev Wanted : ℕ := 2
/-- The power 4^m. -/
abbrev PowFour : ℕ := 3
/-- The power 2^m. -/
abbrev PowTwo : ℕ := 4
/-- The exponent m. -/
abbrev Expo : ℕ := 5
/-- The result. -/
abbrev Result : ℕ := 6
/-- A power of D. -/
abbrev Power : ℕ := 7
/-- The exponent of that power. -/
abbrev Count : ℕ := 8
/-- 1 as long as no power of D has exceeded N, then 0. -/
abbrev Fits : ℕ := 9

end RegimeLocal

open RegimeLocal

/-! ## The text -/

/-- The search for the exponent m, with 4^m and 2^m. -/
def regimeExp : Stmt :=
  .while (v PowFour <' v Cols) (
    .set PowFour (v PowFour *' k 4) ;;
    .set PowTwo (v PowTwo *' k 2) ;;
    .set Expo (v Expo +' k 1))

/-- One round of regimePow: if the next power of D exceeds N, give up; if not, go on to it. -/
def regimePowRound : Stmt :=
  .ite (v Rows <' v Power *' v Cols)
    (.set Fits (k 0) ;; .set Count (k 18))
    (.set Power (v Power *' v Cols) ;; .set Count (v Count +' k 1))

/-- The test D^18 ≤ N: the power of D is at most N unless it is D^0. -/
def regimePow : Stmt :=
  .set Power (k 1) ;;
  .set Count (k 0) ;;
  .set Fits (k 1) ;;
  .while (v Count <' k 18) regimePowRound

/-- The last two tests, after regimePow: D^18 ≤ N and w 2^m ≤ N².  If both hold, the result becomes
m. -/
def regimeSizes : Stmt :=
  .ite (v Fits =' k 1)
    (.ite (v Rows *' v Rows <' v Wanted *' v PowTwo) .skip (.set Result (v Expo)))
    .skip

/-- The four tests: 4^m = D, m ≥ 1, D^18 ≤ N and w 2^m ≤ N².  If all hold, the result becomes m. -/
def regimeTests : Stmt :=
  .ite (v PowFour =' v Cols)
    (.ite (k 0 <' v Expo) (regimePow ;; regimeSizes) .skip)
    .skip

/-- regime(N, D, w). -/
def regimeBody : Stmt :=
  .set PowFour (k 1) ;;
  .set PowTwo (k 1) ;;
  .set Expo (k 0) ;;
  regimeExp ;;
  .set Result (k 0) ;;
  regimeTests ;;
  .set Rows (v Result)

/-! ## What the procedure returns -/

/-! ## The exponent -/

/-! ## The eighteenth power -/

/-! ## The four tests -/

/-! ## The whole procedure -/

end Light.Sec2
