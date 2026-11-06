/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Lang.Lib.Copy
import ThreeSumApsp.Lang.Lib.Sqrt
import ThreeSumApsp.Programs.Sec2.Theorem5.Contracts

/-!
# Three routines of the library, as their callers see them

The programs for Theorem 5 call their procedures by number, and a caller assumes a specification of
the procedure that does not name its body: PowSpec for the tables of powers, FillSpec for filling a
segment, SqrtSpec for the square root.  Each follows from the specification of the routine in the
library; pow first puts its arguments in the order of the library's routine.
-/


namespace Light.Sec2

variable {lim : Limits} {P : Program} {c : ℕ}

/-! ## The tables of powers -/

/-- pow(b, n, dst): the arguments are put in the order of powTable(dst, n + 1, b), whose body
follows.  Local 5 is a temporary. -/
def powBody : Stmt :=
  .set 5 (v 0) ;;
  .set 0 (v 2) ;;
  .set 2 (v 5) ;;
  .set 1 (v 1 +' k 1) ;;
  powTableBody

/-- **pow(b, n, dst)** writes the powers b^0, …, b^n to the cells from dst, within 35 (n + 1) steps.
-/
theorem pow_entry (std : Std lim) (hP : P[pPow]? = some powBody) (hc : 35 ≤ c := by decide) :
    PowSpec lim P c := by
  intro b n dst μ hdst1 hdst hb hpow d _
  refine .mono_const (.of_body hP ?_) hc
  -- The arguments b, n, dst become dst, n + 1, b.
  light_set b
  light_set dst
  light_set b
  light_set (n + 1)
  refine (powTable_ends 0 0 _ std.space_le hdst fun j hj => ?_).mono
    (by simp [powTableTime]; omega) fun _ h => h
  exact le_trans (by exact_mod_cast Nat.pow_le_pow_right hb hj) hpow

/-! ## Filling a segment -/

/-! ## The square root -/

/-- **sqrt(K)** returns ⌊√K⌋, within 18 (⌊√K⌋ + 1) steps. -/
theorem sqrt_entry (hP : P[pSqrt]? = some sqrtBody) (hc : 18 ≤ c := by decide) : SqrtSpec lim P c :=
  fun _ μ hw _ _ =>
    ((sqrt_meets hP μ).mono_time (by simp; omega)).mono_const hc
