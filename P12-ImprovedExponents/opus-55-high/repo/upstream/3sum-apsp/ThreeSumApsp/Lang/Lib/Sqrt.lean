/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Slots
import ThreeSumApsp.Lang.Tactics
import Mathlib.Tactic.Positivity

/-!
# The integer square root by counting up

sqrt(K) returns ⌊√K⌋ within `sqrtTime K` steps (`sqrt_meets`), by running through the squares 1, 4,
9, …: after (k + 1)² comes (k + 1)² + 2k + 3.  It does not touch the memory.
-/


namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

namespace Sqrt

/- The local variables of sqrt: the argument K, which the result replaces, the candidate k, and the
square (k + 1)². -/
slots Arg Cand Square

end Sqrt

open Sqrt in
/-- sqrt(K). -/
def sqrtBody : Stmt :=
  .set Cand (k 0) ;;
  .set Square (k 1) ;;
  .while (v Square ≤' v Arg) (
    .set Square (v Square +' k 2 *' v Cand +' k 3) ;;
    .set Cand (v Cand +' k 1)) ;;
  .set Arg (v Cand)

/-- The time of sqrt. -/
@[simp] def sqrtTime (K : ℕ) : ℕ := 18 * Nat.sqrt K + 12

/-- **sqrt(K)** returns ⌊√K⌋ and leaves the memory as it is. -/
theorem sqrt_meets {p K : ℕ} (hp : P[p]? = some sqrtBody) (μ : ℕ → ℤ)
    (hword : ((3 * K + 4 : ℕ) : ℤ) ≤ lim.word := by omega) :
    Meets lim P p d [K] μ (sqrtTime K) fun r μ' => r = (Nat.sqrt K : ℤ) ∧ μ' = μ := by
  have hle := K.sqrt_le
  have hlt := Nat.lt_succ_sqrt K
  have hself := K.sqrt_le_self
  refine .of_body hp ?_
  light_set 0
  light_set 1
  -- while sq ≤ K.  Before round i, k = i and sq = (i + 1)².
  refine Ends.next _ (Ends.whileBlock
    (fun i σ => σ = ⟨frame [K, i, ((i + 1) * (i + 1) : ℕ)], μ⟩) _ (by simp) ?_ ?_
    le_rfl)
  ·
    rintro i _ hi rfl
    have hsq : (i + 1) * (i + 1) ≤ Nat.sqrt K * Nat.sqrt K := Nat.mul_le_mul (by omega) (by omega)
    rw [show (i + 1 + 1) * (i + 1 + 1) = (i + 1) * (i + 1) + 2 * i + 3 by ring]
    generalize (i + 1) * (i + 1) = q at hsq
    -- The test is safe and holds.  sq := sq + 2 k + 3; k := k + 1 is safe and leads to the next
    -- state.
    exact ⟨by light_side, by light_side, by light_side, by simp [update_frame_setLocal]⟩
  ·
    rintro _ rfl
    generalize (Nat.sqrt K + 1) * (Nat.sqrt K + 1) = q at hlt
    refine ⟨by light_side, by light_side, ?_⟩
    -- the result is k
    light_set (Nat.sqrt K)
    simp
