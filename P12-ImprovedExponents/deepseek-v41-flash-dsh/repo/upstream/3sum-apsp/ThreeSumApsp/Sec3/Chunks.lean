/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaperStatements
public import ThreeSumApsp.Util.Ceil
public import ThreeSumApsp.Util.Counting
public import ThreeSumApsp.TacticsShort

/-!
# Cutting a set of pairs into chunks

Corollary 15 splits the query pairs "into sets of at most n²/√D query pairs", and the proof of
Theorem 17 cuts each set `W_ϱ` "into chunks of at most n²/√D query pairs".  In both, the chunk
number `j` of `S` holds the pairs of `S` whose rank in row-major order, divided by `cap`, is `j`.

* A chunk has at most `cap` pairs (`card_chunk_le`), because different pairs of `S` have different
  ranks (`rankIn_injOn`).
* The first `⌈|S|/cap⌉` chunks cover `S` (`biUnion_chunk`).
* In both uses `cap = ⌊n²/√D⌋`, which is at least 1 for `1 ≤ D ≤ n` (`one_le_queryCap`).
-/

public section

namespace ThreeSumApsp

variable {n : ℕ} {S : Finset (Fin n × Fin n)} {cap : ℕ}

/-! ### Ranks -/

/-! ### Chunks -/

/-! ### The size of the chunks in Corollary 15 and in Theorem 17 -/

/-- `√D ≤ D ≤ n`. -/
theorem sqrt_le_natCast {D : ℕ} (hD : 1 ≤ D) (hDn : D ≤ n) : Real.sqrt D ≤ n :=
  calc Real.sqrt D ≤ Real.sqrt D * Real.sqrt D :=
        le_mul_of_one_le_left (Real.sqrt_nonneg _) (Real.one_le_sqrt.mpr ((by exact_mod_cast hD)))
    _ = D := Real.mul_self_sqrt (Nat.cast_nonneg D)
    _ ≤ n := by exact_mod_cast hDn

/-- The bound `⌊n²/√D⌋` on the size of a chunk is at least 1, because `√D ≤ n ≤ n²`. -/
theorem one_le_queryCap {D : ℕ} (hD : 1 ≤ D) (hDn : D ≤ n) : 1 ≤ queryCap n D := by
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast hD.trans hDn
  refine Nat.le_floor ?_
  rw [Nat.cast_one, le_div_iff₀ (Real.sqrt_pos.mpr ((by exact_mod_cast hD))), one_mul]
  exact (sqrt_le_natCast hD hDn).trans (le_self_pow₀ hn two_ne_zero)

end ThreeSumApsp