/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Sec3.Parameters
public import Mathlib.Algebra.Order.Floor.Semifield
public import ThreeSumApsp.TacticsShort

/-!
# The cost analysis of Theorem 19 for a general choice of the parameters

The two halves of the proof of Theorem 19 are the same computation with different numbers.  Both
apply Theorem 17 with a number `D ≥ 16` between `n^{1/18}/c` and `n^{1/18}` and with `g = ⌈D^η⌉`,
and solve each of the at most `4ng` instances with a saving `D^{2η}`.  Such a pair `D`, `η` is a
`Choice`, and the computation is carried out here for every choice.

1. A choice satisfies the hypotheses `16 ≤ D ≤ n` and `1 ≤ g ≤ √D` of Theorem 17 and the hypothesis
   `D^18 ≤ n` of Corollaries 15 and 16 (`Choice.sixteen_le`, `Choice.le_n`, `Choice.one_le_ceil`,
   `Choice.ceil_le_sqrt`, `Choice.pow_eighteen_le`).
2. The lower bound on `D` gives `D^{-η} ≤ c^η n^{-η/18}` (`Choice.saving`), and the upper bound
   gives `D^a ≤ n^{a/18}` (`Choice.rpow_le_rpow_div`).
3. Each of the four terms of the running time is `O(n^{3-η/18})` up to logarithms: the instances
   (`Choice.instances_le`) and the scans (`Choice.scans_le`) by the first bound, the choice of `p`
   (`Choice.strassen_le`) and building the instances (`Choice.build_le`) by the second.
4. So is their sum (`exists_total_le`).
-/

@[expose] public section

namespace ThreeSumApsp

namespace Theorem19

/-- A choice of the parameters of Theorem 17 as in both halves of the proof of Theorem 19: `D ≥ 16`
lies between `n^{1/18}/c` and `n^{1/18}`, and `g = ⌈D^η⌉` with `0 ≤ η ≤ 1/4`. -/
structure Choice (n D : ℕ) (η c : ℝ) : Prop where
  /-- `D ≥ 16`, as Theorem 17 asks. -/
  sixteen_le : 16 ≤ D
  /-- `D ≤ n^{1/18}`. -/
  le_root : (D : ℝ) ≤ (n : ℝ) ^ (1 / 18 : ℝ)
  /-- `D ≥ n^{1/18}/c`. -/
  root_div_le : (n : ℝ) ^ (1 / 18 : ℝ) / c ≤ (D : ℝ)
  /-- The constant `c` is positive. -/
  c_pos : 0 < c
  /-- `η ≥ 0`. -/
  η_nonneg : 0 ≤ η
  /-- `η ≤ 1/4`, so that `g ≤ √D`. -/
  η_le : η ≤ 1 / 4

/-- `x ≤ n^{1/18}` says that `x^18 ≤ n`. -/
theorem le_root_iff (x n : ℕ) : (x : ℝ) ≤ (n : ℝ) ^ (1 / 18 : ℝ) ↔ x ^ 18 ≤ n := by
  have h := Real.natCast_le_rpow_inv_iff (e := 18) tac_norm_num x n
  rwa [show ((18 : ℕ) : ℝ)⁻¹ = 1 / 18 by norm_num] at h

namespace Choice

variable {n D : ℕ} {η c : ℝ} (P : Choice n D η c)
include P

/-! ### The hypotheses of Theorem 17 and of Corollaries 15 and 16 -/

/-- "Corollary 15 [...] applies because D^{18} ≤ n", and likewise Corollary 16. -/
theorem pow_eighteen_le : D ^ 18 ≤ n :=
  (le_root_iff D n).mp P.le_root

/-- `D ≤ n`, as Theorem 17 asks. -/
theorem le_n : D ≤ n :=
  (Nat.le_self_pow tac_norm_num D).trans P.pow_eighteen_le

private theorem one_le_D : (1 : ℝ) ≤ D :=
  Nat.one_le_cast.mpr (le_trans tac_norm_num P.sixteen_le)

private theorem D_pos : (0 : ℝ) < D :=
  zero_lt_one.trans_le P.one_le_D

/-! ### Logarithms -/

/-- `log D ≤ log n`. -/
theorem log_le_log : Real.log D ≤ Real.log n :=
  Real.log_le_log P.D_pos (Nat.cast_le.mpr P.le_n)

/-! ### Powers of `D` in terms of `n` -/

/-! ### The four terms of the running time

`Λ` is the logarithmic factor of the result, `log² n` or `log n`. -/

end Choice

end Theorem19

end ThreeSumApsp