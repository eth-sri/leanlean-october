/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Sec3.Corollary15_16
import ThreeSumApsp.TimeClaims.Sec3.Definitions

/-!
# The arithmetic behind the running-time claims of Section 3

Elementary inequalities that the deductions between running-time claims use silently.

* `⌈n^{1/3}⌉ ≥ 1` and `(log s + 1)^e ≥ 1`.
* Thin instances, `n ≥ D^18` (Theorem 5, Corollaries 15, 16 and 26): the overheads `n D`, `n² / √D`
  and `1` are at most `n² / D^a`, and so at most the bounds `n² log² D / D^{1/18}` and
  `n² / D^{0.063}`.
* The pieces into which Corollary 15 splits `W` have at most `n² / √D` query pairs (`splitCap_le`).
-/


namespace ThreeSumApsp

/-! ## Two quantities that are at least 1 -/

/-- `⌈n^{1/3}⌉ ≥ 1` for `n ≥ 1`. -/
theorem one_le_cbrtCeil {n : ℕ} (hn : 1 ≤ n) : 1 ≤ cbrtCeil n :=
  Nat.ceil_pos.2 (by positivity)

/-- `(log s + 1)^e ≥ 1`. -/
theorem one_le_log_add_one_pow (s e : ℕ) : 1 ≤ (Real.log s + 1) ^ e :=
  one_le_pow₀ (le_add_of_nonneg_left (Real.log_natCast_nonneg s))

/-! ## Thin instances: `n ≥ D^18` -/

/-! ## The pieces of Corollary 15 -/
