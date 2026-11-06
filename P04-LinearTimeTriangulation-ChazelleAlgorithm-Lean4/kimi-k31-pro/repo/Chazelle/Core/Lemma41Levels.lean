module

public import Mathlib.Data.Nat.Log
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Chazelle.RewriteTactics

/-!
# WP-J, part 2: the levels of the balanced merge tree of Lemma 4.1

The `j` pieces of the cover are merged pairwise, level by level: level `t + 1` has
`lvlCount j (t + 1) = ⌈lvlCount j t / 2⌉` nodes; node `k` of level `t` covers the pieces
`[k 2^t, min ((k + 1) 2^t) j)` (`lvlLo`, `lvlHi`). After `⌈log₂ j⌉` levels one node is left
(`lvlCount_clog`), and `⌈log₂ j⌉ ≤ ⌈log₂ λ⌉ + 1` for `j ≤ 2λ` (`clog_le_of_le_two_mul`).
-/

namespace Chazelle.Core.L41

@[expose] public section

/-- **The merge depth**: `⌈log₂ j⌉ ≤ ⌈log₂ λ⌉ + 1` for `j ≤ 2λ`. -/
theorem clog_le_of_le_two_mul {j lam : ℕ} (hj : j ≤ 2 * lam) :
    Nat.clog 2 j ≤ Nat.clog 2 lam + 1 := by
  apply Nat.clog_le_of_le_pow
  have := Nat.le_pow_clog (b := 2) (by norm_num) lam
  rwo [pow_succ]

end

end Chazelle.Core.L41
