module

public import Mathlib.Data.Nat.Log
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-!
# WP-G, part 7: the dyadic cover of an interval, in two sweeps

The arc-cutter covers an interval `[x, y)` of edge indices of `Q` by aligned blocks
`[q 2^g, (q + 1) 2^g)` (the grade chains of the up phase), in `O(log (y - x))` steps, without
division: it keeps `q = x / 2^g` up to date (`q + 1` after a block, `q / 2` when `g` grows (a
table lookup), `2 q` when `g` shrinks).

* Upward (`upA`, then `upB`): blocks in increasing order (`Tiles x bs y`).
* Downward (`dnA`, then `dnB`): blocks in decreasing order from `y` (`TilesDn y bs x`), for the
  stretches where the walk descends through the vertices of `Q`.

Each block has `2^g ≤ y - x` (`upCover_blocks`, `dnCover_blocks`), and there are at most
`2 (log₂ (y - x) + 1)` of them.
-/

namespace Chazelle.Core

@[expose] public section

namespace ShootCut

/-! ## Upward -/

theorem pow_succ' (g : ℕ) : 2 ^ (g + 1) = 2 * 2 ^ g := by omega

/-! ## Downward -/

/-! ## Blocks of a tiling lie in the interval -/

end ShootCut

end

end Chazelle.Core
