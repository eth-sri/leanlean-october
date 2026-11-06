module

public import Chazelle.Core.DownPhaseTourA
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.MiscTactics
public import Chazelle.ChainTactics

/-!
# WP-M (T, part 1): side `B` of the tour of a chain

The tour of `C.sideWalk β` passes chain edge `k` (between vertices `k` and `k + 1`) a second time
with decreasing vertex index (**side `B`**), at tour position `2m - (k + 1)`.  `tourB β k` is the
tour index of that pass: walk edge `tourB β k + 6` goes from `C.vertex (k + 1)` to `C.vertex k`.
This mirrors `TourA` (the transition uses side `B` when the interior of `Q` lies to the right of
`Q`'s own vertex order).
-/

namespace Chazelle.Core

namespace TourB

@[expose] public section

open Set
open Chazelle.Chain (sidePt sideLeft sideLeftOf sideE)
open Chazelle.Geometry (lerp)
open TourA (sA tourA)

variable (C : Chain) (β : Bool)

/-- **The side-`B` tour index** of chain edge `k`. -/
noncomputable def tourB (k : ℕ) : ℕ := tourA C β (2 * C.m - (k + 1))

variable {C β}

theorem tourB_lt (k : ℕ) : tourB C β k < 2 * C.m := TourA.tourA_lt _

theorem sideIdx_tourB {k : ℕ} (hk : k < C.m) : C.sideIdx β (tourB C β k) = k + 1 := by
  unfold tourB
  rw [Chain.sideIdx_eq, TourA.mod_tourA (by omega)]
  unfold sideE; splao

theorem sideIdx_tourB_succ {k : ℕ} (hk : k < C.m) : C.sideIdx β (tourB C β k + 1) = k := by
  unfold tourB
  rw [C.sideIdx_succ, TourA.mod_tourA (by omega)]
  uro sideE [ite_eq_right (by omega)]

theorem vtx_tourB {k : ℕ} (hk : k < C.m) :
    (C.sideWalk β).vtx (tourB C β k + 6) = C.vertex (k + 1) := by
  rw [C.sideWalk_vtx_tour β (tourB_lt k).le]
  unfold Chain.sideTour; rw [sideIdx_tourB hk]

theorem vtx_tourB_succ {k : ℕ} (hk : k < C.m) :
    (C.sideWalk β).vtx ((tourB C β k + 6 + 1) % (C.sideWalk β).n) = C.vertex k := by
  rw [C.sideWalk_next_tour β (tourB_lt k), C.sideWalk_vtx_tour β (tourB_lt k)]
  unfold Chain.sideTour; rw [sideIdx_tourB_succ hk]

/-- **Contiguity of side `B`**: the pass of edge `k` follows the pass of edge `k + 1`, except at
the tour start. -/
theorem tourB_succ {k : ℕ} (hk : k + 1 < C.m) (hne : 2 * C.m - (k + 1) ≠ sA C β) :
    tourB C β k = tourB C β (k + 1) + 1 := by
  unfold tourB
  have := TourA.tourA_succ (C := C) (β := β) (k := 2 * C.m - (k + 2)) (by omega)
    (by rwx [show 2 * C.m - (k + 2) + 1 = 2 * C.m - (k + 1) by omega])
  rw [show 2 * C.m - (k + 2) + 1 = 2 * C.m - (k + 1) by omega] at this
  rw [this, show 2 * C.m - (k + 1 + 1) = 2 * C.m - (k + 2) by omega]

end

end TourB

end Chazelle.Core
