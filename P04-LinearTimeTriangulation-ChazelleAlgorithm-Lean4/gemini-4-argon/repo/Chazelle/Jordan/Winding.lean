module

public import Chazelle.Mountain.Orientation

/-!
# Integer winding numbers of closed polygonal walks

For a point `z` and a directed edge from `u` to `v` the **signed crossing** `windInd z u v : ℤ`
refines the crossing bit `crossInd` of `Chazelle.Jordan.Parity`: it is `0` when the edge does not
cross the upward vertical ray from `z` (`crosses`, half-open rule), `-1` when it crosses it from
left to right (`u.1 < v.1`) and `+1` when it crosses it from right to left.  The **winding
number** of a closed walk (any vertex list, not necessarily simple) is
`windSum P z = ∑ i < n, windInd z (vtx i) (vtx (i+1))`.

Sign convention: this is the usual winding number, positive for counterclockwise walks; crossing
an edge from its right side to its left side (`det u v x > 0` is the left side) increases the
winding number by `1`.

Main results (for an arbitrary vertex list `P`):

* `windSum_cast`: `windSum` reduced mod 2 is `crossSum`;
* `windInd_swap`: reversing an edge negates its signed crossing — so a strand traversed once in
  each direction contributes nothing;
* `windInd_eventually`, `windSum_eventually_eq`: off the walk the winding number is locally
  constant (the signed endpoint contributions `windAbove` telescope);
* `continuousOn_windSum`, `windSum_eq_of_isPreconnected`: constancy on preconnected sets off the
  walk;
* `windSum_eq_zero_of_far`, `windSum_eq_zero_of_far_below`: far away the winding number is `0`;
* `windSum_jump`: **jump across edges** — if every edge through `z` is non-vertical with `z` in
  its relative interior, then for small `ε > 0`,
  `windSum (z.1, z.2 + ε) = windSum (z.1, z.2 - ε) + ∑_{edges j ∋ z} windDir j`, where
  `windDir u v = 1` for a left-to-right edge and `-1` otherwise.  In particular crossing a single
  strand from right to left adds `1`, and a doubled strand (traversed once each way) does not
  change the winding number;
* closed-walk calculus: `windPath` (signed crossing sum of an open path), `windPath_glue`,
  `windPath_reverse` (reversal negates), `windSum_eq_windPath`, `windSum_rotate`,
  `windSum_split` (cutting a closed walk along a segment `[a, b]` into two closed walks
  `a, Q, b` and `b, P, a`: the winding numbers add up);
* **simple polygons** (`windSum_eq_orient`, `windSum_eq_zero_of_not_mem_filled`): for a simple
  polygon the winding number is `orient P` (`±1`, `Chazelle.Mountain.orient`) on the interior
  and `0` outside the filled region.
-/

namespace Chazelle.Jordan

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Geometry (lerp lerp_fst lerp_snd det_lerp det_lerp_self lerp_mem_segment point_ext
  point_ext_iff)

/-! ### Definitions -/

/-- The signed crossing of the upward vertical ray from `z` by the directed edge `u → v`:
`-1` if the edge crosses it from left to right, `1` from right to left, `0` if it does not
cross it (`crosses`, half-open rule). -/
noncomputable def windInd (z u v : Point) : ℤ :=
  if crosses z u v then (if u.1 < v.1 then -1 else 1) else 0

/-! ### Basic lemmas -/

/-! ### Local behaviour of one edge -/

/-! ### Local constancy -/

/-! ### Far away -/

/-! ### Jump across edges -/

/-! ### Subdividing an edge -/

/-! ### Open paths and closed walks -/

/-- The signed crossing sum of the open polygonal path through the vertex list `L`. -/
noncomputable def windPath (z : Point) : List Point → ℤ
  | [] => 0
  | [_] => 0
  | a :: b :: l => windInd z a b + windPath z (b :: l)

@[simp] theorem windPath_nil (z : Point) : windPath z [] = 0 := rfl

@[simp] theorem windPath_singleton (z a : Point) : windPath z [a] = 0 := rfl

@[simp] theorem windPath_cons_cons (z a b : Point) (l : List Point) :
    windPath z (a :: b :: l) = windInd z a b + windPath z (b :: l) := rfl

/-! ### Simple polygons: the winding number is the orientation inside, `0` outside -/

end

end Chazelle.Jordan
