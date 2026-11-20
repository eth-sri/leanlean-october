module

public import Chazelle.Core.SweepLocal

/-!
# The sweep (WP-D), part 13: detection shots (soundness)

The event loop of the sweep finds the next event on the walk of `C₁` by shooting, in the model of
`C₁`, from an endpoint `a` of a candidate chord of `S₂` at the arcs of the current region `U` of
`S₁` (the region of the current window).  The first hit `w` on those arcs need not be the first
point of the walk hit by the ray: the ray may leave the domain before `w` and re-enter it.

* `not_mem_dom_of_boundary`: a point of the ray that is a limit of points of a region but is not
  in it lies off the domain (it is not on a chord: a horizontal ray meets a chord only along it).
* `ray_in_region_of_firstHit` (**soundness of a detection shot**): if the ray arrives at the first
  hit `w` on the arcs of `U` from inside `U`, the whole ray before `w` lies in `U`; so `w` is the
  first point of the walk hit by the ray, and the segment from `a` to `w` is free.
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (freeIn regionsIn)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Geometry (lerp point_ext)

namespace Sweep

section ChainModel

variable (C : Chain)

/-- The ray points from a later origin, backwards. -/
theorem rayPt_back (a : Point) (σ τ' s : ℝ) :
    rayPt (rayPt a σ τ') (-σ) s = rayPt a σ (τ' - s) := by
  apply point_ext <;> simp [rayPt]; ring

end ChainModel

end Sweep

end

end Chazelle.Core
