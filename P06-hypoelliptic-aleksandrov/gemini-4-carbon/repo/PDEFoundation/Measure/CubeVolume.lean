module

public import PDEFoundation.Geometry.AxisCube
public import PDEFoundation.Measure.RestrictedVolume
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Volume of axis-aligned cubes

Exact volume, positivity, and finiteness for the cube geometry shared with the
application repositories.
-/

@[expose] public section

namespace PDE

open MeasureTheory

theorem volume_axisCube_ne_top {d : ℕ}
    (z : Vec d) (L : ℝ) :
    volume (axisCube z L) ≠ ⊤ :=
  IsOpenBoundedConvexDomain.volume_ne_top
    (isOpenBoundedConvexDomain_axisCube z L)

theorem volume_axisCube_pos {d : ℕ}
    (z : Vec d) {L : ℝ} (hL : 0 < L) :
    0 < volume (axisCube z L) :=
  IsOpenBoundedConvexDomain.volume_pos
    (isOpenBoundedConvexDomain_axisCube z L)
    (axisCube_nonempty z hL)

theorem isFiniteMeasure_volumeOn_axisCube {d : ℕ}
    (z : Vec d) (L : ℝ) :
    IsFiniteMeasure (volumeOn (axisCube z L)) :=
  IsOpenBoundedConvexDomain.isFiniteMeasure_volumeOn
    (isOpenBoundedConvexDomain_axisCube z L)

end PDE
