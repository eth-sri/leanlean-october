module

public import PDEFoundation.Geometry.AxisCube
public import PDEFoundation.Measure.RestrictedVolume
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Volume of axis-aligned cubes

Exact volume, positivity, and finiteness for the cube geometry shared with the
application repositories.
-/

 public section

namespace PDE

open MeasureTheory

variable {d : ℕ} (z : Vec d)

theorem volume_axisCube_ne_top  (L : ℝ) :
    volume (axisCube z L) ≠ ⊤ :=
  IsOpenBoundedConvexDomain.volume_ne_top
    (isOpenBoundedConvexDomain_axisCube z L)

theorem volume_axisCube_pos  {L : ℝ} (hL : 0 < L) :
    0 < volume (axisCube z L) :=
  IsOpenBoundedConvexDomain.volume_pos
    (isOpenBoundedConvexDomain_axisCube z L)
    (axisCube_nonempty z hL)

theorem isFiniteMeasure_volumeOn_axisCube  (L : ℝ) :
    IsFiniteMeasure (volumeOn (axisCube z L)) :=
  IsOpenBoundedConvexDomain.isFiniteMeasure_volumeOn
    (isOpenBoundedConvexDomain_axisCube z L)

end PDE
