module

public import HypoellipticAleksandrov.Measure.ParabolicDyadicInkSpotsBridge
public import HypoellipticAleksandrov.Measure.ParabolicDyadicOpenCover
public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyGeometry

/-!
# Dyadic forward boxes for parabolic Morrey geometry

This module exposes the open dyadic cells as the literal forward
coordinate boxes used by the Morrey layer.  It deliberately does not identify
the half-open partition cells with these boxes.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace HypoellipticAleksandrov.Parabolic

noncomputable section

variable {d n : Nat} (index : ParabolicDyadicIndex d n) (child : ParabolicDyadicChild d)

/-- The existing dyadic source-box data is literally the forward box used by
the physical Morrey projection. -/
theorem parabolicDyadicOpenCell_eq_parabolicBox
     :
    parabolicDyadicOpenCell index =
      parabolicBox 1
        (parabolicDyadicSourceBox index).radius
        (parabolicDyadicSourceBox index).baseTime
        (parabolicDyadicSourceBox index).center := (inkSpotsSourceBox_parabolicDyadicSourceBox index).symm

/-- One simultaneous dyadic refinement halves the forward-box radius. -/
theorem parabolicDyadicSourceBox_radius_childIndex
     :
    (parabolicDyadicSourceBox (parabolicDyadicChildIndex index child)).radius =
      (parabolicDyadicSourceBox index).radius / 2 := by
  change ((2 : Real) ^ (n + 1))⁻¹ = ((2 : Real) ^ n)⁻¹ / 2
  ring

/-- The corresponding child forward box is contained in its parent forward
box, in the orientation expected by normalized restriction. -/
theorem parabolicDyadicForwardBox_child_subset
     :
    parabolicBox 1
        (parabolicDyadicSourceBox
          (parabolicDyadicChildIndex index child)).radius
        (parabolicDyadicSourceBox
          (parabolicDyadicChildIndex index child)).baseTime
        (parabolicDyadicSourceBox
          (parabolicDyadicChildIndex index child)).center ⊆
      parabolicBox 1
        (parabolicDyadicSourceBox index).radius
        (parabolicDyadicSourceBox index).baseTime
        (parabolicDyadicSourceBox index).center := by
  rw [← parabolicDyadicOpenCell_eq_parabolicBox,
    ← parabolicDyadicOpenCell_eq_parabolicBox]
  exact parabolicDyadicOpenCell_child_subset index child

/-- The dyadic forward-box diameter scale tends to zero. -/
theorem tendsto_two_mul_parabolicDyadicSourceBox_radius_atTop :
    Tendsto (fun n : Nat => 2 * ((2 : Real) ^ n)⁻¹) atTop (nhds 0) := tendsto_parabolicDyadicVelocityWidth_atTop

end

end HypoellipticAleksandrov.Parabolic
