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

theorem parabolicDyadicSourceBox_radius_rpow_truncate_mul
    {d m n : Nat} (hmn : m <= n) (index : ParabolicDyadicIndex d n)
    (alpha : Real) :
    (parabolicDyadicSourceBox (parabolicDyadicTruncate hmn index)).radius ^ alpha *
        ((2 : Real) ^ (-alpha)) ^ (n - m) =
      (parabolicDyadicSourceBox index).radius ^ alpha := by
  change ((2 : Real) ^ m)⁻¹ ^ alpha * ((2 : Real) ^ (-alpha)) ^ (n - m) =
    ((2 : Real) ^ n)⁻¹ ^ alpha
  have hbase (k : Nat) : ((2 : Real) ^ k)⁻¹ ^ alpha =
      (2 : Real) ^ (-(k : Real) * alpha) := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg (by norm_num : (0 : Real) <= 2),
      ← Real.rpow_mul (by norm_num : (0 : Real) <= 2)]
  have hfactor : ((2 : Real) ^ (-alpha)) ^ (n - m) =
      (2 : Real) ^ (-alpha * ((n - m : Nat) : Real)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : Real) <= 2)]
  rw [hbase m, hbase n, hfactor, ← Real.rpow_add (by norm_num : (0 : Real) < 2)]
  congr 1
  rw [Nat.cast_sub hmn]
  ring

section
variable {d n : Nat} (index : ParabolicDyadicIndex d n)

/-- The existing dyadic source-box data is literally the forward box used by
the physical Morrey projection. -/
theorem parabolicDyadicOpenCell_eq_parabolicBox :
    parabolicDyadicOpenCell index =
      parabolicBox 1
        (parabolicDyadicSourceBox index).radius
        (parabolicDyadicSourceBox index).baseTime
        (parabolicDyadicSourceBox index).center := by
  change parabolicDyadicOpenCell index =
    inkSpotsSourceBox (parabolicDyadicSourceBox index)
  exact (inkSpotsSourceBox_parabolicDyadicSourceBox index).symm

/-- One simultaneous dyadic refinement halves the forward-box radius. -/
theorem parabolicDyadicSourceBox_radius_childIndex
    (child : ParabolicDyadicChild d) :
    (parabolicDyadicSourceBox (parabolicDyadicChildIndex index child)).radius =
      (parabolicDyadicSourceBox index).radius / 2 := by
  change ((2 : Real) ^ (n + 1))⁻¹ = ((2 : Real) ^ n)⁻¹ / 2
  rw [pow_succ]
  field_simp

/-- The corresponding child forward box is contained in its parent forward
box, in the orientation expected by normalized restriction. -/
theorem parabolicDyadicForwardBox_child_subset
    (child : ParabolicDyadicChild d) :
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
  rw [← parabolicDyadicOpenCell_eq_parabolicBox
        (parabolicDyadicChildIndex index child),
    ← parabolicDyadicOpenCell_eq_parabolicBox index]
  exact parabolicDyadicOpenCell_child_subset index child

end

/-- The dyadic forward-box diameter scale tends to zero. -/
theorem tendsto_two_mul_parabolicDyadicSourceBox_radius_atTop :
    Tendsto (fun n : Nat => 2 * ((2 : Real) ^ n)⁻¹) atTop (nhds 0) := by
  have heq : parabolicDyadicVelocityWidth =
      (fun n : Nat => 2 * ((2 : Real) ^ n)⁻¹) := by
    funext n
    exact rfl
  rw [← heq]
  exact tendsto_parabolicDyadicVelocityWidth_atTop

end

end HypoellipticAleksandrov.Parabolic
