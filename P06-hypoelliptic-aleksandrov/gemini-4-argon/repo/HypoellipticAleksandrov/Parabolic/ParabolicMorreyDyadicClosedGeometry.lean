module

public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyDyadicForwardBox
public import Mathlib.Tactic

/-!
# Closed dyadic forward-box geometry for parabolic Morrey estimates

This module derives literal closed dyadic forward-box nesting from the
open forward-box containments.  It contains no projection estimate,
tail, chain, residual, or representative result.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace HypoellipticAleksandrov.Parabolic

noncomputable section

/-- A literal closed dyadic forward child box is contained in its literal
closed forward parent box. -/
theorem parabolicDyadicClosedForwardBox_child_subset
    {d n } (index : ParabolicDyadicIndex d n)
    (child : ParabolicDyadicChild d) :
    parabolicClosedBox 1
        (parabolicDyadicSourceBox
          (parabolicDyadicChildIndex index child)).radius
        (parabolicDyadicSourceBox
          (parabolicDyadicChildIndex index child)).baseTime
        (parabolicDyadicSourceBox
          (parabolicDyadicChildIndex index child)).center ⊆
      parabolicClosedBox 1
        (parabolicDyadicSourceBox index).radius
        (parabolicDyadicSourceBox index).baseTime
        (parabolicDyadicSourceBox index).center := by
  have hchildRadius :=
    parabolicDyadicSourceBox_radius_pos (parabolicDyadicChildIndex index child)
  have hparentRadius :=
    parabolicDyadicSourceBox_radius_pos index
  rw [← closure_parabolicBox_of_pos (d := d) (vartheta := (1 : Real))
        (r := (parabolicDyadicSourceBox
          (parabolicDyadicChildIndex index child)).radius)
        (t0 := (parabolicDyadicSourceBox
          (parabolicDyadicChildIndex index child)).baseTime)
        (v0 := (parabolicDyadicSourceBox
          (parabolicDyadicChildIndex index child)).center) (by norm_num) hchildRadius,
    ← closure_parabolicBox_of_pos (d := d) (vartheta := (1 : Real))
        (r := (parabolicDyadicSourceBox index).radius)
        (t0 := (parabolicDyadicSourceBox index).baseTime)
        (v0 := (parabolicDyadicSourceBox index).center) (by norm_num) hparentRadius]
  exact closure_mono (parabolicDyadicForwardBox_child_subset index child)

end

end HypoellipticAleksandrov.Parabolic
