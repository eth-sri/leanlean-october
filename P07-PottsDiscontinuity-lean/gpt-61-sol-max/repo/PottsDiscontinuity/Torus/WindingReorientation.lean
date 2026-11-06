module
public import Mathlib

public import PottsDiscontinuity.Torus.LoopReorientation
public import PottsDiscontinuity.Torus.LoopStatistics

/-!
# Vertical winding is independent of loop orientation

The explicit loop equivalence and edge-antisymmetry of algebraic crossings show
that reversing loops preserves their absolute vertical winding. This identifies the
canonical RC statistic U with the winding count in every compatible arrow orientation,
and proves the sector inclusion needed for Corollary 3.13(iii).
-/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

section

variable (ω₀ ω₁ : ArrowConfig N M) (s : Smoothing N M) (h₀ : CompatibleConfig ω₀ s) (h₁ : CompatibleConfig ω₁ s) (j : Fin M)


/-- A loop's vertical winding is preserved or negated, according to its orientation. -/
theorem loopVertical_reorient 
    (q : DirectedLoop ω₀ s h₀) :
    loopVertical ω₁ s h₁ j (loopReorientEquiv ω₀ ω₁ s h₀ h₁ q) =
      if loopOrientation ω₀ s h₀ ω₁ h₁ q then loopVertical ω₀ s h₀ j q
      else -loopVertical ω₀ s h₀ j q :=
  by
    solve_by_elim [_root_.PottsDiscontinuity.Torus.loopSum_reorient, _root_.PottsDiscontinuity.Torus.verticalCross_edgeReverse]

/-- The sum of absolute windings is independent of all loop-reversal choices. -/
theorem verticalMass_reorient  :
    verticalMass ω₁ s h₁ j = verticalMass ω₀ s h₀ j := by
  
  unfold verticalMass
  rw [← (loopReorientEquiv ω₀ ω₁ s h₀ h₁).sum_comp]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [loopVertical_reorient]
  grind

theorem verticalWindingCount_reorient  :
    verticalWindingCount ω₁ s h₁ j = verticalWindingCount ω₀ s h₀ j := by
  grind [verticalWindingCount, verticalMass_reorient]

end

section

variable (hN : Even N) (hM : Even M) (j : Fin M) (A : RCConfig N M) (ω : ArrowConfig N M) (h : CompatibleConfig ω (rcSmoothing A))
include h

/-- The canonically defined RC statistic equals the winding count of any of its orientations. -/
theorem rcVerticalWinding_eq_oriented  :
    rcVerticalWinding hN hM j A = verticalWindingCount ω (rcSmoothing A) h j :=
  by
    solve_by_elim [_root_.Eq.symm, _root_.PottsDiscontinuity.Torus.checkerArrows_compatible, _root_.PottsDiscontinuity.Torus.verticalWindingCount_reorient]

/-- The actual RC configuration underlying an oriented loop configuration in sector r
has U at least r. This is the event inclusion in the proof of Corollary 3.13(iii),
without assuming the unproved FK weight identity or a turning-number classification. -/
theorem sector_le_rcVerticalWinding 
    {r : ℕ} (hr : ω.absUp + r = N / 2) : r ≤ rcVerticalWinding hN hM j A := by
  rw [rcVerticalWinding_eq_oriented hN hM j A ω h]
  exact sector_le_verticalWindingCount hN ω (rcSmoothing A) h j hr

end

end PottsDiscontinuity.Torus
