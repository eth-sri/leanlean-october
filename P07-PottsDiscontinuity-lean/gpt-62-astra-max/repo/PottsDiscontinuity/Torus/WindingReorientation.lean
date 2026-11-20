module

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

variable (ω₀ ω₁ : ArrowConfig N M) (s : Smoothing N M) (h₀ : CompatibleConfig ω₀ s)
    (h₁ : CompatibleConfig ω₁ s) (hN : Even N) (hM : Even M) (j : Fin M)

/-- A loop's vertical winding is preserved or negated, according to its orientation. -/
theorem loopVertical_reorient
    (q : DirectedLoop h₀) :
    loopVertical j (loopReorientEquiv ω₀ ω₁ s h₀ h₁ q) =
      if loopOrientation ω₀ s h₀ h₁ q then loopVertical j q
      else -loopVertical j q :=
  loopSum_reorient ω₀ ω₁ s h₀ h₁ (verticalCross_edgeReverse j) q

/-- The sum of absolute windings is independent of all loop-reversal choices. -/
theorem verticalMass_reorient :
    verticalMass h₁ j = verticalMass h₀ j := by
  classical
  unfold verticalMass
  rw [← (loopReorientEquiv ω₀ ω₁ s h₀ h₁).sum_comp]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [loopVertical_reorient]
  grind

theorem verticalWindingCount_reorient {s : Smoothing N M}
    (h₀ : CompatibleConfig ω₀ s) (h₁ : CompatibleConfig ω₁ s) (j : Fin M) :
    verticalWindingCount h₁ j = verticalWindingCount h₀ j := by
  unfold verticalWindingCount
  rw [verticalMass_reorient ω₀ ω₁ s h₀ h₁ j]

/-- The canonically defined RC statistic equals the winding count of any of its orientations. -/
theorem rcVerticalWinding_eq_oriented
    (A : RCConfig N M) (ω : ArrowConfig N M) (h : CompatibleConfig ω (rcSmoothing A)) :
    rcVerticalWinding hN hM j A = verticalWindingCount h j :=
  (verticalWindingCount_reorient (checkerArrows N M) ω
    (checkerArrows_compatible hN hM (rcSmoothing A)) h j).symm

/-- The actual RC configuration underlying an oriented loop configuration in sector r
has U at least r. This is the event inclusion in the proof of Corollary 3.13(iii),
without assuming the unproved FK weight identity or a turning-number classification. -/
theorem sector_le_rcVerticalWinding
    {A : RCConfig N M} {ω : ArrowConfig N M} (h : CompatibleConfig ω (rcSmoothing A))
    {r : ℕ} (hr : ω.absUp + r = N / 2) : r ≤ rcVerticalWinding hN hM j A := by
  rw [rcVerticalWinding_eq_oriented hN hM j A ω h]
  exact sector_le_verticalWindingCount hN ω h j hr

end PottsDiscontinuity.Torus
