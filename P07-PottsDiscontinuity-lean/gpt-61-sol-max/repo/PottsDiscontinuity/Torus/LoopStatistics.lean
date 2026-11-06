module
public import Mathlib

public import PottsDiscontinuity.Torus.DiamondGraph
public import PottsDiscontinuity.Torus.LoopCrossings

/-!
# Vertical winding counts and the sector bound

Parity of the signed flux proves the evenness of the total absolute vertical winding
without a classification of essential loops. The canonical checkerboard orientation
then defines the unoriented RC statistic U using the actual smoothed loop cycles.
Its independence of other choices of loop orientation is a separate proof obligation.
-/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

/-- Parity, rather than parallelism of essential loops, already proves that the total
absolute vertical winding is even. -/
theorem verticalMass_even (hN : Even N) (ω : ArrowConfig N M) (s : Smoothing N M)
    (h : CompatibleConfig ω s) (j : Fin M) : Even (verticalMass ω s h j) := by
  apply ZMod.natCast_eq_zero_iff_even.mp
  calc
     verticalMass ω s h j  =
        ((∑ q : DirectedLoop ω s h, loopVertical ω s h j q : ℤ) : ZMod 2) := by
      simp_all [verticalMass]
    _ =  (2 *  ω.absUp  - N : ℤ)  := by rw [sum_loopVertical]
    _ = 0 := by
      have hn  := hN.natCast_zmod_two
      have htwo : (2 : ZMod 2) = 0 := by decide
      simp_all

/-- Half the actual absolute vertical displacement winding, for a directed loop partition. -/
noncomputable def verticalWindingCount (ω : ArrowConfig N M) (s : Smoothing N M)
    (h : CompatibleConfig ω s) (j : Fin M) : ℕ := verticalMass ω s h j / 2

section

variable (hN : Even N) (ω : ArrowConfig N M) (s : Smoothing N M) (h : CompatibleConfig ω s) (j : Fin M)
include hN

theorem two_mul_verticalWindingCount  :
    2 * verticalWindingCount ω s h j = verticalMass ω s h j := by
                                                                 solve_by_elim [_root_.Nat.mul_div_cancel', _root_.Even.two_dvd, _root_.PottsDiscontinuity.Torus.verticalMass_even]

/-- The up-arrow sector forces at least r pairs of absolute vertical windings. -/
theorem sector_le_verticalWindingCount  {r : ℕ}
    (hr : ω.absUp + r = N / 2) : r ≤ verticalWindingCount ω s h j := by
  have hb := two_mul_sector_le_verticalMass hN ω s h j hr
  have he := two_mul_verticalWindingCount hN ω s h j
  omega

end

/-- The RC loop-count statistic ell, using the canonical orientation of its smoothing. -/
noncomputable def rcLoopCount (hN : Even N) (hM : Even M) (A : RCConfig N M)  :=
  loopCount hN hM (rcSmoothing A)

/-- The RC vertical statistic U: half the sum of absolute vertical windings of its loops.
The row is an explicit nonempty reference-line index; there is no empty-torus fallback. -/
noncomputable def rcVerticalWinding (hN : Even N) (hM : Even M) (j : Fin M)
    (A : RCConfig N M)  :=
  verticalWindingCount (checkerArrows N M) (rcSmoothing A)
    (checkerArrows_compatible hN hM (rcSmoothing A)) j

end PottsDiscontinuity.Torus
