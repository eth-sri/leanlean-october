module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionOverlapCells
import Mathlib.Tactic

/-! # Finite-speed support on the source's time-position cells -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory

/- Strict future support forces the source time-bin index to precede the output index. -/
theorem positionOverlap_time_index (c : Clock) (s x : ℝ) (j i : ℕ) (k ell )
    (e z : Point) (he : e ∈ enlargedStartCell c s x j k)
    (hz : z ∈ enlargedStartCell c s x i ell) (ht : e.time < z.time) : j ≤ i := by
  by_contra hji
  have hj := lt_of_not_ge hji
  have helo := enlargedTimeBin_lower_strict c.r s e.time j (by omega) he.1
  have hzup := (enlargedTimeBin_bounds c.r s z.time i hz.1).2
  have hcast : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hj
  nlinarith only [helo, hzup, hcast, sq_nonneg c.r, ht]

/- Elapsed time on a source-output pair is bounded by the index difference plus one. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
