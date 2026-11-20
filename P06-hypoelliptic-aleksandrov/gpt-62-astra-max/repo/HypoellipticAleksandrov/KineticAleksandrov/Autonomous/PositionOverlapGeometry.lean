module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionOverlapCells
import Mathlib.Tactic

/-! # Finite-speed support on the source's time-position cells -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory

variable (c : Clock) (s x : ℝ) (j i : ℕ) (k ell : ℤ) (e z : Point)
    (he : e ∈ enlargedStartCell c s x j k) (hz : z ∈ enlargedStartCell c s x i ell)
    (ht : e.time < z.time)
include he hz

include ht in
/-- Strict future support forces the source time-bin index to precede the output index. -/
theorem positionOverlap_time_index : j ≤ i := by
  by_contra hji
  have hj := lt_of_not_ge hji
  have helo := enlargedTimeBin_lower_strict c.r s e.time j (by omega) he.1
  have hzup := (enlargedTimeBin_bounds c.r s z.time i hz.1).2
  have hcast : i + 1 ≤ (j : ℝ) := by exact_mod_cast hj
  nlinarith only [helo, hzup, hcast, sq_nonneg c.r, ht]

/-- Elapsed time on a source-output pair is bounded by the index difference plus one. -/
theorem positionOverlap_elapsed :
    z.time - e.time ≤ ((i : ℝ) - (j : ℝ) + 1) * c.r ^ 2 := by
  linarith [(enlargedTimeBin_bounds c.r s e.time j he.1).1, (enlargedTimeBin_bounds c.r s z.time i hz.1).2]

include ht in
/-- Speed at most `3r` permits only linearly many position-cell differences. -/
theorem positionOverlap_position_index
    (hcone : |z.position 0 - e.position 0| ≤ 3 * c.r * (z.time - e.time)) :
    |((ell - k : ℤ) : ℝ)| ≤ 5 * ((i : ℝ) - (j : ℝ) + 1) := by
  have hcast : j ≤ (i : ℝ) := by exact_mod_cast (positionOverlap_time_index c s x j i k ell e z he hz ht)
  have hd : 1 ≤ i - (j : ℝ) + 1 := by linarith only [hcast]
  have hs : |z.position 0 - e.position 0| ≤
      3 * (i - j + 1) * c.r ^ 3 := by
    apply hcone.trans
    calc
      _ ≤ 3 * c.r * ((i - j + 1) * c.r ^ 2) :=
        mul_le_mul_of_nonneg_left (positionOverlap_elapsed c s x j i k ell e z he hz) (by linarith [c.positive])
      _ = _ := by ring
  have hep := he.2
  have hzp := hz.2
  have hr3 := pow_pos c.positive 3
  have hleft : (ell - k) * c.r ^ 3 ≤
      (3 * (i - j + 1) + 1) * c.r ^ 3 := by
    nlinarith only [hep.2, hzp.1, hs, (le_abs_self (z.position 0 - e.position 0))]
  have hright : -(ell - k) * c.r ^ 3 ≤
      (3 * (i - j + 1) + 1) * c.r ^ 3 := by
    nlinarith only [hep.1, hzp.2, hs, (neg_le_abs (z.position 0 - e.position 0))]
  have hl := (mul_le_mul_iff_left₀ hr3).mp hleft
  have hr := (mul_le_mul_iff_left₀ hr3).mp hright
  rw [Int.cast_sub, abs_le]
  constructor <;> linarith only [hl, hr, hd]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
