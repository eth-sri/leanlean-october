module
public import Mathlib

public import PottsDiscontinuity.TorusRC.MeasureFacts
public import PottsDiscontinuity.Torus.LoopStatistics

/-! # The zero-rate upper-tail case

This module records the exact `r = 1` case of (3.16), where the right-hand
side is zero. It is independent of the unresolved exponential estimate for
`r ≥ 2`.
-/

@[expose] public section

open Filter

namespace PottsDiscontinuity.TorusRC

open Torus

variable {N M : ℕ}

/-- Configurations with at least `r` units of vertical loop winding. -/
def torusRCVerticalTail (hN : Even N) (hM : Even M) (j : Fin M) (r : ℕ)  :=
  {A | r ≤ rcVerticalWinding hN hM j A}

/-- Every torus vertical-winding tail has probability at most one, so its
logarithm is nonpositive. -/
theorem torusRCVerticalTail_log_nonpos (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (j : Fin M) (r : ℕ) :
    Real.log (torusRCProbability hN hM q (torusRCVerticalTail hN hM j r)) ≤ 0 := by
                                                                                   solve_by_elim [_root_.Real.log_nonpos, _root_.PottsDiscontinuity.TorusRC.torusRCProbability_nonneg, _root_.PottsDiscontinuity.TorusRC.torusRCProbability_le_one]

/-- A positive even period parametrized without the empty period. -/
def positiveEvenPeriod (n : ℕ) : ℕ := 2 * (n + 1)

theorem positiveEvenPeriod_even (n : ℕ) : Even (positiveEvenPeriod n) := by
  grind +locals

theorem positiveEvenPeriod_pos (n : ℕ) : 0 < positiveEvenPeriod n := by
  simp [positiveEvenPeriod]

/-- Logarithmic vertical-tail probability per vertical period, restricted to
positive even torus periods. -/
noncomputable def positiveEvenVerticalTailRate (q : Set.Ici (1 : ℝ))
    (r n m : ℕ)  :=
  let M := positiveEvenPeriod m
  Real.log (torusRCProbability (positiveEvenPeriod_even n) (positiveEvenPeriod_even m) q
    (torusRCVerticalTail (positiveEvenPeriod_even n) (positiveEvenPeriod_even m)
      ⟨0, positiveEvenPeriod_pos m⟩ r)) / (M : ℝ)

/-- Extended-real logarithmic rate, so a limit of `-∞` is represented without
requiring a separate uniform lower bound. -/
noncomputable def positiveEvenVerticalTailRateE (q : Set.Ici (1 : ℝ))
    (r n m : ℕ)  :=
  (positiveEvenVerticalTailRate q r n m : EReal)

end PottsDiscontinuity.TorusRC
