module

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

variable (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ)) (j : Fin M) (r : ℕ) (n : ℕ)

include hN hM j r in
/-- Configurations with at least `r` units of vertical loop winding. -/
def torusRCVerticalTail :
    Set (RCConfig N M) :=
  {A | r ≤ rcVerticalWinding hN hM j A}

include n in
/-- A positive even period parametrized without the empty period. -/
def positiveEvenPeriod : ℕ := 2 * (n + 1)

theorem positiveEvenPeriod_even : Even (positiveEvenPeriod n) := by
  simp [positiveEvenPeriod]

theorem positiveEvenPeriod_pos : 0 < positiveEvenPeriod n := by
  simp [positiveEvenPeriod]

include q in
/-- Logarithmic vertical-tail probability per vertical period, restricted to
positive even torus periods. -/
noncomputable def positiveEvenVerticalTailRate
    (r n m : ℕ) : ℝ :=
  let M := positiveEvenPeriod m
  Real.log (torusRCProbability (positiveEvenPeriod_even n) (positiveEvenPeriod_even m) q
    (torusRCVerticalTail (positiveEvenPeriod_even n) (positiveEvenPeriod_even m)
      ⟨0, positiveEvenPeriod_pos m⟩ r)) / (M : ℝ)

include q in
/-- Extended-real logarithmic rate, so a limit of `-∞` is represented without
requiring a separate uniform lower bound. -/
noncomputable def positiveEvenVerticalTailRateE
    (r n m : ℕ) : EReal :=
  (positiveEvenVerticalTailRate q r n m : EReal)

end PottsDiscontinuity.TorusRC
