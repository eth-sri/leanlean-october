module

public import PottsDiscontinuity.TorusRC.MeasureFacts
public import PottsDiscontinuity.Torus.LoopStatistics

/-! # The zero-rate upper-tail case

This module records the exact `r = 1` case of (3.16), where the right-hand
side is zero. It is independent of the unresolved exponential estimate for
`r ≥ 2`.
-/

@[expose] public noncomputable section

open Filter

namespace PottsDiscontinuity.TorusRC

open Torus

variable {N M : ℕ}

section
variable (hN : Even N) (hM : Even M)
/-- Configurations with at least `r` units of vertical loop winding. -/
def torusRCVerticalTail (j : Fin M) (r : ℕ) :
    Set (RCConfig N M) :=
  {A | r ≤ rcVerticalWinding hN hM j A}

/-- Every torus vertical-winding tail has probability at most one, so its
logarithm is nonpositive. -/
theorem torusRCVerticalTail_log_nonpos (q : Set.Ici (1 : ℝ)) (j : Fin M) (r : ℕ) :
    Real.log (torusRCProbability hN hM q (torusRCVerticalTail hN hM j r)) ≤ 0 :=
  Real.log_nonpos
    (torusRCProbability_nonneg hN hM q (torusRCVerticalTail hN hM j r))
    (torusRCProbability_le_one hN hM q (torusRCVerticalTail hN hM j r))
end

section
variable (n : ℕ)
/-- A positive even period parametrized without the empty period. -/
def positiveEvenPeriod  : ℕ := 2 * (n + 1)

theorem positiveEvenPeriod_even  : Even (positiveEvenPeriod n) := by
  simp [positiveEvenPeriod]

theorem positiveEvenPeriod_pos  : 0 < positiveEvenPeriod n := by
  simp [positiveEvenPeriod]
end

section
variable (q : Set.Ici (1 : ℝ)) (r n m : ℕ)
/-- Logarithmic vertical-tail probability per vertical period, restricted to
positive even torus periods. -/
def positiveEvenVerticalTailRate  : ℝ :=
  let M := positiveEvenPeriod m
  Real.log (torusRCProbability (positiveEvenPeriod_even n) (positiveEvenPeriod_even m) q
    (torusRCVerticalTail (positiveEvenPeriod_even n) (positiveEvenPeriod_even m)
      ⟨0, positiveEvenPeriod_pos m⟩ r)) / (M : ℝ)

/-- Extended-real logarithmic rate, so a limit of `-∞` is represented without
requiring a separate uniform lower bound. -/
def positiveEvenVerticalTailRateE  : EReal :=
  (positiveEvenVerticalTailRate q r n m : EReal)
end

end PottsDiscontinuity.TorusRC
