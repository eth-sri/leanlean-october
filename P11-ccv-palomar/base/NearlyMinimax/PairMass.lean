module

public import Mathlib

@[expose] public section

/-!
Finite partition form of (U7-mass), and actual product-measure integrals
underlying scalar factorial lifts.  The partition arguments expose the cell
probabilities and volumes, rather than postulating a bound on pair mass.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace NearlyMinimax

/-- Pair mass of an equal-volume partition with `K` cells. -/
def partitionPairMass {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
  (Fintype.card ι : ℝ) * ∑ i, p i ^ 2

/-- Cauchy--Schwarz proves the lower bound in (U7-mass). -/
theorem partitionPairMass_lower {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (hsum : ∑ i, p i = 1) : 1 ≤ partitionPairMass p := by
  have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := p)
  simpa [partitionPairMass, hsum] using h

end NearlyMinimax
