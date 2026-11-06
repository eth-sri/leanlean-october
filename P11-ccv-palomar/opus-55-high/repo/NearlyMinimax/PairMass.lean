module

public import Mathlib
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-!
Finite partition form of (U7-mass), and actual product-measure integrals
underlying scalar factorial lifts.  The partition arguments expose the cell
probabilities and volumes, rather than postulating a bound on pair mass.
-/


𝚪
𝚵

𝚨

/-- Pair mass of an equal-volume partition with `K` cells. -/
def partitionPairMass [Fintype ι] (p : 𝙛) : ℝ :=
  (Fintype.card ι : ℝ) * ∑ i, p i ^ 2

/-- Cauchy--Schwarz proves the lower bound in (U7-mass). -/
theorem partitionPairMass_lower [Fintype ι] (p : 𝙛)
    (hsum : ∑ i, p i = 1) : 1 ≤ partitionPairMass p := by
  have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := p)
  aesop
