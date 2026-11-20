module

public import QPBT.Combining.DirectLowDegree.GameValue

/-! # Probability bounds for the directly indexed low-degree game

This module records two elementary probability bounds needed when a caller caps an
assembled direct-game rejection estimate by one. The results are formalization-only
support: they do not bound any individual game branch or prove a passing-value theorem.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:178-186`
- Parent issue Dengnifer/MIPStarRE-QPBT-bak#119 and arithmetic issue
  Dengnifer/MIPStarRE-QPBT-bak#333
-/

@[expose] public section

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

namespace Strategy

/-- Every tensor-product strategy has nonnegative value. -/
theorem value_nonneg {G : Game} (S : Strategy G) : 0 ≤ S.value := by
  apply avgOver_nonneg
  intro questions
  apply Finset.sum_nonneg
  intro answerA _
  apply Finset.sum_nonneg
  intro answerB _
  split
  · apply outcomeWeight_nonneg
  · exact le_rfl

end Strategy

end MIPStarRE.QPBT
