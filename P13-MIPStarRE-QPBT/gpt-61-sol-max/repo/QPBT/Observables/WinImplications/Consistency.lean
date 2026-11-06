module

public import QPBT.Observables.WinImplications.MagicSquare

/-!
# Exact consistency winning implication

This module proves the exact same-question consistency bound for the two
players' Pauli-test measurements.

## References

The strategy consistency theorem proves item 1
of `lem:qld-win-implications`
from `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:192-267`
and blueprint `lem:qld-win-implications` and `lem:qld-win-implications-obs`.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

namespace WinImplications

/-- The self-loop verifier edge at one Pauli question type. This is the edge
used for item 1 of `lem:qld-win-implications`, paper
`14_analysis_of_the_pauli_basis_test.tex:197-199`. -/
def pauliLoopEdge (t : PauliType) : PauliEdge :=
  ⟨(t, t), by simp [pauliEdges]⟩

/-- Unequal answers to the same sampled question are rejected on its self-loop.
This is the rejection event used for item 1 of `lem:qld-win-implications`, paper
`14_analysis_of_the_pauli_basis_test.tex:197-199`. -/
theorem loopMismatch_le_rejection {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (t : PauliType) (z : PauliSpace P) :
    outcomeEventWeight S.toStrategy
        (t, pauliCL P t z) (t, pauliCL P t z) (fun A B => A ≠ B) ≤
      pauliRejectionAt S.toStrategy (pauliLoopEdge t) z := by
  unfold pauliRejectionAt pauliSourceQuestions pauliLoopEdge
  dsimp
  apply outcome_event_weight_mono
  intro A B hne
  simp only [pauliWinPredicate, Bool.and_eq_true, ↓reduceIte,
    Bool.if_false_right, Bool.decide_and, Bool.decide_eq_true,
    Bool.and_eq_false_imp, decide_eq_false_iff_not, and_imp]
  intro _ _
  exact hne

end WinImplications

end

end MIPStarRE.QPBT
