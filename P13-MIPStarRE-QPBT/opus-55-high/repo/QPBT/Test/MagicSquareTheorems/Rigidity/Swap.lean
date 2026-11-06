module

public import QPBT.Test.MagicSquareTheorems.PerfectStrategy.Observables
public import QPBT.Test.MagicSquareTheorems.Rigidity.Anticommutation

/-!
# Swap-isometry extraction for Magic Square rigidity

This module constructs the local swap isometries used in the finite-dimensional
proof of Magic Square rigidity.  A binary observable `Z` splits a local vector
into its two eigenspaces, while a second binary observable `X` identifies the
negative eigenspace with the residual copy of the original Hilbert space.
Crucially, the resulting map is an exact isometry even when `X` and `Z`
anticommute only on the strategy state.

The final section specializes this construction to the distinguished local
binary observables of both players in the projectively dilated Magic Square
strategy.  A joint two-EPR specialization is not stated here: the current
symmetric game does not relate the two players' variable representations.  The
resulting two-copy obstruction is recorded in
`audits/2026-09-04_magic-square-rigidity-orientation-obstruction.md`.

## References

The target statement is blueprint `thm:ms-rigidity`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`.
The concrete binary Pauli projectors and EPR vector are those of
`references/qpbt-paper/04_preliminaries.tex:1097-1262`.  The cited robust
self-test is Coladangelo--Stark, arXiv:1709.09267v2, Theorem 6.9.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open MIPStarRE.LDT MIPStarRE.Quantum

noncomputable section

/-! ## The one-qubit swap isometry -/





/-! ## Binary Pauli actions on the extracted register -/

/-! ## Local Magic Square specializations -/

end

end MIPStarRE.QPBT.MagicSquareRigidity
