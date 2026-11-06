module

public import QPBT.Algebra.Pauli
public import QPBT.Test.MagicSquareTheorems.Basic
public import QPBT.Test.MagicSquareTheorems.PerfectStrategy
public import QPBT.Test.MagicSquareTheorems.Rigidity.Relations
public import QPBT.Test.MagicSquareTheorems.Rigidity.Dilation
public import QPBT.Test.MagicSquareTheorems.Rigidity.Anticommutation
public import QPBT.Test.MagicSquareTheorems.Rigidity.Transfer
public import QPBT.Test.MagicSquareTheorems.Rigidity.AnticommutatorB
public import QPBT.Test.MagicSquareTheorems.Rigidity.Swap
public import QPBT.Test.MagicSquareTheorems.Rigidity.Consistency
public import QPBT.Test.MagicSquareTheorems.Rigidity.IdealTarget
public import QPBT.Test.MagicSquareTheorems.Rigidity.Constants
public import QPBT.Test.MagicSquareTheorems.Rigidity.TwoQubitSwap
public import QPBT.Test.MagicSquareTheorems.Rigidity.JointState
public import QPBT.Test.MagicSquareTheorems.Rigidity.Marginals

/-!
# Magic Square rigidity

This stable public facade re-exports the elementary symmetry facts, the
value-to-parity relation layer, and the perfect strategy construction while
retaining the rigidity theorem and its supporting definitions.

The rigidity theorem is stated in the corrected form adopted on issue
Dengnifer/MIPStarRE-QPBT-bak#172: the
source quantifies over all strategies, which is false for the role-symmetric
game (`docs/paper-gaps/qpbt_ms-rigidity-symmetric-strategies.tex`), and the
corrected statement assumes that the two players' `Variable_1` and `Variable_5`
measurements agree between the players up to `δ` in the squared
state-dependent distance of `def:povm-distance`
(`msVariableConsistencyDefect`, in `Rigidity/Consistency.lean`).  Symmetric
consistent strategies in the sense of `def:consistent-strategy`, which are
projective, and in particular the SPCC strategies of `def:spcc`, satisfy the
hypothesis with `δ = 0` (`exists_ms_rigidity_of_symmetric_consistent`).

## References

The source statement is blueprint
`thm:ms-rigidity`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`.

The variable indices below are zero-based: indices 0 and 4 represent the
paper's first and fifth variables, respectively.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT MIPStarRE.Quantum MagicSquareRigidity

noncomputable section



/-! ## The coarse witness and the large-error regime -/

/-! ## The bit-measurement and anticommutator estimates on the dilation -/

end

end MIPStarRE.QPBT
