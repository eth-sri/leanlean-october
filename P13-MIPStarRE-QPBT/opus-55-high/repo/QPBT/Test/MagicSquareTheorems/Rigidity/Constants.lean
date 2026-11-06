module

public import QPBT.Test.MagicSquareTheorems.Rigidity.Transfer
public import QPBT.Test.MagicSquareTheorems.Rigidity.IdealTarget

/-!
# Coarse estimates and the large-error regime of Magic Square rigidity

The rigidity theorem `thm:ms-rigidity` asserts a bound at the scale
`C * (sqrt ε + sqrt δ)` with a universal constant `C`.  Once `sqrt ε + sqrt δ`
exceeds one, that scale exceeds `C`, and the assertion is carried by the trivial
estimates available for *any* witness: two unit vectors are at distance at most
two, the state-dependent distance between two contractions on a unit vector is
at most two, and a two-outcome family therefore has squared distance at most
eight.

This file collects those estimates together with the elementary isometry used to
build a witness for an arbitrary strategy: the embedding of a local space as the
fiber of the extracted register over one fixed basis vector.  The estimates are
stated for the one-point distribution and the binary alphabet in which the
rigidity conclusions are phrased.

## References

blueprint `thm:ms-rigidity`,
paper `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`.
The distance conventions are blueprint
`def:povm-distance`, paper `06_nonlocal_games_and_mipstar.tex:258-285`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open MIPStarRE.LDT MIPStarRE.Quantum

noncomputable section

/-! ## The fiber embedding of a local space in an extracted register -/




/-! ## Coarse contraction estimates -/

end

end MIPStarRE.QPBT.MagicSquareRigidity
