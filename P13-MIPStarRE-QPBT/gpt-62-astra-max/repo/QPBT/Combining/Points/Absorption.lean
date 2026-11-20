module

public import QPBT.Combining.Points.Closeness
public import QPBT.Combining.Witnesses

/-!
# Absorption estimates for combined point measurements

This module proves the first projection step used to compare a joint point
measurement with the corresponding marginal point measurement.  Projectivity
makes the complementary projection contractive, and the two ordered
consistency fields of `CombinedPointsWitness` supply the resulting averaged
bounds.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:902-915`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

end

end MIPStarRE.QPBT
