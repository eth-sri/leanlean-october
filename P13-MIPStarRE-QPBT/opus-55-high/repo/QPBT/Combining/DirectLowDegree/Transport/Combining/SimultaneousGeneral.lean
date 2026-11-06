module

public import QPBT.Combining.DirectLowDegree.Transport.Combining.RecoveryTransport
public import QPBT.Combining.DirectLowDegree.Transport.Simultaneous

/-!
# Simultaneous polynomial measurements for a general simultaneity parameter

`prop:ld-simultaneous-general-k` produces, from a projective strategy for the
directly indexed low-degree game at parameters `(q, m, d, k)` succeeding with
probability at least `1 - ε`, a pair of polynomial-tuple measurements
satisfying the three consistency relations of `lem:ld-soundness`.

The reduction applies the case `k = 1` once, to the combined strategy of
`def:ld-combined-strategy` at the combined parameters `(q, m + k, d, 1)`: by
`lem:ld-combined-value` that strategy succeeds with probability at least
`1 - 10 ε`, so the case `k = 1` produces measurements with outcomes in the
polynomials of `m + k` variables, satisfying the three relations with the error
of `thm:main-formal` at the combined parameters, and
`lem:ld-combining-recovery` post-processes them by the recovery map of
`def:ld-combining-map`, at the cost of `(m + k) d / q` in the two point
relations.

The displayed error is `Test.mainFormalError` from the direct `k = 1` result
derived from `thm:main-formal` at the combined parameters, plus `(m + k) d / q`.
Its absorption into `deltaLd` at the original parameters, with the universal
constants `a = 10^23` and `b = 1/80000`, is
`exists_directCombinedTransportConstants`, and the absorbed form of the
conclusion is `exists_direct_ld_soundness`.

## Main statements

* `exists_directSimultaneousPolynomialMeasurements_combinedError` —
  `prop:ld-simultaneous-general-k` with the error displayed in the parameters
  of the combined game.

## References

* `references/neexp-paper/05_quantum_preliminaries.tex:1409-1503`
* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `blueprint/src/chapter/ch13_qpbt_test.tex:682-715`
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.LDT.Preliminaries
open MIPStarRE.Quantum
open DistanceCalculus

noncomputable section

end

end MIPStarRE.QPBT
