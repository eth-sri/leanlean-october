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

set_option maxHeartbeats 1600000 in
/-- `prop:ld-simultaneous-general-k`, with `Test.mainFormalError` from the direct
`k = 1` result derived from `thm:main-formal` at the combined parameters, plus
the recovery loss `(m + k) d / q`.

The combined strategy of `def:ld-combined-strategy` succeeds with probability
at least `1 - 10 ε` at the combined parameters, whose simultaneity parameter is
`1`; the direct `k = 1` result derived from `thm:main-formal` produces
measurements with outcomes in the polynomials of `m + k` variables, and
`lem:ld-combining-recovery` post-processes them by the recovery map. -/
theorem exists_directSimultaneousPolynomialMeasurements_combinedError
    (D : DirectLdParams) (S : Strategy (directLdGame D)) (hS : S.IsProjective)
    (ε : Error) (hwin : 1 - ε ≤ S.value) :
    ∃ GA : DirectPolyMeasTuple D S.ιA,
      ∃ GB : DirectPolyMeasTuple D S.ιB,
        bipartiteDefect
            (uniformDistribution (DirectPoint D))
            (fun u => (S.A (directLdPointQuestionOf D u)).postprocess
            (directLdPointValuesOrZero D))
            (fun u => GB.postprocess (evalDirectPolyTupleAt u))
            S.ψ ≤
          Test.mainFormalError D.combined.toLDTParameters
              (directLdAuxParameter D.combined) (3 * (10 * ε)) +
            ((D.combined.m * D.d : ℕ) : ℝ) / D.q ∧
        bipartiteDefect
            (uniformDistribution (DirectPoint D))
            (fun u => GA.postprocess (evalDirectPolyTupleAt u))
            (fun u => (S.B (directLdPointQuestionOf D u)).postprocess
            (directLdPointValuesOrZero D))
            S.ψ ≤
          Test.mainFormalError D.combined.toLDTParameters
              (directLdAuxParameter D.combined) (3 * (10 * ε)) +
            ((D.combined.m * D.d : ℕ) : ℝ) / D.q := by
  obtain ⟨GA, GB, h1, h2, _⟩ :=
    exists_directSimultaneousPolynomialMeasurements_of_k_eq_one D.combined rfl
      (directCombinedStrategy D S) ((by
                                      refine ⟨fun q => ?_, fun q => ?_⟩
                                      · exact MIPStarRE.QPBT.SandwichProduct.postprocess_isProjective _ (hS.1 _) _
                                      · exact MIPStarRE.QPBT.SandwichProduct.postprocess_isProjective _ (hS.2 _) _))
      (10 * ε) ((by
                  have hcomb := directLdRejectionProbability_directCombinedStrategy_le D S
                  rw [directLdRejectionProbability_eq_one_sub_value,
                    directLdRejectionProbability_eq_one_sub_value] at hcomb
                  linarith))
  refine ⟨GA.postprocess (directTupleOfCombinedTuple D),
    GB.postprocess (directTupleOfCombinedTuple D), ?_, ?_⟩
  · exact (directCombinedRecovery_bound D S.A S.ψ S.ψ_norm GB).trans (add_le_add h1 le_rfl)
  · refine (bipartiteDefect_prodComm _ _ _ S.ψ).symm.trans_le <|
      (directCombinedRecovery_bound D S.B _ ((reindexState_norm_eq _ _).trans S.ψ_norm) GA).trans
        (add_le_add ?_ le_rfl)
    exact (bipartiteDefect_prodComm _ _ _ S.ψ).trans_le h2

end

end MIPStarRE.QPBT
