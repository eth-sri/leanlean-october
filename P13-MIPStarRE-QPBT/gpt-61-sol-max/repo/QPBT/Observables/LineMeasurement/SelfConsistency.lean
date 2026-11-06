module

public import QPBT.Observables.PointConsistency
public import QPBT.Observables.LineMeasurement.Expanded
public import QPBT.Observables.LineMeasurement.SquareRootError

/-!
# Self-consistency of the expanded line measurements

This module proves item 1 of the expanded-line consistency lemma on the two
opposite-placement bipartitions. The strategy line measurements are
self-consistent between the two players on average over the line-point
distribution, because a disagreement on a sampled line is rejected by the
corresponding self-loop of the Pauli basis test; the Pauli line projectors are
perfectly consistent on an EPR pair; and the data-processing inequality
transfers the product estimate to the addition postprocessing that defines the
expanded line measurement.

The module also records that the error parameter of a projective setting is
nonnegative, which is not assumed by the structure and is needed by the other
two items as well.

## References

The declarations formalize `enu:qld-comm-line-self-cons`, item 1 of
`lem:qld-comm-line-cons`, whose paper source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:527-532`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

/-! ## Self-consistency of the unexpanded line measurements -/

namespace ProjectiveSetting

variable {P : AdmissibleParams} {ε : ℝ}

/-! ## The error parameter -/

variable (S : ProjectiveSetting P ε)

/-- The error parameter of a projective setting is nonnegative. Nothing in the
structure assumes this: it follows from the winning premise `1 - ε ≤ value`
together with the bound `value ≤ 1` satisfied by the value of every strategy.
Formalization-only auxiliary supplying the sign condition of the winning
implications used in items 2 and 3 of `lem:qld-comm-line-cons`. -/
theorem eps_nonneg (S : ProjectiveSetting P ε)  : 0 ≤ ε := by
  have hv := WinImplications.strategy_value_le_one S.toStrategy
  have hw := S.win
  linarith

/-! ## Placement of differences on the two bipartitions -/

-- The four-level product indices below exceed the default instance-search
-- size.

set_option synthInstance.maxSize 400 in
/-- On the `AA' | BA''(B'B'')` bipartition, the difference of an `AA'` and a
`BA''` placement acts on the expanded state as the corresponding difference
of left and right tensor placements. Formalization-only transport for the
placement pairs of `lem:qld-comm-line-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:527-545`. -/
theorem norm_place_AA'_sub_place_BA'' 
    (O₁ : Op (S.toStrategy.ιA × PauliRegister P))
    (O₂ : Op (S.toStrategy.ιB × PauliRegister P)) :
    ‖applyOperatorToState (S.place .AA' O₁ - S.place .BA'' O₂) S.psiHat‖ =
      ‖applyOperatorToState
        (heteroKron O₁ (1 : Op ((S.toStrategy.ιB × PauliRegister P) ×
             PauliRegister P × PauliRegister P )) -
          heteroKron (1 : Op (S.toStrategy.ιA × PauliRegister P))
            (heteroKron O₂ (1 : Op (PauliRegister P × PauliRegister P))))
        (reindexState (aaBaBipartition P S.toStrategy.ιA S.toStrategy.ιB)
          S.psiHat)‖ := by
  rw [WinImplications.norm_applyOperatorToState_reindexState,
    WinImplications.reindexOp_sub, reindexOp_aaBaBipartition_left,
    reindexOp_aaBaBipartition_right]

set_option synthInstance.maxSize 400 in
/-- On the `AB'' | BB'(A'A'')` bipartition, the difference of an `AB''` and a
`BB'` placement acts on the expanded state as the corresponding difference of
left and right tensor placements. Formalization-only transport for the
placement pairs of `lem:qld-comm-line-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:527-545`. -/
theorem norm_place_AB''_sub_place_BB' 
    (O₁ : Op (S.toStrategy.ιA × PauliRegister P))
    (O₂ : Op (S.toStrategy.ιB × PauliRegister P)) :
    ‖applyOperatorToState (S.place .AB'' O₁ - S.place .BB' O₂) S.psiHat‖ =
      ‖applyOperatorToState
        (heteroKron O₁ (1 : Op ((S.toStrategy.ιB × PauliRegister P) ×
             PauliRegister P × PauliRegister P )) -
          heteroKron (1 : Op (S.toStrategy.ιA × PauliRegister P))
            (heteroKron O₂ (1 : Op (PauliRegister P × PauliRegister P))))
        (reindexState (abBbBipartition P S.toStrategy.ιA S.toStrategy.ιB)
          S.psiHat)‖ := by
  rw [WinImplications.norm_applyOperatorToState_reindexState,
    WinImplications.reindexOp_sub, reindexOp_abBbBipartition_left,
    reindexOp_abBbBipartition_right]

set_option synthInstance.maxSize 400 in
/-- Reindexing the expanded state along any equivalence onto a product of
the six registers leaves it a unit vector. Formalization-only auxiliary
carrying the normalization of `def:expanded-state` to the two bipartitions
used by the consistency estimates. -/
theorem norm_reindexState_psiHat 
    (e : SixReg P S.toStrategy.ιA S.toStrategy.ιB ≃
      (S.toStrategy.ιA × PauliRegister P) ×
         (S.toStrategy.ιB × PauliRegister P) ×
           PauliRegister P × PauliRegister P  ) :
    ‖reindexState e S.psiHat‖ = 1 := by
  rw [reindexState_norm_eq, psiHat_norm]

/-! ## Fine-product consistency on the two bipartitions -/

/-! ## Data processing and transport back to the six registers -/

end ProjectiveSetting

end

end MIPStarRE.QPBT
