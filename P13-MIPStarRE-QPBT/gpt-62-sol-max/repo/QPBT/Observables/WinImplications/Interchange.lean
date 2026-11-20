module

public import QPBT.Observables.WinImplications.Consistency
public import QPBT.Test.PauliSymmetry

/-!
# Interchange of the tensor factors in the winning implications

This module collects the statements shared by the operator-distance companions
of the winning implications and by their factor-interchanged forms: transport of
the state-dependent distance along the interchange of the two tensor factors,
the constant-factor passage from consistency to distance, the reversed
verifier edges, and the clause-by-clause symmetry of the Pauli win predicate
on the ordered type pairs that the implications use.

## References

The declarations support the trailing clause of `lem:qld-win-implications` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:616-706`. Their paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:192-267`,
whose closing sentences at lines 227 and 263-264 state both companions.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

/-- In a symmetric Pauli basis test we may exchange the strategy's two players. -/
noncomputable abbrev ProjectiveSetting.swap {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) : ProjectiveSetting P ε where
  toStrategy := (pauliBasisTestSymm P).swapStrategy S.toStrategy
  isProjective := S.isProjective.symm
  win := ((pauliBasisTestSymm P).swapStrategy_value S.toStrategy).symm ▸ S.win

namespace WinImplications

/-! ## Transport of the distance functional along the factor interchange -/

section

variable {X α ιA ιB : Type*} [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (μ : Distribution X) (A : X → Measurement α ιA) (B : X → Measurement α ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB))
include X α ιA ιB μ A B ψ

/-- Consistency bounds the state-dependent distance of two oppositely placed
measurement families. This is the first item of `fact:agreement`, blueprint
`ch12_qpbt_games.tex:260-276`, in the placed form used by the trailing clause
of `lem:qld-win-implications`, blueprint `ch14_qpbt_observables.tex:699-701`,
paper `14_analysis_of_the_pauli_basis_test.tex:263-264`. -/
theorem opFamilyDistSq_placed_le_two_mul_consistencyDefect :
    opFamilyDistSq μ (fun x a => heteroKron ((A x).effect a) 1)
        (fun x a => heteroKron 1 ((B x).effect a)) ψ ≤
      2 * bipartiteDefect μ A
        B ψ :=
  opFamilyDistSq_le_two_mul_consistencyDefect μ
    (fun x => DistanceCalculus.leftPlacedMeasurement (A x))
    (fun x => DistanceCalculus.rightPlacedMeasurement (B x)) ψ

/-- Consistency at level `c` gives operator distance at level `2 * c` for two
oppositely placed measurement families. This is the quantitative form of
`fact:agreement`, blueprint `ch12_qpbt_games.tex:260-276`, used by the trailing
clause of `lem:qld-win-implications`, blueprint
`ch14_qpbt_observables.tex:699-701`, paper
`14_analysis_of_the_pauli_basis_test.tex:263-264`. -/
theorem opFamilyDistSq_placed_le_of_consistencyDefect_le {c : ℝ}
    (h : bipartiteDefect μ A
      B ψ ≤ c) :
    opFamilyDistSq μ (fun x a => heteroKron ((A x).effect a) 1)
      (fun x a => heteroKron 1 ((B x).effect a)) ψ ≤ 2 * c := by
  have hstep := opFamilyDistSq_placed_le_two_mul_consistencyDefect μ A B ψ
  linarith

end

/-! ## Reversed verifier edges

The Pauli type graph is a set of unordered pairs, so every ordered edge used by
the exact implications has its reverse in the graph. The reversed edges carry
the interchanged conclusions of `lem:qld-win-implications`, blueprint
`ch14_qpbt_observables.tex:701-703`. -/

/-- The Pauli/point verifier edge, reversing `pointPauliEdge`. -/
def pauliPointEdge (W : PauliKind) : PauliEdge :=
  ⟨(.pauli W, .point W), by simp [pauliEdges]⟩

/-! ## Symmetry of the win predicate on the subtests used here

`def:pauli-win-predicate` lists every clause together with its mirror image, so
on each ordered type pair occurring in `lem:qld-win-implications` exchanging the
two questions and the two answers leaves the predicate unchanged. Paper
`08_classical_and_quantum_low_degree_tests.tex:1126-1225`, blueprint
`ch13_qpbt_test.tex:410-449`. -/

/-! ## Numeric bookkeeping -/

end WinImplications

end

end MIPStarRE.QPBT
