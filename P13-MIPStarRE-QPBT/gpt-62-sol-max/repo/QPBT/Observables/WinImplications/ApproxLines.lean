module

public import QPBT.Observables.WinImplications.Interchange

/-! Player exchange for the line and Pauli readout subtests. -/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

namespace WinImplications

theorem win_low_degree_interchanged_explicit :
    ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε → ∀ W : PauliKind,
      bipartiteDefect (linePointDist P.toLdParams)
        (fun sample => S.pointMeasOption .alice W sample.2)
        (fun sample => S.lineEvalMeas .bob W sample.1 sample.2)
        S.toStrategy.ψ ≤ 86 * ε := by
  intro P ε S hε W
  exact le_of_eq_of_le (DistanceCalculus.consistencyDefect_prodComm (linePointDist P.toLdParams)
    (fun x a => (S.pointMeasOption .alice W x.2).effect a)
    (fun x a => (S.lineEvalMeas .bob W x.1 x.2).effect a) S.toStrategy.ψ).symm
    (win_low_degree_explicit P ε S.swap hε W)

theorem win_pauli_basis_cons_interchanged_explicit :
    ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε → ∀ W : PauliKind,
      bipartiteDefect (uniformDistribution (PauliPoint P))
        (S.pauliEvalMeas .alice W)
        (S.pointMeas .bob W)
        S.toStrategy.ψ ≤ 86 * ε := by
  intro P ε S hε W
  exact le_of_eq_of_le (DistanceCalculus.consistencyDefect_prodComm (uniformDistribution (PauliPoint P))
    (fun u a => (S.pauliEvalMeas .alice W u).effect a)
    (fun u a => (S.pointMeas .bob W u).effect a) S.toStrategy.ψ).symm
    (win_pauli_basis_cons_explicit P ε S.swap hε W)

end WinImplications

end

end MIPStarRE.QPBT
