module

public import QPBT.Observables.WinImplications.FactorTransport
public import QPBT.Observables.WinImplications.TwistedCommutation

/-! # Twisted commutation on Bob's factor -/
@[expose] public section
open scoped BigOperators
namespace MIPStarRE.QPBT.WinImplications
open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

/-- The factor-interchanged phase-signed commutation relation on Bob's factor.
This is the trailing clause of `lem:qld-win-implications-obs`, paper
`14_analysis_of_the_pauli_basis_test.tex:309-354`, blueprint
`ch14_qpbt_observables.tex:761-794`. -/
theorem point_obs_twisted_commutation_interchanged_explicit :
    ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε →
      opDistSq (uniformDistribution (PauliTuple P))
        (fun ω => heteroKron 1
          (S.pointObs .bob .X ω.2.2.1 ω.1 *
            S.pointObs .bob .Z ω.2.2.2 ω.2.1))
        (fun ω => phaseSign (gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) •
          heteroKron 1
            (S.pointObs .bob .Z ω.2.2.2 ω.2.1 *
              S.pointObs .bob .X ω.2.2.1 ω.1))
        S.toStrategy.ψ ≤
          (2 * (1024 * (2 * (Fintype.card PauliEdge : ℝ)) +
              1024 * Real.sqrt (4 * (Fintype.card PauliEdge : ℝ))) +
            (96 * (16 * (Fintype.card PauliEdge : ℝ)) +
              3551040 * (16 * (Fintype.card PauliEdge : ℝ))) + 4) *
            Real.sqrt ε := by
  intro P ε S hε
  rw [← opDistSq_smul_swappedState]
  exact point_obs_twisted_commutation_explicit P ε S.swap hε

end MIPStarRE.QPBT.WinImplications
